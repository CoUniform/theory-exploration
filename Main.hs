module Main where

import Utils
import TermsFormulaeClasses
import MatchableTerm
import Formula
import CUPSearch
import RewritingTree
import Examples

import Data.Maybe
import Text.ParserCombinators.Parsec


runSimpleSearch :: LambdaProg -> LambdaHornClause -> IO ()
runSimpleSearch prog goal = do
  putStr "Proving the goal... "
  case unlimitedCUPsearch prog goal of
    [] -> do
      putStrLn "Fail\n"
      putStrLn "Result: Unable to prove the goal\n"
    (pt : _) -> do
      putStrLn $ "Success (example proof term: " ++ show pt ++ ")\n"
      putStrLn "Result: Provable\n"

runSearchWithExplorationUniversal :: FOProg -> FOAtom -> IO ()
runSearchWithExplorationUniversal prog goal = do
  putStr "Proving the goal... "
  case limitedCUPsearch (progEmbedding prog)
                        (hornClauseEmbedding (HornClause goal [])) of
    (pt : _) -> do
      putStrLn $ "Success (example proof term: " ++ show pt ++ ")\n"
      putStrLn "Result: Provable\n"
    [] -> do
      putStrLn "Fail"
      putStrLn "Start theory exploration (universal)"
      putStr "Generating a more general hypothesis... "
      case moreGeneralHypUniversal prog goal of
        Nothing -> do
          putStrLn "Fail\n"
          putStrLn "Result: Unable to prove the goal\n"
        Just genHyp -> do
          putStrLn "Success"
          putStr "Candidate coinduction hypothesis: " >> print genHyp
          putStr "Proving the candidate hypothesis... "
          case limitedCUPsearch (progEmbedding prog) (hornClauseEmbedding genHyp) of
            [] -> do
              putStrLn "Fail\n"
              putStrLn "Result: Unable to prove the goal\n"
            (ptGenHyp : _) -> do
              putStrLn $ "Success (example proof term: " ++ show ptGenHyp ++ ")"
              putStr "Proving the goal with the additional hypothesis... "
              case unlimitedCUPsearch (progEmbedding (augmentProg ("gen_hyp", genHyp) prog))
                                      (hornClauseEmbedding (HornClause goal [])) of
                [] -> do
                  putStrLn "Fail\n"
                  putStrLn "Result: Unable to prove the goal\n"
                (pt : _) -> do
                  putStrLn $ "Success (example proof term: " ++ show pt ++ ")\n"
                  putStrLn $ "Result: Provable with the additional hypothesis \"" ++ show genHyp ++ "\"\n"
  where
    augmentProg defCl (Prog defCls) = Prog (defCl : defCls) 

runSearchWithExplorationExistential :: FOProg -> FOAtom -> IO ()
runSearchWithExplorationExistential prog goal = do
  putStr "Proving the goal... "
  case checkExistentialGoalInProg goal prog of
    Just at -> do
      putStrLn "Success\n"
      putStrLn $ "Result: Genralized instance \"" ++ show (HornClause at []) ++ "\" is provable\n"
    Nothing -> do
      putStrLn "Fail"
      putStrLn "Start theory exploration (existential)"
      processCandHyps (genHypsExistential prog goal)
    where
      processCandHyps [] = do
        putStrLn "No more candidate hypotheses can be found\n"
        putStrLn "Result: Unable to prove the goal\n"
      processCandHyps (candHyp : candHyps) = do
        putStr "Candidate coinduction hypothesis: " >> print (HornClause candHyp [])
        putStr "Proving the goal by the candidate hypothesis... "
        case checkExistentialGoal goal candHyp of
            False -> do
              putStrLn "Fail"
              processCandHyps candHyps
            True -> do
              putStrLn "Success"
              putStr "Proving the candidate hypothesis... "
              case limitedCUPsearch (progEmbedding prog) (HornClause candHyp []) of
                [] -> do
                  putStrLn "Fail"
                  processCandHyps candHyps
                (ptGenHyp : _) -> do
                  putStrLn $ "Success (example proof term: " ++ show ptGenHyp ++ ")\n"
                  putStrLn $ "Result: Genralized instance \"" ++ show (HornClause candHyp []) ++ "\" is provable\n"

runSearchWithExploration :: FOProg -> FOExistAtom -> IO ()
runSearchWithExploration prog (ExistAtom goal) =
  case fv goal of
    [] -> runSearchWithExplorationUniversal prog goal
    _ -> runSearchWithExplorationExistential prog goal

showInvitation :: IO ()
showInvitation = putStrLn "\n\
\1 - Run simple CUP search\n\
\2 - Run search with theory exploration\n\
\3 - Show restrictions\n\
\4 - Show examples\n\
\5 - Run all examples\n\
\6 - Exit\n\
\"

processSearchQuerry :: IO ()
processSearchQuerry = do
  putStrLn "Enter the correct program (named horn clauses over lambda-terms, see examples and restrictions):"
  iprog <- parseWholeString pLambdaProg <$> getLines
  case iprog of
    Left _ -> putStrLn "Can not parse program"
    Right prog -> do
      putStrLn "Enter the correct goal (horn clause over lambda-terms, see examples and restrictions):"
      igoal <- parseWholeString pLambdaHornClause <$> getLine
      putStr "\n"
      case igoal of
        Left _ -> putStrLn "Can not parse goal"
        Right goal -> runSimpleSearch prog goal


processExplorationQuerry :: IO ()
processExplorationQuerry = do
  putStrLn "Enter the correct program (named horn clauses over FO-terms, see examples and restrictions):"
  iprog <- parseWholeString pFOProg <$> getLines
  case iprog of
    Left _ -> putStrLn "Can not parse program"
    Right prog -> do
      putStrLn "Enter the correct goal (existentially quantified atom over FO-terms, see examples and restrictions):"
      igoal <- parseWholeString pFOExistAtom <$> getLine
      putStr "\n"
      case igoal of
        Left _ -> putStrLn "Can not parse goal"
        Right goal -> runSearchWithExploration prog goal

processRestrictionsQuerry :: IO ()
processRestrictionsQuerry = putStrLn "\
\! All terms should be typable and guarded\n\
\! All quantified variables should have the base type\n\
\! Programs should be universal and non-overlapping\n\
\! Definite clause names should be unique\n\
\! All existentially quantified variables should occur at most once\n\
\\n\
\Simple CUP search works for\n\
\- a set of named horn clauses over lambda terms as a program\n\
\- a horn clause over lambda terms as a goal\n\
\\n\
\Search with theory exploration works for\n\
\- a set of named horn clauses over first-order terms as a program\n\
\- a (possibly) existentially quantified atom over first-order terms as a goal\n\
\\n\
\Both searches may diverge\n\
\If the input does not satisfy these requirements the behaviour is undefined\n\
\\n\
\"

showExample :: Int -> ExampleQuerry -> IO ()
showExample n (SearchQuerry prog goal) = do
  putStr "Example #" >> print n
  putStr "Simple CUP search for the program\n\n"
  print prog
  putStr "\nand the goal  " >> print goal >> putStr "\n"
showExample n (ExplorationQuerry prog goal) = do
  putStr "Example #" >> print n
  putStr "Search with theory exploration for the program\n\n"
  print prog
  putStr "\nand the goal  " >> print goal >> putStr "\n"

processShowExamplesQuerry :: IO ()
processShowExamplesQuerry = sequence_ $ zipWith (\i ex -> showExample i ex >>
                                                          putStr "\n")
                                                [1..]
                                                allExamples

processRunExamplesQuerry :: IO ()
processRunExamplesQuerry = sequence_ $ zipWith (\i ex -> showExample i ex >>
                                                         runExample ex >>
                                                         putStr "\n")
                                               [1..]
                                               allExamples
  where
    runExample (SearchQuerry prog goal) = runSimpleSearch prog goal
    runExample (ExplorationQuerry prog goal) = runSearchWithExploration prog goal


interactiveCycle :: IO ()
interactiveCycle = do
  showInvitation
  i <- parseWholeString pNatural <$> getLine
  putStr "\n"
  case i of Left _ -> putStrLn "Can't parse the input (number expected)" >> interactiveCycle
            Right 1 -> processSearchQuerry >> interactiveCycle
            Right 2 -> processExplorationQuerry >> interactiveCycle
            Right 3 -> processRestrictionsQuerry >> interactiveCycle
            Right 4 -> processShowExamplesQuerry >> interactiveCycle
            Right 5 -> processRunExamplesQuerry >> interactiveCycle
            Right 6 -> return ()
            Right _ -> putStrLn "Number between 1 and 6 expected" >> interactiveCycle

main = interactiveCycle
