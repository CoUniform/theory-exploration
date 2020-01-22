{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Formula where

import Utils
import TermsFormulaeClasses
import MatchableTerm

import Data.List
import Text.ParserCombinators.Parsec


{- Atoms -}

data Atom term var = Atom String [term var]

type FOAtom = Atom FOTermGen Var

type LambdaAtom = Atom LambdaTermGen Var

instance Show FOAtom where
  showsPrec _ (Atom p args) = (p ++) . unwordsShowS (map showsInnerFOTerm args)

instance Show LambdaAtom where
  showsPrec _ (Atom p args) = (p ++) . unwordsShowS (map (showsLamTermRightOn 0) args)

pAtom :: ([String] -> Parser (term var)) -> [String] -> Parser (Atom term var)
pAtom pTerm fVars = do
  p <- pConst fVars
  args <- many (pTerm fVars)
  return (Atom p args)

pFOAtom :: [String] -> Parser FOAtom
pFOAtom = pAtom pFOTermInner

pLambdaAtom :: [String] -> Parser LambdaAtom
pLambdaAtom = pAtom pLambdaTermInner

instance Functor f => Functor (Atom f) where
  fmap f (Atom p args) = Atom p (fmap f <$> args)

instance Foldable f => Foldable (Atom f) where
  foldMap f (Atom p args) = mconcat (foldMap f <$> args)

instance Substable t f => Substable t (Atom f) where
  joinTerm (Atom p args) = Atom p (joinTerm <$> args)

instance Matchable t f => Matchable t (Atom f) where
  matchMarkedBounded b (Atom p1 args1) (Atom p2 args2) | p1 == p2 = matchMarkedListsBounded b args1 args2
                                                       | otherwise = Nothing

atomPredicate :: Atom t v -> String
atomPredicate (Atom p _) = p

constsMultisetFOAtom :: FOAtom -> [String]
constsMultisetFOAtom (Atom p args) = foldr (++) [] (constsMultisetFOTerm <$> args)

atomEmbedding :: FOAtom -> LambdaAtom
atomEmbedding (Atom p args) = Atom p (termEmbedding <$> args)

pattersonCondition :: FOAtom -> FOAtom -> Bool
pattersonCondition b a =    let fvMa = fvMultiset a
                         in let fvMb = fvMultiset b
                         in let cMa = constsMultisetFOAtom a
                         in let cMb = constsMultisetFOAtom b
                         in submultiset fvMb fvMa &&
                            submultiset cMb cMa &&
                            length (fvMb ++ cMb) < length (fvMa ++ cMa)
  where
    submultiset sub sup = all (\x -> countElem x sub <= countElem x sup) (nub sub)
    countElem x = length . filter (== x)

isCriticalPair :: FOAtom -> FOAtom -> Bool
isCriticalPair b a = atomPredicate a == atomPredicate b && not (pattersonCondition a b)


newtype ExistAtom term var = ExistAtom (Atom term var)

type FOExistAtom = ExistAtom FOTermGen Var

type LambdaExistAtom = ExistAtom LambdaTermGen Var

instance (Show (Atom f Var), Functor f, Foldable f) => Show (ExistAtom f Var) where
  show (ExistAtom a) =
       let allVars = fv a
    in let showsForallPref = case allVars of
                                [] -> id
                                otherwise -> ("∃" ++) . unwordsShowS (map (++) allVars) . (". " ++)
    in (showsForallPref . shows a) ""

pExistPrefix :: Parser [String]
pExistPrefix =
  (try $ do
    (pReservedOp "∃" <|> pReserved "exists")
    fVars <- many1 pIdentifier
    pReservedOp "."
    return fVars
  ) <|> return []

pExistAtom :: ([String] -> Parser (Atom term var)) -> Parser (ExistAtom term var)
pExistAtom pAtom = do
  fVars <- pExistPrefix
  ExistAtom <$> pAtom fVars

pFOExistAtom :: Parser FOExistAtom
pFOExistAtom = pExistAtom pFOAtom

pLambdaExistAtom :: Parser LambdaExistAtom
pLambdaExistAtom = pExistAtom pLambdaAtom



{- Horn clauses and programs -}

data HornClause term var = HornClause (Atom term var) [Atom term var]

type FOHornClause = HornClause FOTermGen Var

type LambdaHornClause = HornClause LambdaTermGen Var

instance (Show (Atom term Var),
          Functor term,
          Foldable term) => Show (HornClause term Var) where
  showsPrec _ hc@(HornClause h body) =
       let allVars = fv hc
    in let showsForallPref = case allVars of
                                [] -> id
                                otherwise -> ("∀" ++) . unwordsShowS (map (++) allVars) . (". " ++)
    in let showsPremisesPref = case body of
                                  [] -> id
                                  (pr : prs) -> shows pr .
                                                composeList (map (\pri -> (" /\\ " ++) . shows pri) prs) .
                                                (" -> " ++)
    in showsForallPref . showsPremisesPref . shows h

clauseHead :: HornClause t v -> Atom t v
clauseHead (HornClause h body) = h

hornClauseEmbedding :: FOHornClause -> LambdaHornClause
hornClauseEmbedding (HornClause h body) = HornClause (atomEmbedding h) (atomEmbedding <$> body)

pUnivPrefix :: Parser [String]
pUnivPrefix =
  (try $ do
    (pReservedOp "∀" <|> pReserved "forall")
    fVars <- many1 pIdentifier
    pReservedOp "."
    return fVars
  ) <|> return []

pImplPrefix :: Parser (Atom term var) -> Parser [Atom term var]
pImplPrefix pAtom =
  (try $ do
    body <- sepBy1 pAtom (pReservedOp "/\\")
    pReservedOp "->"
    return body
  ) <|> return []

pHornClause :: ([String] -> Parser (Atom term var)) -> Parser (HornClause term var)
pHornClause pAtom = do
  fVars <- pUnivPrefix 
  body <- pImplPrefix (pAtom fVars)
  h <- pAtom fVars
  return (HornClause h body)

pFOHornClause :: Parser FOHornClause
pFOHornClause = pHornClause pFOAtom

pLambdaHornClause :: Parser LambdaHornClause
pLambdaHornClause = pHornClause pLambdaAtom

instance Functor f => Functor (HornClause f) where
  fmap f (HornClause h body) = HornClause (fmap f h) (fmap f <$> body)

instance Foldable f => Foldable (HornClause f) where
  foldMap f (HornClause h body) = mconcat (foldMap f h : (foldMap f <$> body))


type ClauseName = String

newtype Prog term var = Prog [(ClauseName, HornClause term var)]

type FOProg = Prog FOTermGen Var

type LambdaProg = Prog LambdaTermGen Var

instance Show (HornClause term var) => Show (Prog term var) where
   showsPrec _ (Prog prog) = unwordsWith ";\n" $ map (\(cn, hcl) -> (cn ++) . (" : " ++) . shows hcl) prog

pNamedHornClause :: Parser (HornClause term var) -> Parser (ClauseName, HornClause term var)
pNamedHornClause pHornClause = do
    name <- pIdentifier
    pReservedOp ":"
    hc <- pHornClause
    return (name, hc)

pProg :: Parser (ClauseName, HornClause term var) -> Parser (Prog term var)
pProg pNamedHornClause = Prog <$> sepBy pNamedHornClause (pReservedOp ";")

pFOProg :: Parser FOProg
pFOProg = pProg (pNamedHornClause pFOHornClause)

pLambdaProg :: Parser LambdaProg
pLambdaProg = pProg (pNamedHornClause pLambdaHornClause)

progEmbedding :: FOProg -> LambdaProg
progEmbedding (Prog cls) = Prog (map (\(n, hcl) -> (n, hornClauseEmbedding hcl)) cls)


data ProofTerm = ProofApp ClauseName [ProofTerm]

instance Show ProofTerm where
  showsPrec _ (ProofApp n pts) = (n ++) . unwordsShowS (map showsProofTermInner pts)

showsProofTermInner pt@(ProofApp _ []) = shows pt
showsProofTermInner pt = ("(" ++) . shows pt . (")" ++)
