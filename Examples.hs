module Examples where

import Utils
import MatchableTerm
import Formula

import Text.ParserCombinators.Parsec

data ExampleQuerry = SearchQuerry LambdaProg LambdaHornClause
                   | ExplorationQuerry FOProg FOExistAtom

unsafeParse :: Parser a -> String -> a
unsafeParse p s = case parseWholeString p s
                  of Right r -> r
                     Left _ -> error "Unparsable example definition!"


fgInfUnProg :: FOProg
fgInfUnProg = unsafeParse pFOProg "\
\k_fg : ∀ x y. p x y -> p (f y) (g x)\
\"

fgInfUnGoal :: FOExistAtom
fgInfUnGoal = unsafeParse pFOExistAtom "∃ x y. p x y"

fgInfUnExample :: ExampleQuerry
fgInfUnExample = ExplorationQuerry fgInfUnProg fgInfUnGoal


fgInfBinProg :: FOProg
fgInfBinProg = unsafeParse pFOProg "\
\k_fg : ∀ x y. p x y -> p (f x y) (g x y)\
\"

fgInfBinGoal :: FOExistAtom
fgInfBinGoal = unsafeParse pFOExistAtom "∃ x y. p x y"

fgInfBinExample :: ExampleQuerry
fgInfBinExample = ExplorationQuerry fgInfBinProg fgInfBinGoal


zeroStreamProg :: FOProg
zeroStreamProg = unsafeParse pFOProg "\
\k_stream0 : ∀ x. stream x -> stream (scons 0 x)\
\"

zeroStreamGoal :: FOExistAtom
zeroStreamGoal = unsafeParse pFOExistAtom "∃ x. stream x"

zeroStreamExample :: ExampleQuerry
zeroStreamExample = ExplorationQuerry zeroStreamProg zeroStreamGoal


zeroOneStreamProg :: FOProg
zeroOneStreamProg = unsafeParse pFOProg "\
\k_stream01 : ∀ x. streamOneZero x -> streamZeroOne (scons 0 x);\n\
\k_stream10 : ∀ x. streamZeroOne x -> streamOneZero (scons 1 x)\
\"

zeroOneStreamGoal :: FOExistAtom
zeroOneStreamGoal = unsafeParse pFOExistAtom "∃ x. streamZeroOne x"

zeroOneStreamExample :: ExampleQuerry
zeroOneStreamExample = ExplorationQuerry zeroOneStreamProg zeroOneStreamGoal


uProg :: FOProg
uProg = unsafeParse pFOProg "\
\k_u : ∀ x. p (f x) -> p x\
\"

uGoal :: FOExistAtom
uGoal = unsafeParse pFOExistAtom "p a"

uExample :: ExampleQuerry
uExample = ExplorationQuerry uProg uGoal


pqfProg :: FOProg
pqfProg = unsafeParse pFOProg "\
\k_i1 : ∀ x. p (f x) /\\ q x -> p x;\n\
\k_i2 : q a;\n\
\k_i3 : ∀ x. q x -> q (f x)\
\"

pqfGoal :: FOExistAtom
pqfGoal = unsafeParse pFOExistAtom "p a"

pqfExample :: ExampleQuerry
pqfExample = ExplorationQuerry pqfProg pqfGoal


oddEvenProg :: FOProg
oddEvenProg = unsafeParse pFOProg "\
\k_i : eq i;\n\
\k_odd : ∀ x. eq x /\\ eq (even x) -> eq (odd x);\n\
\k_even : ∀ x. eq x /\\ eq (odd x) -> eq (even x)\
\"

oddEvenGoal :: LambdaHornClause
oddEvenGoal = unsafeParse pLambdaHornClause "eq (odd i)"

oddEvenExample :: ExampleQuerry
oddEvenExample = SearchQuerry (progEmbedding oddEvenProg) oddEvenGoal


treeProg :: FOProg
treeProg = unsafeParse pFOProg "\
\k_t : ∀ x y z. t x y /\\ t z z -> t (f x y) z\
\"

treeGoal1 :: LambdaHornClause
treeGoal1 = unsafeParse pLambdaHornClause "∀ x y. t x y -> t (f x y) (f x y)"

treeExample1 :: ExampleQuerry
treeExample1 = SearchQuerry (progEmbedding treeProg) treeGoal1

treeGoal2 :: LambdaHornClause
treeGoal2 = unsafeParse pLambdaHornClause "t (fix x. f x x) (fix x. f x x)"

treeExample2 :: ExampleQuerry
treeExample2 = SearchQuerry (progEmbedding treeProg) treeGoal2


fromProg :: FOProg
fromProg = unsafeParse pFOProg "\
\k_from : ∀ x y. from (s x) y -> from x (scons x y)\
\"

fromGoal1 :: FOExistAtom
fromGoal1 = unsafeParse pFOExistAtom "∃ x y. from x y"

fromExample1 :: ExampleQuerry
fromExample1 = ExplorationQuerry fromProg fromGoal1

fromGoal2 :: FOExistAtom
fromGoal2 = unsafeParse pFOExistAtom "∃ s. from 0 s"

fromExample2 :: ExampleQuerry
fromExample2 = ExplorationQuerry fromProg fromGoal2


fibProg :: FOProg
fibProg = unsafeParse pFOProg "\
\k_fib : ∀ x y z. fib y (plus x y) z -> fib x y (scons x z)\
\"

fibGoal1 :: FOExistAtom
fibGoal1 = unsafeParse pFOExistAtom "∃ x y z. fib x y z"

fibExample1 :: ExampleQuerry
fibExample1 = ExplorationQuerry fibProg fibGoal1

fibGoal2 :: FOExistAtom
fibGoal2 = unsafeParse pFOExistAtom "∃ s. fib 0 1 s"

fibExample2 :: ExampleQuerry
fibExample2 = ExplorationQuerry fibProg fibGoal2


allExamples :: [ExampleQuerry]
allExamples = [
                fgInfUnExample,
                fgInfBinExample,
                zeroStreamExample,
                zeroOneStreamExample,
                uExample,
                pqfExample,
                oddEvenExample,
                treeExample1,
                treeExample2,
                fromExample1,
                fromExample2,
                fibExample1,
                fibExample2
              ]
