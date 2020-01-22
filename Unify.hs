{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Unify where

import Utils
import TermsFormulaeClasses
import MatchableTerm
import Formula

{- First-order unification -}

class Substable t a => Unifiable t a | a -> t where
  -- precondition: arguments do not share free variables
  unify :: a Var -> a Var -> Maybe (Subst (t Var))

  -- precondition: arguments do not share free variables
  unifyLists :: [a Var] -> [a Var] -> Maybe (Subst (t Var))
  unifyLists ts1 ts2 | length ts1 == length ts2 =
    foldl (\ms (t1, t2) -> ms >>= (\s -> (++ s) <$> unify (applySubst s t1) (applySubst s t2)))
          (Just [])
          (zip ts1 ts2)
  unifyLists _ _ = Nothing

instance Unifiable FOTermGen FOTermGen where
  unify (FOVar x) t = Just [(x, t)]
  unify t (FOVar x) = Just [(x, t)]
  unify (Constr c1 ts1) (Constr c2 ts2) | c1 == c2 = unifyLists ts1 ts2
                                        | otherwise = Nothing

instance Unifiable t f => Unifiable t (Atom f) where
  unify (Atom p1 args1) (Atom p2 args2) | p1 == p2 = unifyLists args1 args2
                                        | otherwise = Nothing


{- Restricted heterogeneous unification for existential goal check -}

-- preconditions:
-- ! atoms do not share free variables
-- ! free variables in the left atom are unique
heteroUnify :: FOAtom -> LambdaAtom -> Maybe (Subst LambdaTerm)
heteroUnify (Atom foP foArgs) (Atom lP lArgs) | foP == lP = heteroUnifyTermLists foArgs lArgs
                                              | otherwise = Nothing
  where
    heteroUnifyTermLists foTs lTs | length foTs == length lTs =
      foldl (\ms (foT, lT) -> ms >>= (\s -> (++ s) <$> heteroUnifyTerms foT (applySubst s lT)))
            (Just [])
            (zip foTs lTs)
    heteroUnifyTermLists _ _ = Nothing

    heteroUnifyTerms foT lT = heteroUnifyWHNF foT (termToWHNF lT)

    heteroUnifyWHNF (FOVar _) _ = Just []
    heteroUnifyWHNF foT (WHNFApp (FreeVar x) []) = Just [(x, termEmbedding foT)]
    heteroUnifyWHNF (Constr foC foTs) (WHNFApp (Const lC) lTs) | foC == lC = heteroUnifyTermLists foTs lTs
                                                               | otherwise = Nothing
    heteroUnifyWHNF foT h@(WHNFApp (Fix _) _) = heteroUnifyWHNF foT (unfoldFix h)
    heteroUnifyWHNF _ _ = Nothing


{- Circular unification -}

uniteEquations :: (a -> a -> Maybe [eq]) -> [a] -> [a] -> Maybe [eq]
uniteEquations genEq xs ys | length xs == length ys = concat <$> sequence (zipWith genEq xs ys)
                           | otherwise = Nothing

checkEquationsLinearity :: [(String, FOTerm)] -> Maybe ()
checkEquationsLinearity eqs = if noDup (fst <$> eqs) then Just () else Nothing

solveCircularEquations :: [(String, FOTerm)] -> Subst LambdaTerm
solveCircularEquations = solveCircularEquationsAcc []
  where
    solveCircularEquationsAcc as [] = as
    solveCircularEquationsAcc as ((x, t) : reqs) =
      case applySubst as (termEmbedding t)
      of FreeVar y | y == x -> solveCircularEquationsAcc as reqs
         tu -> let xt = if elem x (fv tu)
                        then Fix (fixBind x tu)
                        else tu
               in solveCircularEquationsAcc (substAddBind x xt as) reqs

    fixBind = fixBindOn 0

    fixBindOn lev x t@(FreeVar y) | x == y = BoundVar lev
                                  | otherwise = t
    fixBindOn lev x t@(Const _) = t
    fixBindOn lev x t@(BoundVar _) = t
    fixBindOn lev x (App t1 t2) = App (fixBindOn lev x t1) (fixBindOn lev x t2)
    fixBindOn lev x (Lam t) = Lam (fixBindOn (lev + 1) x t)
    fixBindOn lev x (Fix t) = Fix (fixBindOn (lev + 1) x t)

    substAddBind x t s = (x, t) : map (\(y, r) -> (y, applySubst [(x, t)] r)) s

class CircUnifiable a where
  getEquations :: a -> a -> Maybe [(String, FOTerm)]

  unifyCirc :: a -> a -> Maybe (Subst LambdaTerm)
  unifyCirc x y = do
    eqs <- getEquations x y
    checkEquationsLinearity eqs
    return $ solveCircularEquations eqs

  unifyListsCirc :: [a] -> [a] -> Maybe (Subst LambdaTerm)
  unifyListsCirc xs ys = do
    eqs <- uniteEquations getEquations xs ys
    checkEquationsLinearity eqs
    return $ solveCircularEquations eqs

instance CircUnifiable FOTerm where
  getEquations (FOVar x) t = Just [(x, t)]
  getEquations t (FOVar x) = Just [(x, t)]
  getEquations (Constr c1 ts1) (Constr c2 ts2) | c1 == c2 = uniteEquations getEquations ts1 ts2
                                               | otherwise = Nothing

instance CircUnifiable FOAtom where
  getEquations (Atom p1 args1) (Atom p2 args2) | p1 == p2 = uniteEquations getEquations args1 args2
                                               | otherwise = Nothing


------------ Examples -----------

-- p x y = Atom "p" [x, y]

-- f x y = Constr "f" [x, y]
-- g x y = Constr "g" [x, y]
-- h x = Constr "h" [x]
-- k x = Constr "k" [x]

-- x = FOVar "x"
-- y = FOVar "y"

-- a1, a2, a3, b1, b2, b3 :: FOAtom

-- a1 = p (h y) (k x)
-- b1 = p x y

-- a2 = p (f x y) (g x y)
-- b2 = p x y

-- a3 = p (f x y) (g x y)
-- b3 = p x x
