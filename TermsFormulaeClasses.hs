{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module TermsFormulaeClasses where

import Utils

import Data.List


type Var = String

fv :: (Functor a, Foldable a) => a Var -> [Var]
fv = foldr union [] . fmap (\v -> [v])

fvMultiset :: (Functor a, Foldable a) => a Var -> [Var]
fvMultiset = foldr (++) [] . fmap (\v -> [v])

renameApart :: Functor a => [Var] -> a Var -> a Var
renameApart forbidden = fmap (freshifyName forbidden)


type Subst a = [(String, a)]

class Functor t => Term t where
  varTerm :: v -> t v
  constTerm :: String -> t v

applySubstInVar :: Term t => Subst (t Var) -> Var -> t Var
applySubstInVar s x = case lookup x s
                      of Just sT -> sT
                         Nothing -> varTerm x

data MarkedVar = MatchableVar Var | UnmatchableVar Var

unmarkVar :: MarkedVar -> Var
unmarkVar (MatchableVar x) = x
unmarkVar (UnmatchableVar x) = x

unmarkSubst :: Term t => Subst (t MarkedVar) -> Subst (t Var)
unmarkSubst = map (\(x, t) -> (x, unmarkVar <$> t))

applySubstInMarkedVar :: Term t => Subst (t MarkedVar) -> MarkedVar -> t MarkedVar
applySubstInMarkedVar s (MatchableVar x) =
  case lookup x s
  of Just sT -> sT
     Nothing -> varTerm (MatchableVar x)
applySubstInMarkedVar s (UnmatchableVar x) = varTerm (UnmatchableVar x)


class (Term t, Functor a) => Substable t a | a -> t where
  joinTerm :: a (t v) -> a v

  applySubstGen :: (Subst (t v) -> v -> t v) -> Subst (t v) -> a v -> a v
  applySubstGen apV s = joinTerm . fmap (apV s)

  applySubst :: Subst (t Var) -> a Var -> a Var
  applySubst = applySubstGen applySubstInVar

  ground :: a Var -> a v
  ground = joinTerm . fmap constTerm


class (Functor a, Substable t a) => Matchable t a | a -> t where
  matchMarkedBounded :: NatInf -> a MarkedVar -> a MarkedVar -> Maybe (Subst (t MarkedVar))

  matchMarked :: a MarkedVar -> a MarkedVar -> Maybe (Subst (t MarkedVar))
  matchMarked = matchMarkedBounded Inf

  matchBounded :: NatInf -> a Var -> a Var -> Maybe (Subst (t Var))
  matchBounded b pattern value = unmarkSubst <$> matchMarkedBounded b (MatchableVar <$> pattern) (UnmatchableVar <$> value)

  match :: a Var -> a Var -> Maybe (Subst (t Var))
  match = matchBounded Inf

  matchMarkedListsBounded :: NatInf -> [a MarkedVar] -> [a MarkedVar] -> Maybe (Subst (t MarkedVar))
  matchMarkedListsBounded b patterns values =
    if length patterns == length values
    then foldl (\ms (p, v) -> ms >>= (\s -> (++ s) <$> matchMarkedBounded b (applySubstGen applySubstInMarkedVar s p) v))
               (Just [])
               (zip patterns values)
    else Nothing

  matchMarkedLists :: [a MarkedVar] -> [a MarkedVar] -> Maybe (Subst (t MarkedVar))
  matchMarkedLists = matchMarkedListsBounded Inf

  matchLists :: [a Var] -> [a Var] -> Maybe (Subst (t Var))
  matchLists patterns values = unmarkSubst <$> matchMarkedLists (fmap MatchableVar <$> patterns)
                                                                (fmap UnmatchableVar <$> values)
