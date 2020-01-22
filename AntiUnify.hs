{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module AntiUnify where

import TermsFormulaeClasses
import MatchableTerm
import Formula

import Control.Monad.State.Lazy
import Data.Maybe
import Data.Tuple
import Data.List (intersect)

type AntiSubst = [(FOTerm, String)]

-- | State of the antiunification process.
-- Contains counter for fresh variables and the two
-- antisubstitutions for the two terms that are antiunified.
data AUState = AUState
  { varcount :: Int
  , lasubst :: AntiSubst
  , rasubst :: AntiSubst
  }

initState :: AUState
initState = (AUState 0 [] [])

-- | Monad for antiunification
type AUResult a = State AUState a

afVarName :: String
afVarName = "a"

-- | Generates a fresh variable
fresh :: AUResult String
fresh = do
  i <- state $ \s -> (varcount s, s {varcount = varcount s + 1})
  return $ afVarName ++ show i

-- | Obtain all the variables that the antisubstitution maps the given term to.
asImage :: FOTerm -> AntiSubst -> [String]
asImage t = mapMaybe (\(s, x) -> if s == t then Just x else Nothing)

-- | Obtain all the variables that the antisubstitution for the first term maps
-- the given term to.
lvars :: FOTerm -> AUResult [String]
lvars t = gets (asImage t . lasubst)

-- | Obtain all the variables that the antisubstitution for the second term maps
-- the given term to.
rvars :: FOTerm -> AUResult [String]
rvars t = gets (asImage t . rasubst)

-- | Extend the antiunifications in the state.
updateASubsts :: String -> FOTerm -> String -> FOTerm -> AUResult ()
updateASubsts x s y t = do
  st <- get
  put $ st { lasubst = (s, x) : lasubst st
           , rasubst = (t, y) : rasubst st
           }

-- | Generates the antiunifier for incomparable terms.
-- If the two given (incomparable) terms are identified through the left and
-- right antisubstitutions, then the identification is kept. Otherwise, we
-- create a fresh variable and abstract away the subterms.
replace :: FOTerm -> FOTerm -> AUResult FOTerm
replace s t = do
  vs <- lvars s
  vt <- rvars t
  let v = intersect vs vt
  case v of
     -- Note: The intersection v should never have more than one variable
    (x : _) -> return $ FOVar x
    _ -> do
      z <- fresh
      updateASubsts z s z t
      return $ FOVar z

-- | The antiunification workhorse. Only tested on first-order terms of base
-- type in normal form, i.e. those given by t ::= x | f(t1, ..., tn).
af :: FOTerm -> FOTerm -> AUResult FOTerm
af s@(Constr f ss) t@(Constr g ts) =
  if f == g
  then Constr f <$> sequence (zipWith af ss ts)
  else replace s t
af s t = replace s t

-- | Computes the antiunifier for the two given terms.
-- Let M and N be terms and write M <= N, if there there is a substitution σ,
-- such that M[σ] = N.
-- For terms s and t, we put A = antiunify s t. Then A is the largest term
-- wrt. the above order, such that A <= s and A <= t. To get the substitutions
-- that witness this, see antiunifySubst.
-- *** Moved to a general class ***
-- antiunify :: FOTerm -> FOTerm -> FOTerm
-- antiunify s t = evalState (af s t) (AUState 0 [] [])

-- | Computes the antiunifier and the witnessing substitutions.
-- For terms s and t, and (A, σ, τ) = antiunifySubst s t, we have that
-- A is the antiunifier of s and t with A[σ] = s and A[τ] = t.
antiunifySubst :: FOTerm -> FOTerm -> (FOTerm, Subst FOTerm, Subst FOTerm)
antiunifySubst s t =
  let (c, st) = runState (af s t) initState
  in (c, map swap $ lasubst st, map swap $ rasubst st)


class Antiunifiable a where
  antiunifyM :: a -> a -> AUResult a

  antiunify :: a -> a -> a
  antiunify x y = evalState (antiunifyM x y) initState

  antiunifyNonemptyList :: a -> [a] -> a
  antiunifyNonemptyList hd tl = evalState (foldM antiunifyM hd tl) initState


instance Antiunifiable FOTerm where
  antiunifyM = af

-- Antiunified atoms should have the same predicate (with the same arity)
instance Antiunifiable (t v) => Antiunifiable (Atom t v) where
  antiunifyM (Atom p ss) (Atom _ ts) = Atom p <$> sequence (zipWith antiunifyM ss ts)



------------ Examples -----------

-- a = Constr "a" []
-- b = Constr "b" []
-- c = Constr "c" []
-- f = Constr "f"
-- g x = Constr "g" [x]
-- h x = Constr "h" [x]
-- k x = Constr "k" [x]

-- tr x y z = Constr "tr" [x, y, z]

-- x = FOVar "x"
-- y = FOVar "y"
-- z = FOVar "z"

-- s1, s2, s3, t1, t2, t3 :: FOTerm

-- s1 = f (g a) a
-- t1 = f (g (k x)) (k x)

-- s2 = f (g x) x
-- t2 = f (g (k x)) (k x)

-- s3 = f (g a) a
-- t3 = f (g (k x)) (k a)

-- s1, t1 :: FOTerm
-- s1 = f [a, a, a]
-- t1 = f [b, c, c]
