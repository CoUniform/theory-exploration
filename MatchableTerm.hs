{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module MatchableTerm where

import Utils
import TermsFormulaeClasses

import Data.List
import Text.ParserCombinators.Parsec


{- First-order terms -}
data FOTermGen a = FOVar a | Constr String [FOTermGen a] deriving Eq

type FOTerm = FOTermGen Var

instance Show FOTerm where
  showsPrec _ (FOVar x) = (x ++)
  showsPrec _ (Constr c ts) = (c ++) . unwordsShowS (map showsInnerFOTerm ts)

showsInnerFOTerm t@(FOVar _) = shows t
showsInnerFOTerm t@(Constr _ []) = shows t
showsInnerFOTerm t = ('(' :) . shows t . (')' :)

pFOVar :: [String] -> Parser FOTerm
pFOVar fVars = try $ FOVar <$> pVar fVars

pFOConst :: [String] -> Parser FOTerm
pFOConst fVars = try $ flip Constr [] <$> pConst fVars

pFOConstr :: [String] -> Parser FOTerm
pFOConstr fVars = try $ do
  c <- pConst fVars
  ts <- many (pFOTermInner fVars)
  return (Constr c ts)

pFOTerm :: [String] -> Parser FOTerm
pFOTerm fVars = pFOVar fVars <|> pFOConstr fVars <|> pParens (pFOTerm fVars)

pFOTermInner :: [String] -> Parser FOTerm
pFOTermInner fVars = pFOVar fVars <|> pFOConst fVars <|> pParens (pFOTerm fVars)

instance Functor FOTermGen where
  fmap f (FOVar x) = FOVar (f x)
  fmap f (Constr c ts) = Constr c (fmap f <$> ts)

instance Foldable FOTermGen where
  foldMap f (FOVar x) = f x
  foldMap f (Constr c ts) = mconcat (foldMap f <$> ts)

instance Term FOTermGen where
  varTerm = FOVar
  constTerm c = Constr c []

instance Substable FOTermGen FOTermGen where
  joinTerm (FOVar t) = t
  joinTerm (Constr c ts) = Constr c (joinTerm <$> ts)

instance Matchable FOTermGen FOTermGen where
  matchMarkedBounded _ (FOVar (MatchableVar x)) t = Just [(x, t)]
  matchMarkedBounded _ (FOVar (UnmatchableVar x)) (FOVar (UnmatchableVar y)) | x == y = Just []
  matchMarkedBounded _ (Constr c1 ts1) (Constr c2 ts2) | c1 == c2 = matchMarkedLists ts1 ts2
  matchMarkedBounded _ _ _ = Nothing

constsMultisetFOTerm :: FOTerm -> [String]
constsMultisetFOTerm (FOVar _) = []
constsMultisetFOTerm (Constr c ts) = c : foldr (++) [] (constsMultisetFOTerm <$> ts)



{- Lambda terms -}

data LambdaTermGen a =
    FreeVar a
  | Const String
  | BoundVar Int
  | App (LambdaTermGen a) (LambdaTermGen a)
  | Lam (LambdaTermGen a)
  | Fix (LambdaTermGen a)

type LambdaTerm = LambdaTermGen Var

instance Show LambdaTerm where
  showsPrec _ = showsLamTermOn 0

boundVarName :: String
boundVarName = "x"

showsLamTermOn lev (FreeVar x) = (x ++)
showsLamTermOn lev (Const c) = (c ++)
showsLamTermOn lev (BoundVar i) = (boundVarName ++) . shows (lev - i - 1)
showsLamTermOn lev (App t1 t2) = showsLamTermLeftOn lev t1 . prependSpace . showsLamTermRightOn lev t2
showsLamTermOn lev (Lam t) = ("λ " ++) . (boundVarName ++) . shows lev . (". " ++) . showsLamTermOn (lev + 1) t
showsLamTermOn lev (Fix t) = ("fix " ++) . (boundVarName ++) . shows lev . (". " ++) . showsLamTermOn (lev + 1) t

showsLamTermLeftOn  lev t@(Lam _)   = ('(' :) . showsLamTermOn lev t . (')' :)
showsLamTermLeftOn  lev t@(Fix _)   = ('(' :) . showsLamTermOn lev t . (')' :)
showsLamTermLeftOn  lev t           =           showsLamTermOn lev t
showsLamTermRightOn lev t@(App _ _) = ('(' :) . showsLamTermOn lev t . (')' :)
showsLamTermRightOn lev t@(Lam _)   = ('(' :) . showsLamTermOn lev t . (')' :)
showsLamTermRightOn lev t@(Fix _)   = ('(' :) . showsLamTermOn lev t . (')' :)
showsLamTermRightOn lev t           =           showsLamTermOn lev t

incrIndices :: [(String, Int)] -> [(String, Int)]
incrIndices = map (\(x, i) -> (x, i + 1))

pLambdaFreeVar :: [String] -> [(String, Int)] -> Parser LambdaTerm
pLambdaFreeVar fVars _ = try $ FreeVar <$> pVar fVars

pLambdaConst :: [String] -> [(String, Int)] -> Parser LambdaTerm
pLambdaConst fVars bVarIndices = try $ Const <$> pConst (fVars ++ map fst bVarIndices)

pLambdaBoundVar :: [String] -> [(String, Int)] -> Parser LambdaTerm
pLambdaBoundVar _ bVarIndices = try $ do
  b <- pIdentifier
  Just i <- return $ lookup b bVarIndices
  return (BoundVar i)

pLambdaAppSeq :: [String] -> [(String, Int)] -> Parser LambdaTerm
pLambdaAppSeq fVars bVarIndices = try $ do
  ts <- many1 (pLambdaTermInnerInd fVars bVarIndices)
  return (foldl1 App ts)

pLambdaLam :: [String] -> [(String, Int)] -> Parser LambdaTerm
pLambdaLam fVars bVarIndices = try $ do
  (pReservedOp "\\" <|> pReservedOp "λ")
  x <- pIdentifier
  pReservedOp "."
  Lam <$> pLambdaTermInd fVars ((x, 0) : incrIndices bVarIndices)

pLambdaFix :: [String] -> [(String, Int)] -> Parser LambdaTerm
pLambdaFix fVars bVarIndices = try $ do
  pReserved "fix"
  x <- pIdentifier
  pReservedOp "."
  Fix <$> pLambdaTermInd fVars ((x, 0) : incrIndices bVarIndices)

pLambdaTermInd :: [String] -> [(String, Int)] -> Parser LambdaTerm
pLambdaTermInd fVars bVarIndices = (pLambdaAppSeq fVars bVarIndices) <|>
                                   (pLambdaLam fVars bVarIndices) <|>
                                   (pLambdaFix fVars bVarIndices) <|>
                                   pParens (pLambdaTermInd fVars bVarIndices)

pLambdaTerm :: [String] -> Parser LambdaTerm
pLambdaTerm fVars = pLambdaTermInd fVars []

pLambdaTermInnerInd :: [String] -> [(String, Int)] -> Parser LambdaTerm
pLambdaTermInnerInd fVars bVarIndices = (pLambdaBoundVar fVars bVarIndices) <|>
                                        (pLambdaFreeVar fVars bVarIndices) <|>
                                        (pLambdaConst fVars bVarIndices) <|>
                                        pParens (pLambdaTermInd fVars bVarIndices)

pLambdaTermInner :: [String] -> Parser LambdaTerm
pLambdaTermInner fVars = pLambdaTermInnerInd fVars []

instance Functor LambdaTermGen where
  fmap f (FreeVar x) = FreeVar (f x)
  fmap f (Const c) = Const c
  fmap f (BoundVar i) = BoundVar i
  fmap f (App t1 t2) = App (fmap f t1) (fmap f t2)
  fmap f (Lam t) = Lam (fmap f t)
  fmap f (Fix t) = Fix (fmap f t)

instance Foldable LambdaTermGen where
  foldMap f (FreeVar x) = (f x)
  foldMap f (Const c) = mempty
  foldMap f t@(BoundVar _) = mempty
  foldMap f (App t1 t2) = (foldMap f t1) `mappend` (foldMap f t2)
  foldMap f (Lam t) = foldMap f t
  foldMap f (Fix t) = foldMap f t

instance Term LambdaTermGen where
  varTerm = FreeVar
  constTerm = Const

instance Substable LambdaTermGen LambdaTermGen where
  joinTerm (FreeVar t) = t
  joinTerm (Const c) = Const c
  joinTerm (BoundVar i) = BoundVar i
  joinTerm (App t1 t2) = App (joinTerm t1) (joinTerm t2)
  joinTerm (Lam t) = Lam (joinTerm t)
  joinTerm (Fix t) = Fix (joinTerm t)

instance Matchable LambdaTermGen LambdaTermGen where
  matchMarkedBounded = matchMarkedLamTermBounded


data WHNF a = WHNFApp (LambdaTermGen a) [LambdaTermGen a] | WHNFLam (LambdaTermGen a)

succUnboundedBoundVars :: LambdaTermGen a -> LambdaTermGen a
succUnboundedBoundVars = succLvarsFrom 0
  where
    succLvarsFrom n t@(FreeVar _) = t
    succLvarsFrom n t@(Const _) = t
    succLvarsFrom n t@(BoundVar i) | i >= n = BoundVar (i + 1)
                                   | otherwise = BoundVar i
    succLvarsFrom n (App t1 t2) = App (succLvarsFrom n t1) (succLvarsFrom n t2)
    succLvarsFrom n (Lam t) = Lam (succLvarsFrom (n + 1) t)
    succLvarsFrom n (Fix t) = Fix (succLvarsFrom (n + 1) t)

substToBoundVar :: LambdaTermGen a -> LambdaTermGen a -> LambdaTermGen a
substToBoundVar = substToBoundVarInd 0
  where
    substToBoundVarInd n sT t@(FreeVar _) = t
    substToBoundVarInd n sT t@(Const _) = t
    substToBoundVarInd n sT t@(BoundVar i) | i == n = sT
                                           | otherwise = t
    substToBoundVarInd n sT (App t1 t2) = App (substToBoundVarInd n sT t1) (substToBoundVarInd n sT t2)
    substToBoundVarInd n sT (Lam t) = Lam (substToBoundVarInd (n + 1) (succUnboundedBoundVars sT) t)
    substToBoundVarInd n sT (Fix t) = Fix (substToBoundVarInd (n + 1) (succUnboundedBoundVars sT) t)

termToWHNF :: LambdaTermGen a -> WHNF a
termToWHNF (App t1 t2) = case termToWHNF t1
                         of WHNFApp h ts -> WHNFApp h (ts ++ [t2])
                            WHNFLam fT -> termToWHNF $ substToBoundVar t2 fT
termToWHNF (Lam t) = WHNFLam t
termToWHNF t = WHNFApp t []

whnfToTerm :: WHNF a -> LambdaTermGen a
whnfToTerm (WHNFApp h ts) = foldl App h ts
whnfToTerm (WHNFLam t) = Lam t

unfoldFix :: WHNF a -> WHNF a
unfoldFix (WHNFApp (Fix ft) ts) = termToWHNF $ foldl App (substToBoundVar (Fix ft) ft) ts
unfoldFix h = h

noUnboundVars :: LambdaTermGen a -> Bool
noUnboundVars = noUnboundVarsFrom 0
  where
    noUnboundVarsFrom n (FreeVar _) = True
    noUnboundVarsFrom n (Const _) = True
    noUnboundVarsFrom n (BoundVar i) | i >= n = False
                                     | otherwise = True
    noUnboundVarsFrom n (App t1 t2) = noUnboundVarsFrom n t1 && noUnboundVarsFrom n t2
    noUnboundVarsFrom n (Lam t) = noUnboundVarsFrom (n + 1) t
    noUnboundVarsFrom n (Fix t) = noUnboundVarsFrom (n + 1) t

matchMarkedLamTermBounded :: NatInf -> LambdaTermGen MarkedVar -> LambdaTermGen MarkedVar -> Maybe (Subst (LambdaTermGen MarkedVar))
matchMarkedLamTermBounded b pattern term = matchWHNF b (termToWHNF pattern) (termToWHNF term)
  where
    matchWHNF (Nat 0) _ _ = Nothing
    matchWHNF b (WHNFApp (FreeVar (MatchableVar x)) []) h2 = let t = whnfToTerm h2
                                                             in if noUnboundVars t
                                                                then Just [(x, t)]
                                                                else Nothing
    matchWHNF b (WHNFApp (FreeVar (UnmatchableVar x)) ts1) (WHNFApp (FreeVar (UnmatchableVar y)) ts2) =
      if x == y
      then matchMarkedListsBounded b ts1 ts2
      else Nothing
    matchWHNF b (WHNFApp (Const c1) ts1) (WHNFApp (Const c2) ts2) =
      if c1 == c2
      then matchMarkedListsBounded b ts1 ts2
      else Nothing
    matchWHNF b (WHNFApp (BoundVar v1) ts1) (WHNFApp (BoundVar v2) ts2) =
      if v1 == v2
      then matchMarkedListsBounded b ts1 ts2
      else Nothing
    matchWHNF b (WHNFLam p) (WHNFLam t) = matchMarkedLamTermBounded b p t
    matchWHNF b h1@(WHNFApp (Fix ft1) ts1) h2@(WHNFApp (Fix ft2) ts2) =
      case matchMarkedListsBounded b (ft1 : ts1) (ft2 : ts2)
      of Just [] -> Just []
         _       -> matchWHNF (decrNatInf b) (unfoldFix h1) (unfoldFix h2)
    matchWHNF b h1@(WHNFApp (Fix _) _) h2 = matchWHNF (decrNatInf b) (unfoldFix h1) h2
    matchWHNF b h1 h2@(WHNFApp (Fix _) _) = matchWHNF (decrNatInf b) h1 (unfoldFix h2)
    matchWHNF _ _ _ = Nothing

termEmbedding :: FOTermGen a -> LambdaTermGen a
termEmbedding (FOVar v) = FreeVar v
termEmbedding (Constr c ts) = foldl App (Const c) (termEmbedding <$> ts)


------------ Examples ------------

-- vf, cst :: String -> FOTerm
-- con :: String -> [FOTerm] -> FOTerm

-- vf = FOVar
-- cst c = Constr c []
-- con = Constr

-- p1 = con "f" [cst "1", con "g" [vf "x", vf "y"], con "g" [vf "z", vf "x"]]
-- v1 = con "f" [cst "1", con "g" [vf "y", vf "x"], con "g" [cst "3", vf "y"]]

-- p2 = con "f" [cst "1", con "g" [vf "x", vf "y"], con "g" [vf "z", vf "x"]]
-- v2 = con "f" [cst "1", con "g" [cst "2", vf "x"], con "g" [cst "3", vf "y"]]


-- vl, c :: String -> LambdaTerm
-- b :: Int -> LambdaTerm
-- (@@) :: LambdaTerm -> LambdaTerm -> LambdaTerm
-- lam, nu :: LambdaTerm -> LambdaTerm

-- vl = FreeVar
-- b = BoundVar
-- c = Const
-- (@@) = App
-- lam = Lam
-- nu = Fix

-- p3 = c "f" @@ vl "x" @@ vl "x"
-- v3 = c "f" @@ (lam (nu (c "scons" @@ b 1 @@ b 0)) @@ vl "x") @@ (c "scons" @@ vl "x" @@ nu (c "scons" @@ vl "x" @@ b 0))

-- p4 = (lam (b 0)) @@ vl "z"
-- v4 = c "0"

-- p5 = (lam (b 0)) @@ vl "z"
-- v5 = b 0
