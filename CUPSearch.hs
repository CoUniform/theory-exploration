{-# LANGUAGE FlexibleContexts #-}

module CUPSearch where

import Utils
import TermsFormulaeClasses
import MatchableTerm
import Formula
import Unify

import Data.List
import Data.Maybe


resolve :: NatInf ->
           NatInf ->
           [(String, LambdaHornClause)] ->
           [(String, LambdaHornClause)] ->
           LambdaAtom ->
           [ProofTerm]
resolve (Nat 0) _ _ _ _ = []
resolve rBound mBound currStepClauses nextStepClauses goal = concat $ map tryClause currStepClauses
  where
    tryClause (name, HornClause h body) =
      case matchBounded mBound h goal
      of Just s -> ProofApp name <$> mapM (resolve (decrNatInf rBound) mBound nextStepClauses nextStepClauses . applySubst s) body
         Nothing -> []


cupSearch :: NatInf ->
             NatInf ->
             LambdaProg ->
             LambdaHornClause ->
             [ProofTerm]
cupSearch rBound mBound (Prog defCls) goal@(HornClause h premises) =
    let numbered_prems = zipWith (\i pr -> ("premise_" ++ show i, HornClause pr []))
                                 [1..]
                                 (map ground premises)
    in let clsContext = ("coinductive_hyp", goal) : numbered_prems ++ defCls
    in  resolve rBound mBound defCls clsContext (ground h)

limitedCUPsearch :: LambdaProg -> LambdaHornClause -> [ProofTerm]
limitedCUPsearch = cupSearch (Nat 20) (Nat 3)

unlimitedCUPsearch :: LambdaProg -> LambdaHornClause -> [ProofTerm]
unlimitedCUPsearch = cupSearch Inf Inf

checkExistentialGoal :: FOAtom -> LambdaAtom -> Bool
checkExistentialGoal goal fact = isJust $ heteroUnify (renameApart (fv fact) goal) fact

checkExistentialGoalInProg :: FOAtom -> FOProg -> Maybe FOAtom
checkExistentialGoalInProg goal (Prog defCls) = checkDefCls defCls
  where
    checkDefCls [] = Nothing
    checkDefCls ((_, HornClause h []) : defClsR) | checkExistentialGoal goal (atomEmbedding h) = Just h
                                                 | otherwise = checkDefCls defClsR
    checkDefCls (_ : defClsR) = checkDefCls defClsR
