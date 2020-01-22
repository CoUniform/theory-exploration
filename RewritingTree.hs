module RewritingTree where

import Utils
import TermsFormulaeClasses
import MatchableTerm
import Formula
import AntiUnify
import Unify

import Data.Maybe
import Data.Functor
import Control.Monad


data LeafType = Fail | Critical

data RewritingTree = Leaf LeafType FOAtom |
                     Node FOAtom ClauseName [RewritingTree]

data RewritingTreeStatus = Proven | Failed | TemplateClosed deriving Eq

rtStatus :: RewritingTree -> RewritingTreeStatus
rtStatus (Leaf Fail _) = Failed
rtStatus (Leaf Critical _) = TemplateClosed
rtStatus (Node _ _ ns) = foldr meetStatus initStatus (rtStatus <$> ns)
  where
    meetStatus Failed _ = Failed
    meetStatus _ Failed = Failed
    meetStatus TemplateClosed _ = TemplateClosed
    meetStatus _ TemplateClosed = TemplateClosed
    meetStatus _ _ = Proven

    initStatus = Proven

rtRoot :: RewritingTree -> FOAtom 
rtRoot (Leaf _ a) = a
rtRoot (Node a _ _) = a

rtLeaves :: RewritingTree -> [FOAtom]
rtLeaves (Leaf _ a) = [a]
rtLeaves (Node _ _ children) = concat (rtLeaves <$> children)


findAndApplyClause :: [(ClauseName, FOHornClause)] -> FOAtom -> Maybe (ClauseName, [FOAtom])
findAndApplyClause [] a = Nothing
findAndApplyClause ((cn, HornClause h body) : cls) a =
  case match h a
  of (Just s) -> Just (cn, applySubst s <$> body)
     Nothing -> findAndApplyClause cls a 

buildRTGen :: Maybe (FOAtom, ClauseName) -> FOProg -> FOAtom -> RewritingTree
buildRTGen rootForCheck prog@(Prog defCls) a =
  case (rootForCheck, findAndApplyClause defCls a)
  of (Just (aRoot, cnRoot), Just (cn, children)) | atomPredicate aRoot == atomPredicate a &&
                                                   cn == cnRoot &&
                                                   not (pattersonCondition a aRoot) -> Leaf Critical a
     (_, Just (cn, children)) -> Node a cn (buildRTGen rootForCheck prog <$> children)
     (_, Nothing) -> Leaf Fail a

findTemplateClosedSubtree :: FOProg -> FOAtom -> Maybe RewritingTree
findTemplateClosedSubtree prog@(Prog defCls) a =
  case findAndApplyClause defCls a
  of Nothing -> Nothing
     Just (cn, children) ->
        let rt = Node a cn (buildRTGen (Just (a, cn)) prog <$> children)
        in case rtStatus rt of TemplateClosed -> Just rt
                               otherwise -> Nothing

buildRT :: FOProg -> FOAtom -> RewritingTree
buildRT = buildRTGen Nothing


buildAbstractRT :: FOProg -> RewritingTree -> RewritingTree
buildAbstractRT prog rtOrig@(Node aRoot _ _) =
      rebuildIntoAbstract prog rtOrig (antiunifyNonemptyList aRoot (rtLeaves rtOrig))
  where
    rebuildIntoAbstract prog (Leaf _ _) a = Leaf Critical a
    rebuildIntoAbstract prog@(Prog defCls) (Node _ cnOrig childrenOrig) a =
      case findAndApplyClause defCls a
      of Nothing -> Leaf Fail a 
         Just (cn, children) | cn == cnOrig -> Node a cn (zipWith (rebuildIntoAbstract prog)
                                                                  childrenOrig
                                                                  children)
         _ -> error "Atom should be a generalisation of the original root atom"
buildAbstractRT _ _ = error "Only for template closed or template irregular trees"

hypFromAbstractRT :: FOProg -> RewritingTree -> FOHornClause
hypFromAbstractRT prog (Leaf _ a) = HornClause a []
hypFromAbstractRT (Prog defCls) rt@(Node aRoot cnRoot _) = HornClause aRoot (nonTripleLeaves rt)
  where
    nonTripleLeaves (Leaf Fail a) = [a]
    nonTripleLeaves (Leaf Critical a) =
      case (pattersonCondition a aRoot, findAndApplyClause defCls a)
      of (False, Just (cn, _)) | cn == cnRoot -> []
         (_, _) -> [a]
    nonTripleLeaves (Node _ _ children) = concat (nonTripleLeaves <$> children)


rtTransition :: FOProg -> RewritingTree -> Maybe RewritingTree
rtTransition prog@(Prog defClauses) rt = buildRT prog <$> (`applySubst` rtRoot rt) <$> findLeafUnifier rt
  where
    findLeafUnifier (Leaf _ a) = firstJust (unify a <$> renameApart (fv a) <$> clauseHead <$> snd <$> defClauses)
    findLeafUnifier (Node _ _ children) = firstJust (findLeafUnifier <$> children)

tryConstructCircularUnifier :: RewritingTree -> Maybe LambdaAtom
tryConstructCircularUnifier (Leaf _ _) = Nothing
tryConstructCircularUnifier rt@(Node aRoot _ _) = let ls = rtLeaves rt
                                                  in (`applySubst` (atomEmbedding aRoot)) <$> unifyListsCirc (ls $> aRoot) ls

isTemplateIrregualarRT :: RewritingTree -> Bool
isTemplateIrregualarRT (Leaf _ _) = False
isTemplateIrregualarRT rt@(Node aRoot _ _) = all (`isCriticalPair` aRoot) (rtLeaves rt)


tryConstructFixpointStream :: RewritingTree -> Maybe LambdaAtom
tryConstructFixpointStream (Leaf _ _) = Nothing
tryConstructFixpointStream rt@(Node (Atom pRoot argsRoot) _ _) = firstJust (tryWithLeaf <$> rtLeaves rt)
  where
    tryWithLeaf (Atom p args) = do
      guard (p == pRoot)
      guard (length args == length argsRoot)
      let n = length args
      guard (n > 1)
      let xs = init argsRoot ++ [last args]
      s <- init <$> substFromVars n xs
      guard (noDup xs)
      let tQs = applySubst s <$> termEmbedding <$> init args
      let xsI = termEmbedding <$> init xs
      return $ Atom p $ (xsI ++) $ (: []) $ foldl App (Fix (composeList (replicate (n - 1) Lam) (sconsCon (BoundVar (n - 2)) (foldl App (BoundVar (n - 1)) tQs)))) xsI

    substFromVars = substFromVarsI 0

    substFromVarsI i n [] = Just []
    substFromVarsI i n (FOVar xi : vars) = ((xi, BoundVar (n - 2 - i)) :) <$> substFromVarsI (i + 1) n vars
    substFromVarsI i n (_ : vars) = Nothing

    sconsCon x s = App (App (Const "scons") x) s

moreGeneralHypUniversal :: FOProg -> FOAtom -> Maybe FOHornClause
moreGeneralHypUniversal prog goal = hypFromAbstractRT prog <$>
                                    buildAbstractRT prog <$>
                                    findTemplateClosedSubtree prog goal

genHypsExistential :: FOProg -> FOAtom -> [LambdaAtom]
genHypsExistential prog goal = go True prog (buildRT prog goal)
  where
    go beforeAbsDom prog rt =
      maybeToList (tryConstructCircularUnifier rt) ++
      maybeToList (tryConstructFixpointStream rt) ++
      (if beforeAbsDom && isTemplateIrregualarRT rt
        then go False prog (buildAbstractRT prog rt)
        else fromMaybe [] (go beforeAbsDom prog <$> rtTransition prog rt))
