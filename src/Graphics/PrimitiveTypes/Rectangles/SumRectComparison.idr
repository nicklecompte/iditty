module Graphics.PrimitiveTypes.Rectangles.SumRectComparison

import Graphics.PrimitiveTypes.Rectangles.SimpleRects
import Graphics.PrimitiveTypes.Rectangles.Rectangles

%access public export
%default total

||| If two SumRects are equal, then their constituent Rectangles are equal.
equalSumRectsHaveEqualParts: ((SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 _ _ _ _) = (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 _ _ _ _)) ->
    ((lowerLHS1=lowerLHS2),(lowerRHS1=lowerRHS2),(upperLHS1=upperLHS2),(upperRHS1=upperRHS2))
equalSumRectsHaveEqualParts {lowerLHS1 = rlLHS} {lowerRHS1 = rlRHS} {upperLHS1 = ruLHS} {upperRHS1 = ruRHS} 
   {lowerLHS2 = rlLHS} {lowerRHS2 = rlRHS} {upperLHS2 = ruLHS} {upperRHS2 = ruRHS} Refl 
       = (Refl,Refl,Refl,Refl)

||| If two SumRects are equal, then their llhs Rectangles are equal.
equalSumRectsHaveEqualLLHS: ((SumRect lowerLHS1 _ _ _ _ _ _ _) = (SumRect lowerLHS2 _ _ _ _ _ _ _)) ->
    (lowerLHS1=lowerLHS2)
equalSumRectsHaveEqualLLHS {lowerLHS1 = r} {lowerLHS2 = r} Refl 
    = Refl


||| If two SumRects are equal, then their lrhs Rectangles are equal.
equalSumRectsHaveEqualLRHS: ((SumRect _ lowerRHS1 _ _) = (SumRect _ lowerRHS2 _ _)) ->
    (lowerRHS1=lowerRHS2)
equalSumRectsHaveEqualLRHS {lowerRHS1 = r} {lowerRHS2 = r} Refl 
    = Refl       

||| If two SumRects are equal, then their ulhs Rectangles are equal.
equalSumRectsHaveEqualULHS: ((SumRect _ _ upperLHS1 _ _ _ _ _) = (SumRect _ _ upperLHS2 _ _ _ _ _)) ->
    (upperLHS1=upperLHS2)
equalSumRectsHaveEqualULHS {upperLHS1 = r} {upperLHS2 = r} Refl 
    = Refl    

||| If two SumRects are equal, then their urhs Rectangles are equal.
equalSumRectsHaveEqualURHS: ((SumRect _ _ _ upperRHS1 _ _ _ _) = (SumRect _ _ _ upperRHS2 _ _ _ _)) ->
    (upperRHS1=upperRHS2)
equalSumRectsHaveEqualURHS {upperRHS1 = r} {upperRHS2 = r} Refl 
    = Refl    

||| If two SumRects have equal constituent Rectangles, then they are equal.
equalPartsGiveEqualSumRects:
    {lowerLHS1: Rectangle ll} -> {lowerLHS2: Rectangle ll} ->
    {lowerRHS1: Rectangle lr} -> {lowerRHS2: Rectangle lr} ->
    {upperLHS1: Rectangle ul} -> {upperLHS2: Rectangle ul} ->
    {upperRHS1: Rectangle ur} -> {upperRHS2: Rectangle ur} ->
    (lowerLHS1=lowerLHS2) ->
    (lowerRHS1=lowerRHS2) ->
    (upperLHS1=upperLHS2) ->
    (upperRHS1=upperRHS2) ->
    {x: Nat} -> {y: Nat} -> 
    (pfxLow: plus (width ll) (width lr) = x) ->
    (pfxHigh: plus (width ul) (width ur) = x) -> 
    (pfyLeft: plus (height ll) (height ul) = y) ->
    (pfyRight: plus (height lr) (height ur) = y) ->        
    ((SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow pfxHigh pfyLeft pfyRight) = (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow pfxHigh pfyLeft pfyRight))
equalPartsGiveEqualSumRects 
    {lowerLHS1 = r1} {lowerLHS2 = r1} {lowerRHS1 = r2} {lowerRHS2 = r2} 
    {upperLHS1=r3} {upperLHS2 = r3} {upperRHS1 = r4} {upperRHS2 = r4}
    Refl Refl Refl Refl _ _ _ _ =
        Refl


||| Proofs that two SumRects are "congruent."
data EqualSizedSumRects: Rectangle a -> Rectangle a -> Type where
    AreEqualSizedSumRects: 
        (lowerLHS1: Rectangle rlLHS) ->
        (lowerRHS1: Rectangle rlRHS) ->
        (upperLHS1: Rectangle ruLHS) ->
        (upperRHS1: Rectangle ruRHS) ->
        (lowerLHS2: Rectangle rlLHS) ->
        (lowerRHS2: Rectangle rlRHS) ->
        (upperLHS2: Rectangle ruLHS) ->
        (upperRHS2: Rectangle ruRHS) ->
        {x: Nat} -> {y: Nat} -> 
        (pfxLow: plus (width rlLHS) (width rlRHS) = x) ->
        (pfxHigh: plus (width ruLHS) (width ruRHS) = x) -> 
        (pfyLeft: plus (height rlLHS) (height ruLHS) = y) ->
        (pfyRight: plus (height rlRHS) (height ruRHS) = y) ->        
        EqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow pfxHigh pfyLeft pfyRight) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow pfxHigh pfyLeft pfyRight)


Uninhabited (EqualSizedSumRects _ (SingleRect _)) where
    uninhabited (AreEqualSizedSumRects _ _ _ _ _ _ _ _ _ _ _ _) impossible

Uninhabited (EqualSizedSumRects (SingleRect _) _) where
    uninhabited (AreEqualSizedSumRects _ _ _ _ _ _ _ _ _ _ _ _) impossible

||| EqualSizedSumRects is a symmetric relation.
equalSizedSumRectIsReflexive: (EqualSizedSumRects a b) -> (EqualSizedSumRects b a)
equalSizedSumRectIsReflexive (AreEqualSizedSumRects lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow pfxHigh pfyLeft pfyRight) = 
    (AreEqualSizedSumRects lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow pfxHigh pfyLeft pfyRight)

||| EqualSizedSumRects is transitive.
equalSizedSumRectIsTransitive: (EqualSizedSumRects a b) -> (EqualSizedSumRects b c) -> (EqualSizedSumRects a c)
equalSizedSumRectIsTransitive (AreEqualSizedSumRects a b c d e f g h pfxLow pfxHigh pfyLeft pfyRight) (AreEqualSizedSumRects e f g h i j k l pfxLow pfxHigh pfyLeft pfyRight) = 
    AreEqualSizedSumRects a b c d i j k l pfxLow pfxHigh pfyLeft pfyRight

||| Given an EqualSizedSumRects, get a pair of the quadrants.
getQuadrant: RectangleQuadrant -> EqualSizedSumRects r1 r2 -> (a:(Nat,Nat)**(Rectangle (MkRect (fst a) (snd a)), Rectangle (MkRect (fst a) (snd a))))
getQuadrant x (AreEqualSizedSumRects lhsL1 rhsL1 lhsU1 rhsU1 e f g h _ _ _ _) =
    case x of
        LHSLow => rectPairToDepPair lhsL1 e
        LHSHigh => rectPairToDepPair lhsU1 g
        RHSLow => rectPairToDepPair rhsL1 f
        RHSHigh => rectPairToDepPair rhsU1 h

||| EqualSizedSumRects have same SimpleRect underlying their LLHS.
sameWidthLHSEqualSizedSumRects: EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1 pfxLow pfxHigh pfyLeft pfyRight) (SumRect ll2 lr2 ul2 ur2 pfxLow pfxHigh pfyLeft pfyRight) -> ((toSimpleRect ll1) = (toSimpleRect ll2))
sameWidthLHSEqualSizedSumRects (AreEqualSizedSumRects ll1 _ _ _ ll2 _ _ _ pfxLow pfxHigh pfyLeft pfyRight) = Refl

||| EqualSizedSumRects have same SimpleRect underlying their LRHS.
sameWidthRHSEqualSizedSumRects: EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1 pfxLow pfxHigh pfyLeft pfyRight) (SumRect ll2 lr2 ul2 ur2 pfxLow pfxHigh pfyLeft pfyRight) -> ((toSimpleRect lr1) = (toSimpleRect lr2))
sameWidthRHSEqualSizedSumRects (AreEqualSizedSumRects _ lr1 _ _ _ lr2 _ _ pfxLow pfxHigh pfyLeft pfyRight) = Refl


||| EqualSizedSumRects have same SimpleRect underlying their ULHS.
sameWidthULHSEqualSizedSumRects: EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1 pfxLow pfxHigh pfyLeft pfyRight) (SumRect ll2 lr2 ul2 ur2 pfxLow pfxHigh pfyLeft pfyRight) -> ((toSimpleRect ul1) = (toSimpleRect ul2))
sameWidthULHSEqualSizedSumRects (AreEqualSizedSumRects _ _ ul1 _ _ _ ul2 _ pfxLow pfxHigh pfyLeft pfyRight) = Refl


||| EqualSizedSumRects have same SimpleRect underlying their URHS.
sameWidthURHSEqualSizedSumRects: EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1 pfxLow pfxHigh pfyLeft pfyRight) (SumRect ll2 lr2 ul2 ur2 pfxLow pfxHigh pfyLeft pfyRight) -> ((toSimpleRect ur1) = (toSimpleRect ur2))
sameWidthURHSEqualSizedSumRects (AreEqualSizedSumRects _ _ _ ur1 _ _ _ ur2 pfxLow pfxHigh pfyLeft pfyRight) = Refl

||| Lemma stating that if each constituent SimpleRectangle of two SumRects are equal, then the SumRects are equal-sized
equalSimpleRectsGiveEqualSizedSumRects : 
    (ll1: Rectangle ll1Simp) -> (ll2: Rectangle ll2Simp) ->
    (pfLL: ll1Simp = ll2Simp) ->
    (lr1: Rectangle lr1Simp) -> (lr2: Rectangle lr2Simp) ->
    (pfLR: lr1Simp = lr2Simp) ->
    (ul1: Rectangle ul1Simp) -> (ul2: Rectangle ul2Simp) ->
    (pfUL: ul1Simp = ul2Simp) ->
    (ur1: Rectangle ur1Simp) -> (ur2: Rectangle ur2Simp) ->
    (pfUR: ur1Simp = ur2Simp) ->
    {x: Nat} -> {y: Nat} ->
    (pfxLow1: plus (width ll1Simp) (width lr1Simp) = x) ->
    (pfxHigh1: plus (width ul1Simp) (width ur1Simp) = x) -> 
    (pfyLeft1: plus (height ll1Simp) (height ul1Simp) = y) ->
    (pfyRight1: plus (height lr1Simp) (height ur1Simp) = y) ->        
    (pfxLow2: plus (width ll2Simp) (width lr2Simp) = x) ->
    (pfxHigh2: plus (width ul2Simp) (width ur2Simp) = x) -> 
    (pfyLeft2: plus (height ll2Simp) (height ul2Simp) = y) ->
    (pfyRigh21: plus (height lr2Simp) (height ur2Simp) = y) ->        
    EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) (SumRect ll2 lr2 ul2 ur2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2)
equalSimpleRectsGiveEqualSizedSumRects {x} {ll1Simp} {ll2Simp} {lr2Simp} ll1 ll2 pfLL lr1 lr2 pfLR ul1 ul2 pfUL ur1 ur2 pfUR pxfLow1 pfxHigh1 pfyLeft1 pfyRight1 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2 =
    ?eqSizedHole2
    -- equalSimpleRectsGiveEqualSizedSumRects {ll1Simp = (MkRect width height)} {ll2Simp = (MkRect width height)} ll1 ll2 Refl {lr1Simp = (MkRect k j)} {lr2Simp = (MkRect k j)} lr1 lr2 Refl {ul1Simp = (MkRect i n)} {ul2Simp = (MkRect i n)} ul1 ul2 Refl {ur1Simp = (MkRect m z)} {ur2Simp = (MkRect m z)} ur1 ur2 Refl {x = x} {y = y} pfxLow pfxHigh pfyLeft pfyRight = 
--     (AreEqualSizedSumRects  ll1 lr1 ul1 ur1 ll2 lr2 ul2 ur2 {x=x} {y=y} pfxLow pfxHigh pfyLeft pfyRight)

-- ||| Decision procedure for deciding if two Rectangles are EqualSizedSumRects.
-- decEqualSizedSumRects: (r1: Rectangle a) -> (r2: Rectangle a) -> Dec (EqualSizedSumRects r1 r2)
-- decEqualSizedSumRects (SingleRect a) _ = No absurd
-- decEqualSizedSumRects _ (SingleRect a) = No absurd
-- decEqualSizedSumRects (SumRect lowerLHS lowerRHS upperLHS upperRHS pfxLow pfxHigh pfyLeft pfyRight) (SingleRect (MkRect x y)) = No absurd
-- decEqualSizedSumRects (SumRect ll1 lr1 ul1 ur1 {x} {y} pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) (SumRect ll2 lr2 ul2 ur2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) = 
--     case decEq (toSimpleRect ll1) (toSimpleRect ll2) of
--         Yes pfLL =>
--             case decEq (toSimpleRect lr1) (toSimpleRect lr2) of
--                 Yes pfLR =>
--                     case decEq (toSimpleRect ul1) (toSimpleRect ul2) of
--                         Yes pfUL =>
--                             case decEq (toSimpleRect ur1) (toSimpleRect ur2) of
--                                 Yes pfUR => -- You might not know this, but the diamond antipattern is Actually Good. Or, rather, I think it's impossible to avoid given how I defined a Rectangle and given that each contradiction needs to be handled according to its own type.
--                                     Yes (equalSimpleRectsGiveEqualSizedSumRects ll1 ll2 pfLL lr1 lr2 pfLR ul1 ul2 pfUL ur1 ur2 pfUR {x=x} {y=y} {pfxLow1} {pfxHigh1} {pfyLeft1} {pfyRight1} {pfxLow2} {pfxHigh2} {pfyLeft2} {pfyRight2})
--                                 No contraUR => No (upperRightHandSimpleRectMustBeEqualForEqualSizedSumRects contraUR)
--                         No contraUL => No (upperLeftHandSimpleRectMustBeEqualForEqualSizedSumRects contraUL)
--                 No contraLR => No (lowerRightHandSimpleRectMustBeEqualForEqualSizedSumRects contraLR)
--         No contraLL => No (lowerLeftHandSimpleRectMustBeEqualForEqualSizedSumRects contraLL)

||| Lemma allowing you to pull the proofs of equality out of an EqualSizedSumRect
getSameSizeProofsEqSizedSumRect : 
    {ll1: Rectangle ll1Simp} -> {ll2: Rectangle ll2Simp} ->
    {lr1: Rectangle lr1Simp} -> {lr2: Rectangle lr2Simp} ->
    {ul1: Rectangle ul1Simp} -> {ul2: Rectangle ul2Simp} ->
    {ur1: Rectangle ur1Simp} -> {ur2: Rectangle ur2Simp} ->
    EqualSizedSumRects 
        (SumRect ll1 lr1 ul1 ur1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) 
        (SumRect ll2 lr2 ul2 ur2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) ->
    ((ll1Simp = ll2Simp),(lr1Simp=lr2Simp),(ul1Simp=ul2Simp),(ur1Simp=ur2Simp))
getSameSizeProofsEqSizedSumRect (AreEqualSizedSumRects ll1 lr1 ul1 ur1 ll2 lr2 ul2 ur2 pfxLow pfxHigh pfyLeft pfyRight) = (Refl,Refl,Refl,Refl) -- kind of shocked that this worked 
                                                                                       -- but Idris is smarter than me and I won't question it :)
||| Lemma stating that if two SumRects are equal, they are EqualSizedSumRects
equalSumRectsAreEqualSized : 
    ((SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) 
        = (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} pfxLow2 pfxHigh2 pfyLeft2 pfyRight2)) -> 
    EqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1)
equalSumRectsAreEqualSized {lowerLHS1} {lowerRHS1} {upperLHS1} {upperRHS1} {lowerLHS2} {lowerRHS2} {upperLHS2} {upperRHS2} {x} {y} {pfxLow1} {pfxHigh1} {pfyLeft1} {pfyRight1} {pfxLow2} {pfxHigh2} {pfyLeft2} {pfyRight2} pf = 
    ?eqHole1
-- let (pfLl,pfLr,pfUl,pfUr) = (equalSumRectsHaveEqualParts pf) in
--     let pfLlhs = (equalRectsHaveEqualSimpleRects pfLl) in
--         let pfLrhs = (equalRectsHaveEqualSimpleRects pfLr) in
--             let pfUlhs = (equalRectsHaveEqualSimpleRects pfUl) in
--                 let pfUrhs = (equalRectsHaveEqualSimpleRects pfUr) in
--                     equalSimpleRectsGiveEqualSizedSumRects lowerLHS1 lowerLHS2 pfLlhs lowerRHS1 lowerRHS2 pfLrhs upperLHS1 upperLHS2 pfUlhs upperRHS1 upperRHS2 pfUrhs {x} {y} {pfxLow1=pfxLow1} {pfxHigh1=pfxHigh1} {pfyLeft1=pfyLeft1} {pfyRight1=pfyRight1} {pfxLow2=pfxLow2} {pfxHigh2=pfxHigh2} {pfyLeft2=pfyLeft2} {pfyRight2=pfyRight2}
