module Graphics.PrimitiveTypes.Rectangles.SumRectComparison

import Graphics.PrimitiveTypes.Rectangles.SimpleRects
import Graphics.PrimitiveTypes.Rectangles.Rectangles

%access public export
%default total

--------------------------------------------------------------------------------
--                         Simple helper lemmas                               --
--------------------------------------------------------------------------------


||| If two HorizontalSum Rectangles are equal, then their constituent Rectangles are equal.
equalHorizontalSumRectsHaveEqualParts :
    (HorizontalSum a b = HorizontalSum c d) -> (a=c,b=d)
equalHorizontalSumRectsHaveEqualParts Refl = (Refl, Refl)

||| If two VerticalSum Rectangles are equal, then their constituent Rectangles are equal.
equalVerticalSumRectsHaveEqualParts :
    (VerticalSum a b = VerticalSum c d) -> (a=c,b=d)
equalVerticalSumRectsHaveEqualParts Refl = (Refl, Refl)

||| If two HorizontalSum Rectangles are equal, then the underlying SimpleRectangles 
||| of their constituent Rectangles are equal.
equalHorizontalSumRectsHaveEqualSizedParts :
    (HorizontalSum a b = HorizontalSum c d) -> ((toSimpleRect a) = (toSimpleRect c),(toSimpleRect b)=(toSimpleRect d))
equalHorizontalSumRectsHaveEqualSizedParts Refl = (Refl, Refl)

||| If two HorizontalSum Rectangles are equal, then the underlying SimpleRectangles 
||| of their constituent Rectangles are equal.
equalVerticalSumRectsHaveEqualSizedParts :
    (VerticalSum a b = VerticalSum c d) -> ((toSimpleRect a) = (toSimpleRect c),(toSimpleRect b)=(toSimpleRect d))
equalVerticalSumRectsHaveEqualSizedParts Refl = (Refl, Refl)

--------------------------------------------------------------------------------
--                         Datatype definitions                               --
--------------------------------------------------------------------------------

||| Proofs that two SumRects are "congruent."
||| If two SumRects are EqualSized, then their parts have the same type and we can compare them.
data EqualSizedSumRects: Rectangle a -> Rectangle a -> Type where
    AreEqualSizedHorizontal:
        (lowerRect1: Rectangle (MkRect x y1)) ->
        (upperRect1: Rectangle (MkRect x y2)) ->
        (lowerRect2: Rectangle (MkRect x y1)) ->
        (upperRect2: Rectangle (MkRect x y2)) ->
        EqualSizedSumRects (HorizontalSum lowerRect1 upperRect1) (HorizontalSum lowerRect2 upperRect2)
    AreEqualSizedVertical : 
        (leftRect1: Rectangle (MkRect x1 y)) ->
        (rightRect1: Rectangle (MkRect x2 y)) ->    
        (leftRect2: Rectangle (MkRect x1 y)) ->
        (rightRect2: Rectangle (MkRect x2 y)) ->     
        EqualSizedSumRects (VerticalSum leftRect1 rightRect1) (VerticalSum leftRect2 rightRect2)                   

--------------------------------------------------------------------------------
--                                 Uninhabited/Void                           --
--------------------------------------------------------------------------------

implementation Uninhabited (EqualSizedSumRects (SingleRect a) _) where
    uninhabited x impossible

implementation Uninhabited (EqualSizedSumRects _ (SingleRect a)) where
    uninhabited x impossible    

implementation [cantmixVertHoriz1] Uninhabited (EqualSizedSumRects (VerticalSum _ _) (HorizontalSum _ _) ) where
    uninhabited x impossible    
    
implementation [cantmixVertHoriz2] Uninhabited (EqualSizedSumRects (HorizontalSum _ _) (VerticalSum _ _)) where
    uninhabited x impossible    

||| EqualSizedSumRects is reflexive.
equalSizedSumRectIsReflexive : (EqualSizedSumRects a b) -> (EqualSizedSumRects b a)
equalSizedSumRectIsReflexive (AreEqualSizedHorizontal lowerRect1 upperRect1 lowerRect2 upperRect2) = 
    AreEqualSizedHorizontal lowerRect2 upperRect2 lowerRect1 upperRect1
equalSizedSumRectIsReflexive (AreEqualSizedVertical leftRect1 rightRect1 leftRect2 rightRect2) = 
    AreEqualSizedVertical leftRect2 rightRect2 leftRect1 rightRect1


||| EqualSizedSumRects is transitive.
equalSizedSumRectIsTransitive: (EqualSizedSumRects a b) -> (EqualSizedSumRects b c) -> (EqualSizedSumRects a c)
equalSizedSumRectIsTransitive 
    (AreEqualSizedHorizontal lowerRect1 upperRect1 lowerRect2 upperRect2) 
    (AreEqualSizedHorizontal lowerRect2 upperRect2 lowerRect3 upperRect3) 
        = (AreEqualSizedHorizontal lowerRect1 upperRect1 lowerRect3 upperRect3)
equalSizedSumRectIsTransitive
    (AreEqualSizedVertical leftRect1 rightRect1 leftRect2 rightRect2) 
    (AreEqualSizedVertical leftRect2 rightRect2 leftRect3 rightRect3) 
        = (AreEqualSizedVertical leftRect1 rightRect1 leftRect3 rightRect3)

||| Decision procedure for deciding if two Rectangles are EqualSizedSumRects.
decEqualSizedSumRects: 
    (r1: Rectangle (MkRect (plus x1 x2) (plus y1 y2))) -> 
    (r2: Rectangle (MkRect (plus x1 x2) (plus y1 y2))) -> Dec (EqualSizedSumRects r1 r2)        
decEqualSizedSumRects (SingleRect _) (SingleRect _) = No absurd
decEqualSizedSumRects 
    (SingleRect  (MkRect (plus x1 x2) (plus y1 y2))) 
    (HorizontalSum {x= plus x1 x2} {y1=y1} {y2 =y2} lowerRect upperRect) 
        = ?ag
decEqualSizedSumRects 
    (SingleRect (MkRect (plus x1 x2) (plus y1 y2))) 
    (VerticalSum {x1=x1} {x2= x2} {y= plus y1 y2} leftRect rightRect) 
        = No absurd
decEqualSizedSumRects 
    (HorizontalSum {x= plus x1 x2} {y1=y1} {y2 =y2} lowerRect upperRect) 
    (SingleRect (MkRect (plus x1 x2) (plus y1 y2))) 
        = No absurd
decEqualSizedSumRects 
    (HorizontalSum {x= plus x1 x2} {y1=y1} {y2 =y2} re1 re2) 
    (HorizontalSum {x= plus x1 x2} {y1=y1} {y2 =y2} re3 re4) 
        = ?a
decEqualSizedSumRects 
    (HorizontalSum {x= plus x1 x2} {y1=y1} {y2 =y2} _ _) (VerticalSum {x1=x1} {x2= x2} {y= plus y1 y2} _ _) = 
    No (\eqSized => uninhabited @{cantmixVertHoriz2} eqSized)
decEqualSizedSumRects (VerticalSum leftRect rightRect) r2 = ?decEqualSizedSumRects_rhs_3

-- ||| EqualSizedSumRects have same SimpleRect underlying their LLHS.
-- sameWidthLHSEqualSizedSumRects: 
--     EqualSizedSumRects 
--         (SumRect ll1 lr1 ul1 ur1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) 
--         (SumRect ll2 lr2 ul2 ur2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) -> 
--     ((toSimpleRect ll1) = (toSimpleRect ll2))
-- sameWidthLHSEqualSizedSumRects 
--     (AreEqualSizedSumRects 
--         ll1 _ _ _ ll2 _ _ _ 
--         pfxLow1 pfxHigh1 pfyLeft1 pfyRight1 
--         pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) = Refl

-- ||| EqualSizedSumRects have same SimpleRect underlying their LRHS.
-- sameWidthRHSEqualSizedSumRects: 
--     EqualSizedSumRects 
--         (SumRect ll1 lr1 ul1 ur1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) 
--         (SumRect ll2 lr2 ul2 ur2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) -> 
--     ((toSimpleRect lr1) = (toSimpleRect lr2))
-- sameWidthRHSEqualSizedSumRects 
--     (AreEqualSizedSumRects 
--         _ lr1 _ _ _ lr2 _ _ 
--         pfxLow1 pfxHigh1 pfyLeft1 pfyRight1 
--         pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) = Refl


-- ||| EqualSizedSumRects have same SimpleRect underlying their ULHS.
-- sameWidthULHSEqualSizedSumRects: 
--     EqualSizedSumRects 
--         (SumRect ll1 lr1 ul1 ur1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) 
--         (SumRect ll2 lr2 ul2 ur2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) -> 
--     ((toSimpleRect ul1) = (toSimpleRect ul2))
-- sameWidthULHSEqualSizedSumRects 
--     (AreEqualSizedSumRects _ _ ul1 _ _ _ ul2 _ 
--         pfxLow1 pfxHigh1 pfyLeft1 pfyRight1 
--         pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) = Refl


-- ||| EqualSizedSumRects have same SimpleRect underlying their URHS.
-- sameWidthURHSEqualSizedSumRects: 
--     EqualSizedSumRects 
--         (SumRect ll1 lr1 ul1 ur1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1)
--         (SumRect ll2 lr2 ul2 ur2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) -> 
--     ((toSimpleRect ur1) = (toSimpleRect ur2))
-- sameWidthURHSEqualSizedSumRects 
--     (AreEqualSizedSumRects _ _ _ ur1 _ _ _ ur2
--         pfxLow1 pfxHigh1 pfyLeft1 pfyRight1 
--         pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) = Refl

-- ||| Lemma allowing you to change a pfxLow1 into a pfxLow2, among other things, if the rectangles are equal
-- rewriteSumRectWidthRule : 
--     (pfxLow1: plus (width a1) (width b1) = w) -> 
--     (pfLL: a1 = a2) -> (pfLR: b1 = b2) ->
--     (plus (width a2) (width b2) = w)
-- rewriteSumRectWidthRule pfxLow pfLL pfLR = (rewrite (sym pfLL) in (rewrite (sym pfLR) in pfxLow))

-- ||| Lemma allowing you to change a pfxLeft1 into a pfxLeft2, among other things, if the rectangles are equal
-- rewriteSumRectHeightRule : 
--     (pfxLow1: plus (height a1) (height b1) = h) -> 
--     (pfLL: a1 = a2) -> (pfLR: b1 = b2) ->
--     (plus (height a2) (height b2) = h)
-- rewriteSumRectHeightRule pfxLow pfLL pfLR = (rewrite (sym pfLL) in (rewrite (sym pfLR) in pfxLow))

-- ||| Lemma stating that if each constituent SimpleRectangle of two SumRects are equal, 
-- ||| then the SumRects are equal-sized.
-- equalSimpleRectsGiveEqualSizedSumRects : 
--     (ll1: Rectangle ll1Simp) -> (ll2: Rectangle ll2Simp) ->
--     (pfLL: ll1Simp = ll2Simp) ->
--     (lr1: Rectangle lr1Simp) -> (lr2: Rectangle lr2Simp) ->
--     (pfLR: lr1Simp = lr2Simp) ->
--     (ul1: Rectangle ul1Simp) -> (ul2: Rectangle ul2Simp) ->
--     (pfUL: ul1Simp = ul2Simp) ->
--     (ur1: Rectangle ur1Simp) -> (ur2: Rectangle ur2Simp) ->
--     (pfUR: ur1Simp = ur2Simp) ->
--     {x: Nat} -> {y: Nat} ->
--     (pfxLow1: plus (width ll1Simp) (width lr1Simp) = x) ->
--     (pfxHigh1: plus (width ul1Simp) (width ur1Simp) = x) -> 
--     (pfyLeft1: plus (height ll1Simp) (height ul1Simp) = y) ->
--     (pfyRight1: plus (height lr1Simp) (height ur1Simp) = y) ->        
--     (pfxLow2: plus (width ll2Simp) (width lr2Simp) = x) ->
--     (pfxHigh2: plus (width ul2Simp) (width ur2Simp) = x) -> 
--     (pfyLeft2: plus (height ll2Simp) (height ul2Simp) = y) ->
--     (pfyRight2: plus (height lr2Simp) (height ur2Simp) = y) ->          
--     EqualSizedSumRects 
--         (SumRect ll1 lr1 ul1 ur1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) 
--         (SumRect ll2 lr2 ul2 ur2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2)
-- equalSimpleRectsGiveEqualSizedSumRects 
--      {x} {y} 
--     {ll1Simp=(MkRect xll yll)} {ll2Simp=(MkRect xll yll)} 
--     {lr1Simp=(MkRect xlr ylr)} {lr2Simp=(MkRect xlr ylr)} 
--     {ul1Simp=(MkRect xul yul)} {ul2Simp=(MkRect xul yul)} 
--     {ur1Simp=(MkRect xur yur)} {ur2Simp=(MkRect xur yur)}
--      ll1 ll2 Refl lr1 lr2 Refl ul1 ul2 Refl ur1 ur2 Refl 
--      pfxLow1 pfxHigh1 pfyLeft1 pfyRight1 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2 =
--         (AreEqualSizedSumRects 
--             ll1 lr1 ul1 ur1 
--             ll2 lr2 ul2 ur2
--             --(rewrite pfLL in ll2) (rewrite pfLR in lr2) (rewrite pfUL in ul2) (rewrite pfUR in ur2) 
--             {x=x} {y=y}
--             pfxLow1 pfxHigh1 pfyLeft1 pfyRight1
--             pfxLow2 pfxHigh2 pfyLeft2 pfyRight2)

-- ||| Decision procedure for deciding if two Rectangles are EqualSizedSumRects.
-- decEqualSizedSumRects: (r1: Rectangle a) -> (r2: Rectangle a) -> Dec (EqualSizedSumRects r1 r2)
-- decEqualSizedSumRects (SingleRect a) _ = No absurd
-- decEqualSizedSumRects _ (SingleRect a) = No absurd
-- decEqualSizedSumRects (SumRect ll1 lr1 ul1 ur1 {x} {y} pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) (SumRect ll2 lr2 ul2 ur2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) = 
--     case decEq (toSimpleRect ll1) (toSimpleRect ll2) of
--         Yes pfLL =>
--             case decEq (toSimpleRect lr1) (toSimpleRect lr2) of
--                 Yes pfLR =>
--                     case decEq (toSimpleRect ul1) (toSimpleRect ul2) of
--                         Yes pfUL =>
--                             case decEq (toSimpleRect ur1) (toSimpleRect ur2) of
--                                 Yes pfUR => -- You might not know this, but the diamond antipattern is Actually Good. Or, rather, I think it's impossible to avoid given how I defined a Rectangle and given that each contradiction needs to be handled according to its own type.
--                                     Yes (equalSimpleRectsGiveEqualSizedSumRects 
--                                             ll1 ll2 pfLL
--                                             lr1 lr2 pfLR
--                                             ul1 ul2 pfUL
--                                             ur1 ur2 pfUR
--                                             pfxLow1 pfxHigh1 pfyLeft1 pfyRight1
--                                             pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) 
--                                 No contraUR => No (\eqSized => contraUR (sameWidthURHSEqualSizedSumRects eqSized)) --(upperRightHandSimpleRectMustBeEqualForEqualSizedSumRects contraUR)
--                         No contraUL => No (\eqSized => contraUL (sameWidthULHSEqualSizedSumRects eqSized)) -- (upperLeftHandSimpleRectMustBeEqualForEqualSizedSumRects contraUL)
--                 No contraLR => No (\eqSized => contraLR (sameWidthRHSEqualSizedSumRects eqSized)) -- (lowerRightHandSimpleRectMustBeEqualForEqualSizedSumRects contraLR)
--         No contraLL => No (\eqSized => contraLL (sameWidthLHSEqualSizedSumRects eqSized))--(sameWidthLHSEqualSizedSumRects eqSized)) -- (lowerLeftHandSimpleRectMustBeEqualForEqualSizedSumRects contraLL)

-- ||| Lemma allowing you to pull the proofs of equality out of an EqualSizedSumRect
-- getSameSizeProofsEqSizedSumRect : 
--     {ll1: Rectangle ll1Simp} -> {ll2: Rectangle ll2Simp} ->
--     {lr1: Rectangle lr1Simp} -> {lr2: Rectangle lr2Simp} ->
--     {ul1: Rectangle ul1Simp} -> {ul2: Rectangle ul2Simp} ->
--     {ur1: Rectangle ur1Simp} -> {ur2: Rectangle ur2Simp} ->
--     EqualSizedSumRects 
--         (SumRect ll1 lr1 ul1 ur1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) 
--         (SumRect ll2 lr2 ul2 ur2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) ->
--     ((ll1Simp = ll2Simp),(lr1Simp=lr2Simp),(ul1Simp=ul2Simp),(ur1Simp=ur2Simp))
-- getSameSizeProofsEqSizedSumRect 
--     (AreEqualSizedSumRects ll1 lr1 ul1 ur1 ll2 lr2 ul2 ur2 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) 
--         = (Refl,Refl,Refl,Refl) -- kind of shocked that this worked 
--                                 -- but Idris is smarter than me and I won't question it :)

-- ||| Lemma stating that if two SumRects are equal, they are EqualSizedSumRects
-- equalSumRectsAreEqualSized : 
--     ((SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) 
--         = (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} pfxLow2 pfxHigh2 pfyLeft2 pfyRight2)) -> 
--     EqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2)
-- equalSumRectsAreEqualSized {lowerLHS1} {lowerRHS1} {upperLHS1} {upperRHS1} {lowerLHS2} {lowerRHS2} {upperLHS2} {upperRHS2} {x} {y} {pfxLow1} {pfxHigh1} {pfyLeft1} {pfyRight1} {pfxLow2} {pfxHigh2} {pfyLeft2} {pfyRight2} pf = 
--     ?eqHole1

-- -- ||| Helper function allowing you to switch out an equal SimpleRect from the LHS of a SumRect
-- -- sumRectLHSReplaceRule : 
-- --     {a: SimpleRectangle} -> {b: SimpleRectangle} -> (pf: a = b) ->
-- --     {lhs: Rectangle a} -> SumRect lhs _ _ _