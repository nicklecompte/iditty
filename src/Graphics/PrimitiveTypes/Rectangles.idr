module Graphics.PrimitiveTypes.Rectangles

import Data.Vect
import Graphics.PrimitiveTypes.SimpleRects


%access public export
%default total

--------------------------------------------------------------------------------
--                                 Definitions                                --
--------------------------------------------------------------------------------

||| A datatype representing a generic gridded rectangle. It can either be a primitive rectangle or the sum of four rectangles. 0-length/width is allowed. The idea is to create a self-contained analytical geometry with only constructive geometric primitives. For an x,y plane, a Rectangle x y might be written as SumRect of y Rect x 1, which are themselves Rect 1 1. This would correspond to a uniform grid of size x*y.
data Rectangle : SimpleRectangle -> Type where
    ||| A basic Rectangle with width and height. In practice, this may be a "base rectangle." For a drawing, consider this a canvas.
    SingleRect : (a:SimpleRectangle) -> Rectangle a
    ||| A Rectangle can also be the sum of four other Rectangles. The sizes must align - chosen for simplicity so that the rects align in a "cross."
    SumRect:    (lowerLHS: Rectangle rlLHS) ->
                (lowerRHS: Rectangle rlRHS) ->
                (upperLHS: Rectangle ruLHS) ->
                (upperRHS: Rectangle ruRHS) ->
                {x: Nat} -> {y: Nat} ->
                {pfxLow: plus (width rlLHS) (width rlRHS) = x} ->
                {pfxHigh: plus (width ruLHS) (width ruRHS) = x} -> 
                {pfyLeft: plus (height rlLHS) (height ruLHS) = y} ->
                {pfyRight: plus (height rlRHS) (height ruRHS) = y} ->
                Rectangle (MkRect x y)


||| A simple datatype to convey which quadrant a sumrect component is in, without having to reference the constuctor
data RectangleQuadrant = 
    LHSLow |
    LHSHigh |
    RHSLow |
    RHSHigh             
    
    

--------------------------------------------------------------------------------
--                                 Uninhabited/Void                           --
--------------------------------------------------------------------------------

Uninhabited (SingleRect _ = SumRect _ _ _ _) where
    uninhabited Refl impossible
        
Uninhabited (SumRect _ _ _ _ = SingleRect _) where
    uninhabited Refl impossible

--------------------------------------------------------------------------------
--                         Simple helper lemmas                               --
--------------------------------------------------------------------------------

||| Get the width of the underlying SimpleRectangle.
rectangleWidth: (rect: Rectangle a) -> Nat
rectangleWidth {a} rect = width a

||| Two Rectangles with the same underlying SimpleRectangle have the same width.
rectangleWidthsAreEqual: (rect1: Rectangle a) -> (rect2: Rectangle a) -> ((rectangleWidth rect1) = (rectangleWidth rect2))
rectangleWidthsAreEqual rect1 rect2 {a} = Refl

||| Get the height of the underlying SimpleRectangle.
rectangleHeight: (rect: Rectangle a) -> Nat
rectangleHeight {a} rect = height a

||| Two Rectangles with the same underlying SimpleRectangle have the same width.
rectangleHeightsAreEqual: (rect1: Rectangle a) -> (rect2: Rectangle a) -> ((rectangleHeight rect1) = (rectangleHeight rect2))
rectangleHeightsAreEqual rect1 rect2 {a} = Refl

||| Get the underlying SimpleRectangle.
toSimpleRect: Rectangle a -> SimpleRectangle
toSimpleRect _ {a} = a

||| Two equal Rectangles have the same underlying SimpleRectangle.
equalRectsHaveEqualSimpleRects : {r1: Rectangle a} -> {r2: Rectangle b} -> (r1 = r2) -> (a = b)
equalRectsHaveEqualSimpleRects {r1=r1} {r2=r1} Refl = Refl

||| "Shoehorns" a Rectangle (a) into a Maybe (Rectangle b). Just _ if a = b, Nothing o.w.
rectangleShoehorner: Rectangle a -> (b: SimpleRectangle) -> Maybe (Rectangle b)
rectangleShoehorner rect b {a} = case decEq a b of
                                    Yes prfSameSimpleRectangle => Just (replace prfSameSimpleRectangle rect)
                                    No _ => Nothing

||| Replace a SimpleRectangle r with a MkRect (width r) (height r)
replaceSimpleRect: (rect: Rectangle r) -> Rectangle (MkRect (width r) (height r))
replaceSimpleRect rect {r} = replace (simpleRectRewriteLemma r) rect

||| Replace a SimpleRectangle r with a SimpleRectangle s if r = s
replaceSimpleRectGeneral: (rect: Rectangle r) -> {s: SimpleRectangle} -> (r = s) -> Rectangle s
replaceSimpleRectGeneral rect pf = replace pf rect

||| Replacing a SimpleRectangle preserves equality.
replaceSimpleRectEquality: {rect: Rectangle r} -> {s: SimpleRectangle} -> {pf: (r = s)} -> (rect = (replaceSimpleRectGeneral rect {s} pf))
replaceSimpleRectEquality {rect = rect} {r = (MkRect width height)} {s = (MkRect width height)} {pf = Refl} = Refl


||| Helper function for pulling a tuple of (length, height) out as a dependent pair
rectToDepPair : (rect:Rectangle r) -> (a:(Nat,Nat)**(Rectangle (MkRect (fst a) (snd a))))
rectToDepPair rect = let a = (rectangleWidth rect, rectangleHeight rect) in
                        (a ** (replaceSimpleRect rect))


||| Simple helper method mapping a quadrant to Nothing for a SingleRect and to the appropriate component for a SumRect
quadrantToRect: RectangleQuadrant -> (Rectangle r) -> Maybe (a:(Nat,Nat)**(Rectangle (MkRect (fst a) (snd a))))
quadrantToRect _ (SingleRect _) = Nothing
quadrantToRect x (SumRect lhsLow rhsLow lhsHigh rhsHigh) = case x of
                                                            LHSLow => Just (rectToDepPair lhsLow)
                                                            LHSHigh => Just (rectToDepPair lhsHigh)
                                                            RHSLow => Just (rectToDepPair rhsLow)
                                                            RHSHigh => Just (rectToDepPair rhsHigh)    

||| Helper function for pulling a tuple of (length, height) out as a dependent pair from a pair of equal-sized Rectangles.
rectPairToDepPair : (rect1:Rectangle r) -> (rect2: Rectangle r) -> 
        (a:(Nat,Nat)**((Rectangle (MkRect (fst a) (snd a))),(Rectangle (MkRect (fst a) (snd a)))))
rectPairToDepPair rect1 rect2 = let a = (rectangleWidth rect1, rectangleHeight rect1) in
                                    (a ** ((replaceSimpleRect rect1),(replaceSimpleRect rect2)))


--------------------------------------------------------------------------------
--                             SumRect Comparison                             --
--------------------------------------------------------------------------------

||| If two SumRects are equal, then their constituent Rectangles are equal.
equalSumRectsHaveEqualParts: ((SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1) = (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2)) ->
                             ((lowerLHS1=lowerLHS2),(lowerRHS1=lowerRHS2),(upperLHS1=upperLHS2),(upperRHS1=upperRHS2))

equalSumRectsHaveEqualParts {lowerLHS1 = rlLHS} {lowerRHS1 = rlRHS} {upperLHS1 = ruLHS} {upperRHS1 = ruRHS} 
                            {lowerLHS2 = rlLHS} {lowerRHS2 = rlRHS} {upperLHS2 = ruLHS} {upperRHS2 = ruRHS} Refl 
                                = (Refl,Refl,Refl,Refl)

||| If two SumRects are equal, then their llhs Rectangles are equal.
equalSumRectsHaveEqualLLHS: ((SumRect lowerLHS1 _ _ _) = (SumRect lowerLHS2 _ _ _)) ->
    (lowerLHS1=lowerLHS2)
equalSumRectsHaveEqualLLHS {lowerLHS1 = r} {lowerLHS2 = r} Refl 
       = Refl

||| Proofs of equality of LLHS constituent Rectangles can be plumbed through to equal SumRects.
replaceLlhsSumrect : 
    {lowerLHS1 : Rectangle a} -> {lowerLHS2 : Rectangle b} ->
    {pfSimpleRect : a = b} ->
    ((SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1) = (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2)) ->
    ((SumRect (replace pfSimpleRect lowerLHS1) lowerRHS1 upperLHS1 upperRHS1) = (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2))

||| If two SumRects are equal, then their lrhs Rectangles are equal.
equalSumRectsHaveEqualLRHS: ((SumRect _ lowerRHS1 _ _) = (SumRect _ lowerRHS2 _ _)) ->
    (lowerRHS1=lowerRHS2)
equalSumRectsHaveEqualLRHS {lowerRHS1 = r} {lowerRHS2 = r} Refl 
       = Refl       

||| If two SumRects are equal, then their ulhs Rectangles are equal.
equalSumRectsHaveEqualULHS: ((SumRect _ _ upperLHS1 _) = (SumRect _ _ upperLHS2 _)) ->
    (upperLHS1=upperLHS2)
equalSumRectsHaveEqualULHS {upperLHS1 = r} {upperLHS2 = r} Refl 
       = Refl    

||| If two SumRects are equal, then their urhs Rectangles are equal.
equalSumRectsHaveEqualURHS: ((SumRect _ _ _ upperRHS1) = (SumRect _ _ _ upperRHS2)) ->
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
    {pfxLow: plus (width ll) (width lr) = x} ->
    {pfxHigh: plus (width ul) (width ur) = x} -> 
    {pfyLeft: plus (height ll) (height ul) = y} ->
    {pfyRight: plus (height lr) (height ur) = y} ->        
    ((SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {pfxLow = pfxLow1} {pfxHigh = pfxHigh1} {pfyLeft = pfyLeft1} {pfyRight = pfyRight1}) = (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {pfxLow = pfxLow1} {pfxHigh = pfxHigh1} {pfyLeft = pfyLeft1} {pfyRight = pfyRight1}))
equalPartsGiveEqualSumRects 
    {lowerLHS1 = r1} {lowerLHS2 = r1} {lowerRHS1 = r2} {lowerRHS2 = r2} 
    {upperLHS1=r3} {upperLHS2 = r3} {upperRHS1 = r4} {upperRHS2 = r4}
    Refl Refl Refl Refl =
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
        {pfxLow1: plus (width rlLHS) (width rlRHS) = x} ->
        {pfxHigh1: plus (width ruLHS) (width ruRHS) = x} -> 
        {pfyLeft1: plus (height rlLHS) (height ruLHS) = y} ->
        {pfyRight1: plus (height rlRHS) (height ruRHS) = y} ->        
        {pfxLow2: plus (width rlLHS) (width rlRHS) = x} -> -- TODO: we really shouldn't need these.
        {pfxHigh2: plus (width ruLHS) (width ruRHS) = x} -> 
        {pfyLeft2: plus (height rlLHS) (height ruLHS) = y} ->
        {pfyRight2: plus (height rlRHS) (height ruRHS) = y} ->        
        EqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {pfxLow = pfxLow1} {pfxHigh = pfxHigh1} {pfyLeft = pfyLeft1} {pfyRight = pfyRight1}) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {pfxLow = pfxLow2} {pfxHigh = pfxHigh2} {pfyLeft = pfyLeft2} {pfyRight = pfyRight2})



Uninhabited (EqualSizedSumRects _ (SingleRect _)) where
    uninhabited (AreEqualSizedSumRects _ _ _ _ _ _ _ _) impossible

Uninhabited (EqualSizedSumRects (SingleRect _) _) where
    uninhabited (AreEqualSizedSumRects _ _ _ _ _ _ _ _) impossible

||| EqualSizedSumRects is a symmetric relation.
equalSizedSumRectIsReflexive: (EqualSizedSumRects a b) -> (EqualSizedSumRects b a)
equalSizedSumRectIsReflexive (AreEqualSizedSumRects lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 lowerLHS2 lowerRHS2 upperLHS2 upperRHS2) = 
        (AreEqualSizedSumRects lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 )

||| EqualSizedSumRects is transitive.
equalSizedSumRectIsTransitive: (EqualSizedSumRects a b) -> (EqualSizedSumRects b c) -> (EqualSizedSumRects a c)
equalSizedSumRectIsTransitive (AreEqualSizedSumRects a b c d e f g h) (AreEqualSizedSumRects e f g h i j k l) = 
    AreEqualSizedSumRects a b c d i j k l

||| Given an EqualSizedSumRects, get a pair of the quadrants.
getQuadrant: RectangleQuadrant -> EqualSizedSumRects r1 r2 -> (a:(Nat,Nat)**(Rectangle (MkRect (fst a) (snd a)), Rectangle (MkRect (fst a) (snd a))))
getQuadrant x (AreEqualSizedSumRects lhsL1 rhsL1 lhsU1 rhsU1 e f g h) =
    case x of
        LHSLow => rectPairToDepPair lhsL1 e
        LHSHigh => rectPairToDepPair lhsU1 g
        RHSLow => rectPairToDepPair rhsL1 f
        RHSHigh => rectPairToDepPair rhsU1 h

||| EqualSizedSumRects have same SimpleRect underlying their LLHS.
sameWidthLHSEqualSizedSumRects: EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1) (SumRect ll2 lr2 ul2 ur2) -> ((toSimpleRect ll1) = (toSimpleRect ll2))
sameWidthLHSEqualSizedSumRects (AreEqualSizedSumRects ll1 _ _ _ ll2 _ _ _) = Refl

||| Lemma stating that if the LHS of two SumRects don't have equal width, then they cannot be SameSizedSumRects.
lowerLeftHandSimpleRectMustBeEqualForEqualSizedSumRects : (contraLL : (toSimpleRect ll1 = toSimpleRect ll2) -> Void) -> EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1) (SumRect ll2 lr2 ul2 ur2) -> Void
lowerLeftHandSimpleRectMustBeEqualForEqualSizedSumRects contraLL = 
        (\essr => (contraLL (sameWidthLHSEqualSizedSumRects essr)))

||| EqualSizedSumRects have same SimpleRect underlying their LRHS.
sameWidthRHSEqualSizedSumRects: EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1) (SumRect ll2 lr2 ul2 ur2) -> ((toSimpleRect lr1) = (toSimpleRect lr2))
sameWidthRHSEqualSizedSumRects (AreEqualSizedSumRects _ lr1 _ _ _ lr2 _ _) = Refl

||| Lemma stating that if the ULHS of two SumRects don't have equal width, then they cannot be SameSizedSumRects.
lowerRightHandSimpleRectMustBeEqualForEqualSizedSumRects : (contraLR : (toSimpleRect lr1 = toSimpleRect lr2) -> Void) -> EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1) (SumRect ll2 lr2 ul2 ur2) -> Void
lowerRightHandSimpleRectMustBeEqualForEqualSizedSumRects contraLR = 
    (\essr => (contraLR (sameWidthRHSEqualSizedSumRects essr)))

||| EqualSizedSumRects have same SimpleRect underlying their ULHS.
sameWidthULHSEqualSizedSumRects: EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1) (SumRect ll2 lr2 ul2 ur2) -> ((toSimpleRect ul1) = (toSimpleRect ul2))
sameWidthULHSEqualSizedSumRects (AreEqualSizedSumRects _ _ ul1 _ _ _ ul2 _) = Refl

||| Lemma stating that if the ULHS of two SumRects don't have equal width, then they cannot be SameSizedSumRects.
upperLeftHandSimpleRectMustBeEqualForEqualSizedSumRects : (contraUL : (toSimpleRect ul1 = toSimpleRect ul2) -> Void) -> EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1) (SumRect ll2 lr2 ul2 ur2) -> Void
upperLeftHandSimpleRectMustBeEqualForEqualSizedSumRects contraUL = 
        (\essr => (contraUL (sameWidthULHSEqualSizedSumRects essr)))

||| EqualSizedSumRects have same SimpleRect underlying their URHS.
sameWidthURHSEqualSizedSumRects: EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1) (SumRect ll2 lr2 ul2 ur2) -> ((toSimpleRect ur1) = (toSimpleRect ur2))
sameWidthURHSEqualSizedSumRects (AreEqualSizedSumRects _ _ _ ur1 _ _ _ ur2) = Refl

||| Lemma stating that if the LHS of two SumRects don't have equal width, then they cannot be SameSizedSumRects.
upperRightHandSimpleRectMustBeEqualForEqualSizedSumRects : (contraUR : (toSimpleRect ur1 = toSimpleRect ur2) -> Void) -> EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1) (SumRect ll2 lr2 ul2 ur2) -> Void
upperRightHandSimpleRectMustBeEqualForEqualSizedSumRects contraUR = 
    (\essr => (contraUR (sameWidthURHSEqualSizedSumRects essr)))
     
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
    {pfxLow1: plus (width ll1Simp) (width lr1Simp) = x} ->
    {pfxHigh1: plus (width ul1Simp) (width ur1Simp) = x} -> 
    {pfyLeft1: plus (height ll1Simp) (height ul1Simp) = y} ->
    {pfyRight1: plus (height lr1Simp) (height ur1Simp) = y} ->        
    {pfxLow2: plus (width ll2Simp) (width lr2Simp) = x} ->
    {pfxHigh2: plus (width ul2Simp) (width ur2Simp) = x} -> 
    {pfyLeft2: plus (height ll2Simp) (height ul2Simp) = y} ->
    {pfyRight2: plus (height lr2Simp) (height ur2Simp) = y} ->  
    EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1 {pfxLow = pfxLow1} {pfxHigh = pfxHigh1} {pfyLeft = pfyLeft1} {pfyRight = pfyRight1}) (SumRect ll2 lr2 ul2 ur2 {pfxLow = pfxLow2} {pfxHigh = pfxHigh2} {pfyLeft = pfyLeft2} {pfyRight = pfyRight2}) -- {pfxLow = pfxLow2} {pfxHigh = pfxHigh2} {pfyLeft = pfyLeft2} {pfyRight = pfyRight2}
equalSimpleRectsGiveEqualSizedSumRects {ll1Simp = (MkRect width height)} {ll2Simp = (MkRect width height)} ll1 ll2 Refl {lr1Simp = (MkRect k j)} {lr2Simp = (MkRect k j)} lr1 lr2 Refl {ul1Simp = (MkRect i n)} {ul2Simp = (MkRect i n)} ul1 ul2 Refl {ur1Simp = (MkRect m z)} {ur2Simp = (MkRect m z)} ur1 ur2 Refl {x = x} {y = y} {pfxLow1} {pfxHigh1} {pfyLeft1} {pfyRight1} {pfxLow2} {pfxHigh2} {pfyLeft2} {pfyRight2} = 
    (AreEqualSizedSumRects  ll1 lr1 ul1 ur1 ll2 lr2 ul2 ur2 {x=x} {y=y}
                            {pfxLow1 = pfxLow1} 
                            {pfxHigh1 = pfxHigh1} 
                            {pfyLeft1 = pfyLeft1} 
                            {pfyRight1 = pfyRight1}    
                            {pfxLow2 = pfxLow2} 
                            {pfxHigh2 = pfxHigh2} 
                            {pfyLeft2 = pfyLeft2} 
                            {pfyRight2 = pfyRight2}) -- {pfxLow = (the (plus width k = x) pfxLow)} {pfxHigh = (the (plus i m = x) pfxHigh)} {pfyLeft = (the (plus height j = y) pfyLeft)} {pfyRight = (the (plus j z = y) pfyRight)}
-- -- -- {x = x} {y = y} 

--     EqualSizedSumRects (SumRect ll1 lr1 ul1 ur1 {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) (SumRect ll2 lr2 ul2 ur2 {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2})
    

||| Decision procedure for deciding if two Rectangles are EqualSizedSumRects.
decEqualSizedSumRects: (r1: Rectangle a) -> (r2: Rectangle a) -> Dec (EqualSizedSumRects r1 r2)
decEqualSizedSumRects (SingleRect a) _ = No absurd
decEqualSizedSumRects _ (SingleRect a) = No absurd
decEqualSizedSumRects (SumRect lowerLHS lowerRHS upperLHS upperRHS) (SingleRect (MkRect x y)) = No absurd
decEqualSizedSumRects (SumRect ll1 lr1 ul1 ur1 {x} {y} {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) (SumRect ll2 lr2 ul2 ur2 {x} {y} {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2}) = 
    case decEq (toSimpleRect ll1) (toSimpleRect ll2) of
        Yes pfLL =>
            case decEq (toSimpleRect lr1) (toSimpleRect lr2) of
                Yes pfLR =>
                    case decEq (toSimpleRect ul1) (toSimpleRect ul2) of
                        Yes pfUL =>
                            case decEq (toSimpleRect ur1) (toSimpleRect ur2) of
                                Yes pfUR => -- You might not know this, but the diamond antipattern is Actually Good. Or, rather, I think it's impossible to avoid given how I defined a Rectangle and given that each contradiction needs to be handled according to its own type.
                                    Yes (equalSimpleRectsGiveEqualSizedSumRects ll1 ll2 pfLL lr1 lr2 pfLR ul1 ul2 pfUL ur1 ur2 pfUR {x=x} {y=y} {pfxLow1} {pfxHigh1} {pfyLeft1} {pfyRight1} {pfxLow2} {pfxHigh2} {pfyLeft2} {pfyRight2})
                                No contraUR => No (upperRightHandSimpleRectMustBeEqualForEqualSizedSumRects contraUR)
                        No contraUL => No (upperLeftHandSimpleRectMustBeEqualForEqualSizedSumRects contraUL)
                No contraLR => No (lowerRightHandSimpleRectMustBeEqualForEqualSizedSumRects contraLR)
        No contraLL => No (lowerLeftHandSimpleRectMustBeEqualForEqualSizedSumRects contraLL)

||| Lemma allowing you to pull the proofs of equality out of an EqualSizedSumRect
getSameSizeProofsEqSizedSumRect : 
    {ll1: Rectangle ll1Simp} -> {ll2: Rectangle ll2Simp} ->
    {lr1: Rectangle lr1Simp} -> {lr2: Rectangle lr2Simp} ->
    {ul1: Rectangle ul1Simp} -> {ul2: Rectangle ul2Simp} ->
    {ur1: Rectangle ur1Simp} -> {ur2: Rectangle ur2Simp} ->
    EqualSizedSumRects 
        (SumRect ll1 lr1 ul1 ur1 {pfxLow = pfxLow1} {pfxHigh = pfxHigh1} {pfyLeft = pfyLeft1} {pfyRight = pfyRight1}) 
        (SumRect ll2 lr2 ul2 ur2 {pfxLow = pfxLow2} {pfxHigh = pfxHigh2} {pfyLeft = pfyLeft2} {pfyRight = pfyRight2}) ->
    ((ll1Simp = ll2Simp),(lr1Simp=lr2Simp),(ul1Simp=ul2Simp),(ur1Simp=ur2Simp))
getSameSizeProofsEqSizedSumRect (AreEqualSizedSumRects ll1 lr1 ul1 ur1 ll2 lr2 ul2 ur2) = (Refl,Refl,Refl,Refl) -- kind of shocked that this worked 
                                                                                                                -- but Idris is smarter than me and I won't question it :)
||| Lemma stating that if two SumRects are equal, they are EqualSizedSumRects
equalSumRectsAreEqualSized : ((SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) = (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2})) -> 
                             EqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2)
equalSumRectsAreEqualSized {lowerLHS1} {lowerRHS1} {upperLHS1} {upperRHS1} {lowerLHS2} {lowerRHS2} {upperLHS2} {upperRHS2} {x} {y} {pfxLow1} {pfxHigh1} {pfyLeft1} {pfyRight1} {pfxLow2} {pfxHigh2} {pfyLeft2} {pfyRight2} pf = 
    ?eqHole1
    -- let (pfLl,pfLr,pfUl,pfUr) = (equalSumRectsHaveEqualParts pf) in
    --     let pfLlhs = (equalRectsHaveEqualSimpleRects pfLl) in
    --         let pfLrhs = (equalRectsHaveEqualSimpleRects pfLr) in
    --             let pfUlhs = (equalRectsHaveEqualSimpleRects pfUl) in
    --                 let pfUrhs = (equalRectsHaveEqualSimpleRects pfUr) in
    --                     equalSimpleRectsGiveEqualSizedSumRects lowerLHS1 lowerLHS2 pfLlhs lowerRHS1 lowerRHS2 pfLrhs upperLHS1 upperLHS2 pfUlhs upperRHS1 upperRHS2 pfUrhs {x} {y} {pfxLow1=pfxLow1} {pfxHigh1=pfxHigh1} {pfyLeft1=pfyLeft1} {pfyRight1=pfyRight1} {pfxLow2=pfxLow2} {pfxHigh2=pfxHigh2} {pfyLeft2=pfyLeft2} {pfyRight2=pfyRight2}


--------------------------------------------------------------------------------
--                                 Equality                                   --
--------------------------------------------------------------------------------

-- ||| Lemma stating that if the 

Eq (Rectangle a) where
    (==) (SingleRect a) (SingleRect a) = True
    (==) (SingleRect _) (SumRect _ _ _ _) = False
    (==) (SumRect lowerLHS lowerRhs upperLHS upperRHS) (SingleRect _) = False
    (==) (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2}) =
        case (decEqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2})) of
            Yes eqSizedSumRects =>
                let (pfLlhs,pfLrhs,pfUlhs,pfUrhs) = getSameSizeProofsEqSizedSumRect eqSizedSumRects in
                    ((replace pfLlhs lowerLHS1) == lowerLHS2) && ((replace pfLrhs lowerRHS1) == lowerRHS2) && ((replace pfUlhs upperLHS1) == upperLHS2) && ((replace pfUrhs upperRHS1) == upperRHS2)
            No _ => False


notEqualSumRectContra : (notEqualSizedSumRects : EqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2) -> Void) -> (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 = SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2) -> Void
notEqualSumRectContra notEqualSizedSumRects equalSumRects = notEqualSizedSumRects (equalSumRectsAreEqualSized equalSumRects)

getFirstFrom4Tuple : (a,b,c,d) -> a
getFirstFrom4Tuple (x,_,_,_) = x

noHolellhs : 
    {lowerLHS1 : Rectangle rlLHS} -> {lowerLHS2 : Rectangle rlLHS} ->
    (llhsContra : ((lowerLHS1 = lowerLHS2) -> Void)) -> 
    ((SumRect lowerLHS1 _ _ _) = (SumRect lowerLHS2 _ _ _)) -> 
    Void
noHolellhs {lowerLHS1} {lowerLHS2} llhsContra sumRectEq =
    llhsContra (equalSumRectsHaveEqualLLHS sumRectEq)

DecEq (Rectangle a) where
    decEq (SingleRect a) (SingleRect a) = Yes Refl
    decEq (SingleRect _) (SumRect _ _ _ _) = No absurd
    decEq (SumRect lowerLHS lowerRhs upperLHS upperRHS) (SingleRect _) = No absurd
    decEq (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2}) =
        case decEqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2}) of
            Yes eqSizedSumRects =>
                let (pfLlhs,pfLrhs,pfUlhs,pfUrhs) = getSameSizeProofsEqSizedSumRect eqSizedSumRects in
                    case decEq (replace pfLlhs lowerLHS1) lowerLHS2 of
                        Yes llhsEqual =>
                            case decEq (replace pfLrhs lowerRHS1) lowerRHS2 of
                                Yes lrhsEqual =>
                                    case decEq (replace pfUlhs upperLHS1) upperLHS2 of
                                        Yes ulhsEqual => case decEq (replace pfUrhs upperRHS1) upperRHS2 of
                                            Yes urhsEqual => Yes ?yesHole
                                            No urhsContra => ?a4 --No (\sumRectEq => urhsContra (equalSumRectsHaveEqualURHS sumRectEq))
                                        No ulhsContra => ?a3 -- No (\sumRectEq => ulhsContra (equalSumRectsHaveEqualULHS sumRectEq))
                                No lrhsContra => ?a2 --No (\sumRectEq => lrhsContra (equalSumRectsHaveEqualLRHS sumRectEq))
                        No llhsContra => No (\sumRectEq => llhsContra ((equalSumRectsHaveEqualLLHS (replaceLlhsSumrect {pfSimpleRect = pfLlhs} sumRectEq)))) --(noHolellhs {lowerLHS1 = (replace pfLlhs lowerLHS1)} {lowerLHS2} llhsContra)
            No notEqualSumRects => No (notEqualSumRectContra notEqualSumRects)
-- --------------------------------------------------------------------------------
-- --                                 Views                                      --
-- --------------------------------------------------------------------------------



-- -- -- ||| Create a row of 1x1 rectangles, length x and width 1. Built using lower rects as a matter of convention. It "shouldn't" matter :)
-- -- -- rowMaker : (x:Nat) -> Rectangle x (S Z)
-- -- -- rowMaker Z = SingleRect Z (S Z)
-- -- -- rowMaker (S Z) = SingleRect (S Z) (S Z)
-- -- -- rowMaker (S k) = ?rowHole --rewrite (S k = plus (S Z) k) in (rewrite (S Z = plus Z (S Z)) in (SumRect (SingleRect (S Z) (S Z)) (rowMaker k) (SingleRect (S Z) Z) (SingleRect k Z)))

-- -- -- -- ||| Create a row of length 1 and width y. Built using left rects as a matter of convention. It "shouldn't" matter :)
-- -- -- -- colMaker : (y:Nat) -> Rectangle (S Z) y
-- -- -- -- colMaker Z = SingleRect (S Z) Z
-- -- -- -- colMaker (S Z) = SingleRect (S Z) (S Z)
-- -- -- -- colMaker (S k) = SumRect (SingleRect (S Z) (S Z)) (SingleRect Z (S Z)) (colMaker k) (SingleRect Z k)

-- -- -- ||| View of a rectangle as a sum of rows
-- -- -- data RectangleRow : (Rectangle a) -> Type where
-- -- --     ||| Row representation of an empty row rectangle of length x.
-- -- --     Empty: {y: Nat} -> RectangleRow (SingleRect (MkRect Z y))
-- -- --     ||| A single vector of x 1x1 rows.
-- -- --     SingleRow : (x:Nat) -> RectangleRow (SingleRect x (S Z))
-- -- --     ||| A SingleRect x y is y rows of length x.
-- -- --     Rows : Vect y (RectangleRow (SingleRect x (S Z))) -> RectangleRow (SingleRect x y)
-- -- --     ||| A row representation of a SumRect is the sum of four RectangleRows
-- -- --     SumRows: {lhsLoRect: Rectangle x1 y1} -> {rhsLoRect: Rectangle x2 y1} -> {lhsHiRect: Rectangle x1 y2} -> {rhsHiRect: Rectangle x2 y2} ->
-- -- --              RectangleRow lhsLoRect -> RectangleRow rhsLoRect -> RectangleRow lhsHiRect -> RectangleRow rhsHiRect ->
-- -- --              RectangleRow (SumRect lhsLoRect rhsLoRect lhsHiRect rhsHiRect)

            
-- -- -- rectToRectangleRow_rhs_4 : (x:Nat) -> (y:Nat) -> Vect y (RectangleRow (SingleRect x 1))
-- -- -- rectToRectangleRow_rhs_4 x Z = []
-- -- -- rectToRectangleRow_rhs_4 x (S k) = (SingleRow x) :: (rectToRectangleRow_rhs_4 x k)

-- -- -- ||| Covering function for RectangleRow
-- -- -- rectToRectangleRow : (rect: Rectangle x y) -> RectangleRow rect             
-- -- -- rectToRectangleRow {x = x} {y = Z} (SingleRect x Z) = Empty x
-- -- -- rectToRectangleRow {x = x} {y = (S k)} (SingleRect x (S k)) = 
-- -- --     let vect = rectToRectangleRow_rhs_4 x (S k) in
-- -- --         Rows vect
-- -- -- rectToRectangleRow (SumRect lhsLow rhsLow lhsHigh rhsHigh) = 
-- -- --     SumRows (rectToRectangleRow lhsLow) (rectToRectangleRow rhsLow) (rectToRectangleRow lhsHigh) (rectToRectangleRow rhsHigh)





-- -- -- ||| A PrimitiveSumRect is a specific SumRect where the constituents are SingleRects    
-- -- -- data PrimitiveSumRect : Rectangle x1 y1 -> Rectangle x2 y1 -> Rectangle x1 y2 -> Rectangle x2 y2 -> Type where
-- -- --     MkPrimSumRect : PrimitiveSumRect (SingleRect x1 y1) (SingleRect x2 y1) (SingleRect x1 y2) (SingleRect x2 y2)



-- -- -- --  decEq {x} {y} {lhsLow: Rectangle x1 y1} {lhsHigh: Rectangle x1 y2} {rhsLow: Rectangle x2 y1} {rhsHigh: Rectangle x2 y2} {pfx: x = x1 + x2} {pfy: y = y1 + y2} (SumRect lhsLow rhsLow lhsHigh rhsHigh) (SumRect lhsLow rhsLow lhsHigh rhsHigh) = ?h
-- -- -- --  decEq (SingleRect x y) (SumRect _ _ _ _) = ?deh1
-- -- -- --  decEq (SumRect lhsLow rhsLow lhsHigh rhsHigh) (SingleRect x y) = ?deh2

-- -- -- ||| Definition of containment for a coordinate (x1,y1) in a rectangle x y.
-- -- -- data ContainedCoordinate : (rect:Rectangle x y) -> Type where
-- -- --     ||| The type defines containment here, not the nature of the rectangle. We make LTE explicit to give the compiler a break :) Maybe not necessary.
-- -- --     IsInRectangle : (x1:Nat) -> (y1:Nat) -> (pfX: (LTE x1 x)) -> (pfY : LTE y1 y) -> ContainedCoordinate rect


-- -- -- ||| Simple helper method mapping a rect to Nothing for a SingleRect and to the appropriate RectangleQuadrant for a SumRect
-- -- -- coordToQuadrant : Rectangle x y -> (x1:Nat) -> (y1:Nat) -> {auto pfx: LTE x1 x} -> {auto pfy: LTE y1 y} -> Maybe RectangleQuadrant
-- -- -- coordToQuadrant (SingleRect x y) x1 y1 = Nothing
-- -- -- coordToQuadrant (SumRect lhsLow rhsLow lhsHigh rhsHigh) x1 y1 = case (isLTE x1 (rectangleWidth lhsLow)) of
-- -- --                                                                     Yes _ => case (isLTE y1 (rectangleHeight lhsLow)) of
-- -- --                                                                                         Yes _ => Just LHSLow
-- -- --                                                                                         No _ => Just LHSHigh
-- -- --                                                                     No (contraXIsRight) => case (isLTE y1 (rectangleHeight lhsLow)) of
-- -- --                                                                                                 Yes _ => Just RHSLow
-- -- --                                                                                                 No _ => Just RHSHigh

-- -- -- ||| Representation of a ContainedCoordinate in a SumRect as a ContainedCoordinate in one of its composite rects
-- -- -- coordInQuadrantView: (rect: Rectangle x y) -> ContainedCoordinate rect -> (subRect: Rectangle a b ** (ContainedCoordinate subRect))

-- -- -- --coordInQuadrantView {auto pfx: plus x1 x2 = x} {auto pfy: plus y1 y2 = y} (SumRect lhsLow rhsLow lhsHigh rhsHigh) cc = ?coordInQuadrantView_rhs_2



-- -- -- -- generateUniformGrid : (x:Nat) -> (y:Nat) -> Rectangle (x,y)
-- -- -- -- generateUniformGrid Z Z = SingleRect Z Z
-- -- -- -- generateUniformGrid (S Z) (S Z) = SingleRect (S Z) (S Z)
-- -- -- -- generateUniformGrid (S k) (S j) = rewrite ((plus j 1) = S j) in SumRect (generateUniformGrid k j) (generateUniformGrid (S Z) j) (generateUniformGrid k (S Z)) (SingleRect (S Z) (S Z))

              

-- -- -- -- createSubdivision : Rectangle x y -> (x1:Nat) -> (y1: Nat) ->  {auto pfx: LTE x1 x} -> {auto pfy : LTE y1 y} -> Rectangle x y
-- -- -- -- createSubdivision (SingleRect x y) x1 y1 {pfx} {pfy} = rewrite (equivalentRectangleLemma x1 x y1 y pfx pfy) in ((SumRect (SingleRect x1 y1) (SingleRect (x - x1) y1) (SingleRect x1 (y - y1)) (SingleRect (x - x1) (y - y1))))
-- -- -- -- createSubdivision (SumRect lhsLow rhsLow lhsHigh rhsHigh) x1 y1 = let rect = (SumRect lhsLow rhsLow lhsHigh rhsHigh) in 
-- -- -- --                                                                     case coordToQuadrant rect x1 y1 of
-- -- -- --                                                                         Nothing => ?h2
-- -- -- --                                                                         (Just x) => case x of
-- -- -- --                                                                                         LHSLow => SumRect (createSubdivision lhsLow x1 y1) rhsLow lhsHigh rhsHigh
-- -- -- --                                                                                         LHSHigh => ?h_2
-- -- -- --                                                                                         RHSLow => ?h_3
-- -- -- --                                                                                         RHSHigh => ?h_4
