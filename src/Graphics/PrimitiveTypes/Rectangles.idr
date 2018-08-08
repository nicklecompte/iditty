module Graphics.PrimitiveTypes.Rectangles

import Data.Vect

%access public export
%default total

||| A datatype representing a generic gridded rectangle. It can either be a primitive rectangle or the sum of four rectangles. 0-length/width is allowed. The idea is to create a self-contained analytical geometry with only constructive geometric primitives. For an x,y plane, a Rectangle x y might be written as SumRect of y Rect x 1, which are themselves Rect 1 1. This would correspond to a uniform grid of size x*y.
data Rectangle : Nat -> Nat -> Type where

    ||| A basic rectangle with width and height. In practice, this may be a "base rectangle." For a drawing, consider this a canvas.
    ||| @ x - the width
    ||| @ y - the height
    SingleRect :    (x:Nat) -> (y:Nat) -> Rectangle x y

    ||| A rectangle can be the sum of four smaller rectangles. Example: consider a 3x4 rectangle, with a 1x1 lower-left-corner, a 3x1 lower-right-corner, a 1x2 upper-left, and 3x2 upper-right.
    ||| @ lhsLow - the rectangle in the lower left-hand corner. In the example this would be SimpleRect 1 1.
    ||| @ rhsLow - the rectangle in the lower right-hand corner. In the example this would be SimpleRect 3 1.
    ||| @ lhsHigh - the rectangle in the upper left-hand corner. In the example this would be SimpleRect 1 2.
    ||| @ rhsHigh - the rectangle in the upper right-hand corner. In the example this would be SimpleRect 3 2.
    SumRect :   (lhsLow : Rectangle x1 y1) -> 
                (rhsLow : Rectangle x2 y1) -> 
                (lhsHigh : Rectangle x1 y2) ->  
                (rhsHigh : Rectangle x2 y2) -> 
                Rectangle (x1+x2) (y1+y2)

||| Helper function for casting a rectangle to its width (x)            
rectangleWidth: Rectangle x y -> Nat
rectangleWidth {x} r = x

||| Helper function for casting a rectangle to its height (y)
rectangleHeight: Rectangle x y -> Nat
rectangleHeight {y} r = y

||| Create a row of length x and width 1. Built using lower rects as a matter of convention. It "shouldn't" matter :)
rowMaker : (x:Nat) -> Rectangle x (S Z)
rowMaker Z = SingleRect Z (S Z)
rowMaker (S k) = SumRect (SingleRect (S Z) (S Z)) (rowMaker k) (SingleRect (S Z) Z) (SingleRect k Z)

||| Create a row of length 1 and width y. Built using left rects as a matter of convention. It "shouldn't" matter :)
colMaker : (y:Nat) -> Rectangle (S Z) y
colMaker Z = SingleRect (S Z) Z
colMaker (S k) = SumRect (SingleRect (S Z) (S Z)) (SingleRect Z (S Z)) (colMaker k) (SingleRect Z k)

||| View of a rectangle as a sum of rows
data RectangleRow : (Rectangle x y) -> Type where
    ||| Row representation of an empty rectangle
    Empty: (x:Nat) -> RectangleRow (SingleRect x Z)
    SingleRow : (x:Nat) -> RectangleRow (SingleRect x (S Z))
    Rows : Vect y (RectangleRow (SingleRect x (S Z))) -> RectangleRow (SingleRect x y)
    SumRows: {lhsLoRect: Rectangle x1 y1} -> {rhsLoRect: Rectangle x2 y1} -> {lhsHiRect: Rectangle x1 y2} -> {rhsHiRect: Rectangle x2 y2} ->
             RectangleRow lhsLoRect -> RectangleRow rhsLoRect -> RectangleRow lhsHiRect -> RectangleRow rhsHiRect ->
             RectangleRow (SumRect lhsLoRect rhsLoRect lhsHiRect rhsHiRect)

rectToRectangleRow_rhs_4 : (x:Nat) -> (y:Nat) -> Vect y (RectangleRow (SingleRect x 1))
rectToRectangleRow_rhs_4 x Z = []
rectToRectangleRow_rhs_4 x (S k) = (SingleRow x) :: (rectToRectangleRow_rhs_4 x k)

||| Covering function for RectangleRow
rectToRectangleRow : (rect: Rectangle x y) -> RectangleRow rect             
rectToRectangleRow {x = x} {y = Z} (SingleRect x Z) = Empty x
rectToRectangleRow {x = x} {y = (S k)} (SingleRect x (S k)) = 
    let vect = rectToRectangleRow_rhs_4 x (S k) in
        Rows vect
rectToRectangleRow (SumRect lhsLow rhsLow lhsHigh rhsHigh) = 
    SumRows (rectToRectangleRow lhsLow) (rectToRectangleRow rhsLow) (rectToRectangleRow lhsHigh) (rectToRectangleRow rhsHigh)

||| Helper function for pulling a tuple of (length, height) out as a dependent pair
rectToDepPair : Rectangle x y -> (a:(Nat,Nat)**(Rectangle (fst a) (snd a)))
rectToDepPair rect = let a = (rectangleWidth rect, rectangleHeight rect) in
                        (a ** rect)
--rectToDepPair rect = ((rectangleWidth rect), (rectangleHeight rect)) ** rect

||| Helper lemma stating that equality of Nats implies equality of rectangle types.
equalNatsgiveEqualRects : (x1=x2) -> (y1=y2) -> ((Rectangle x1 y1) = (Rectangle x2 y2))
equalNatsgiveEqualRects a b = rewrite b in (rewrite a in Refl)

implementation [rectUninhabited1] Uninhabited (SingleRect x y = SumRect lhsLow rhsLow lhsHigh rhsHigh) where
    uninhabited Refl impossible

implementation [rectUninhabited2] Uninhabited (SumRect lhsLow rhsLow lhsHigh rhsHigh = SingleRect x y) where
    uninhabited Refl impossible    


||| Proofs that (x1,y1) is contained in a rectangle x y
data ContainedCoordinate : (rect:Rectangle x y) -> Type where
    IsInRectangle : (x1:Nat) -> (y1:Nat) -> (pfX: (LTE x1 x)) -> (pfY : LTE y1 y) -> ContainedCoordinate rect


||| A simple datatype to convey which quadrant a sumrect component is in, without having to reference the constuctor
data RectangleQuadrant = 
    LHSLow |
    LHSHigh |
    RHSLow |
    RHSHigh

||| Simple helper method mapping a quadrant to Nothing for a SingleRect and to the appropriate component for a SumRect
quadrantToRect: RectangleQuadrant -> (Rectangle x y) -> Maybe (a:(Nat,Nat)**(Rectangle (fst a) (snd a)))
quadrantToRect _ (SingleRect _ _) = Nothing
quadrantToRect x (SumRect lhsLow rhsLow lhsHigh rhsHigh) = case x of
                                                            LHSLow => Just (rectToDepPair lhsLow)
                                                            LHSHigh => Just (rectToDepPair lhsHigh)
                                                            RHSLow => Just (rectToDepPair rhsLow)
                                                            RHSHigh => Just (rectToDepPair rhsHigh)

||| Simple helper method mapping a rect to Nothing for a SingleRect and to the appropriate RectangleQuadrant for a SumRect
coordToQuadrant : Rectangle x y -> (x1:Nat) -> (y1:Nat) -> {auto pfx: LTE x1 x} -> {auto pfy: LTE y1 y} -> Maybe RectangleQuadrant
coordToQuadrant (SingleRect x y) x1 y1 = Nothing
coordToQuadrant (SumRect lhsLow rhsLow lhsHigh rhsHigh) x1 y1 = case (isLTE x1 (rectangleWidth lhsLow)) of
                                                                    Yes _ => case (isLTE y1 (rectangleHeight lhsLow)) of
                                                                                        Yes _ => Just LHSLow
                                                                                        No _ => Just LHSHigh
                                                                    No (contraXIsRight) => case (isLTE y1 (rectangleHeight lhsLow)) of
                                                                                                Yes _ => Just RHSLow
                                                                                                No _ => Just RHSHigh

||| Representation of a ContainedCoordinate in a SumRect as a ContainedCoordinate in one of its composite rects
coordInQuadrantView: (rect: Rectangle x y) -> ContainedCoordinate rect -> (subRect: Rectangle a b ** (ContainedCoordinate subRect))

--coordInQuadrantView {auto pfx: plus x1 x2 = x} {auto pfy: plus y1 y2 = y} (SumRect lhsLow rhsLow lhsHigh rhsHigh) cc = ?coordInQuadrantView_rhs_2


||| Lemma static that a SumRect will always map to a quadrant
ifNoQuadrantThenNotSumRect : {rect: Rectangle x y} -> {x1: Nat} -> {y1: Nat} -> {auto pfx: LTE x1 x} -> {auto pfy: LTE y1 y} -> (rect = SumRect _ _ _ _) -> (coordToQuadrant rect x1 y1 = Nothing) -> Void
ifNoQuadrantThenNotSumRect {rect} {x1} {y1} prfSumRect prfNoCoord = ?ifNoQuadrantThenNotSumRect_rhs


                                                                                                
||| Lemma stating that if coordToQuadrant rect x y = Nothing then rect is a SingleRect                                                                                                
ifNoQuadrantThenSingleRect : {rect: Rectangle x y} -> {x1: Nat} -> {y1: Nat} -> {auto pfx: LTE x1 x} -> {auto pfy: LTE y1 y} -> (coordToQuadrant rect x1 y1 = Nothing) -> (rect = SingleRect x y)
--ifNoQuadrantThenSingleRect {rect = (SingleRect x y)} prf = Refl
--ifNoQuadrantThenSingleRect {rect = (SumRect lhsLow rhsLow lhsHigh rhsHigh)} prf impossible
-- ifNoQuadrantThenSingleRect {rect = (SingleRect x y)} {x1 = x1} {y1 = y1} prf = Refl

-- generateUniformGrid : (x:Nat) -> (y:Nat) -> Rectangle (x,y)
-- generateUniformGrid Z Z = SingleRect Z Z
-- generateUniformGrid (S Z) (S Z) = SingleRect (S Z) (S Z)
-- generateUniformGrid (S k) (S j) = rewrite ((plus j 1) = S j) in SumRect (generateUniformGrid k j) (generateUniformGrid (S Z) j) (generateUniformGrid k (S Z)) (SingleRect (S Z) (S Z))

||| Definition of congruence for rectangles.
data CongruentRectangle : Rectangle x1 y1 -> Rectangle x2 y2 -> Type where
    ||| Congruence for two single rectangles means the side lengths are the same.
    CongruentSingle :   CongruentRectangle (SingleRect x y) (SingleRect x y)
    ||| Congruence for a two sum-rectangles means the sum components are congruent.
    CongruentSum :      (pflhsLow : CongruentRectangle lhsLow1 lhsLow2) ->
                        (pfrhsLow : CongruentRectangle rhsLow1 rhsLow2) ->                       
                        (pflhsHigh : CongruentRectangle lhsHigh1 lhsHigh2) ->                            
                        (pfrhsHigh : CongruentRectangle rhsHigh1 rhsHigh2) ->
                        CongruentRectangle (SumRect lhsLow1 rhsLow1 lhsHigh1 rhsHigh1) (SumRect lhsLow2 rhsLow2 lhsHigh2 rhsHigh2)

congruenceIsTransitive : {a: Rectangle x1 y1} -> {b: Rectangle x2 y2} -> {c: Rectangle x3 y3} -> (CongruentRectangle a b) -> (CongruentRectangle b c) -> (CongruentRectangle a c)
congruenceIsTransitive CongruentSingle CongruentSingle = CongruentSingle
congruenceIsTransitive (CongruentSum _ _ _ _) CongruentSingle impossible
congruenceIsTransitive CongruentSingle (CongruentSum _ _ _ _) impossible
congruenceIsTransitive (CongruentSum e f g h) (CongruentSum i j k l) = 
    CongruentSum (congruenceIsTransitive e i) (congruenceIsTransitive f j) (congruenceIsTransitive g k) (congruenceIsTransitive h l)


negativeCancellationLemma: (left: Nat) -> (right: Nat) -> (gtPf: LTE left right) -> right = plus left (minus right left)
negativeCancellationLemma Z Z _ = Refl
negativeCancellationLemma Z (S k) _ = Refl
negativeCancellationLemma (S k) Z (gtPf) = absurd gtPf
negativeCancellationLemma (S k) (S j) (gtPf) =  rewrite (negativeCancellationLemma k j (fromLteSucc gtPf) ) in Refl
               
equivalentRectangleLemma : (x1: Nat) -> (x: Nat) -> (y1: Nat) -> (y: Nat) -> (gtpfX : LTE x1 x) -> (gtpfY : LTE y1 y) -> (Rectangle x y = (Rectangle ((x1) + (x - x1)) ((y1) + (y - y1))))
equivalentRectangleLemma Z Z Z Z _ _ = Refl
equivalentRectangleLemma Z Z Z (S k) gtpfX gtpfY = Refl
equivalentRectangleLemma _ _ (S k) Z gtpfX gtpfY = absurd gtpfY
equivalentRectangleLemma Z Z (S k) (S j) gtpfX gtpfY = equalNatsgiveEqualRects Refl ( (negativeCancellationLemma (S k) (S j) (gtpfY)))-- ewrite (equalNatsgiveEqualRects Refl (negativeCancellationLemma (S k) (S j) gtpfY)) in ?h
equivalentRectangleLemma Z (S k) Z Z gtpfX gtpfY = Refl
equivalentRectangleLemma Z (S k) Z (S j) gtpfX gtpfY = Refl
equivalentRectangleLemma Z (S k) (S j) (S i) gtpfX gtpfY = equalNatsgiveEqualRects Refl ( (negativeCancellationLemma (S j) (S i) (gtpfY)))
equivalentRectangleLemma (S k) Z _ _ gtpfX gtpfY = absurd gtpfX
equivalentRectangleLemma (S k) (S j) Z Z gtpfX gtpfY = equalNatsgiveEqualRects ( (negativeCancellationLemma (S k) (S j) (gtpfX))) Refl
equivalentRectangleLemma (S k) (S j) Z (S i) gtpfX gtpfY = equalNatsgiveEqualRects ( (negativeCancellationLemma (S k) (S j) (gtpfX))) Refl
equivalentRectangleLemma (S k) (S j) (S i) (S n) gtpfX gtpfY = equalNatsgiveEqualRects ( (negativeCancellationLemma (S k) (S j) (gtpfX))) ( (negativeCancellationLemma (S i) (S n) (gtpfY)))

-- createSubdivision : Rectangle x y -> (x1:Nat) -> (y1: Nat) ->  {auto pfx: LTE x1 x} -> {auto pfy : LTE y1 y} -> Rectangle x y
-- createSubdivision (SingleRect x y) x1 y1 {pfx} {pfy} = rewrite (equivalentRectangleLemma x1 x y1 y pfx pfy) in ((SumRect (SingleRect x1 y1) (SingleRect (x - x1) y1) (SingleRect x1 (y - y1)) (SingleRect (x - x1) (y - y1))))
-- createSubdivision (SumRect lhsLow rhsLow lhsHigh rhsHigh) x1 y1 = let rect = (SumRect lhsLow rhsLow lhsHigh rhsHigh) in 
--                                                                     case coordToQuadrant rect x1 y1 of
--                                                                         Nothing => ?h2
--                                                                         (Just x) => case x of
--                                                                                         LHSLow => SumRect (createSubdivision lhsLow x1 y1) rhsLow lhsHigh rhsHigh
--                                                                                         LHSHigh => ?h_2
--                                                                                         RHSLow => ?h_3
--                                                                                         RHSHigh => ?h_4


-- getRectangularSubdivision :   (xAnchor:Nat) -> 
--                               (yAnchor: Nat) -> 
--                               Rectangle (x,y) ->
--                               {auto pfX : LTE xAnchor x} -> 
--                               {auto pfY : LTE yAnchor y} ->
--                               {auto pfEqx : (plus xAnchor (x-xAnchor)) = x} ->
--                               {auto pfEqy : (plus yAnchor (y-yAnchor)) = y} ->
--                               Rectangle (x,y)
-- getRectangularSubdivision {x} {y} xAnchor yAnchor _ = ?h -- SumRect (SingleRect xAnchor yAnchor) (SingleRect (x-xAnchor) yAnchor) (SingleRect xAnchor (y-yAnchor)) (SingleRect (x-xAnchor) (y-yAnchor))