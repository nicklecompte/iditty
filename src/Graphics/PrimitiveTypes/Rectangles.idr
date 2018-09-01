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

||| Get the height of the underlying SimpleRectangle.
rectangleHeight: (rect: Rectangle a) -> Nat
rectangleHeight {a} rect = height a

||| Get the underlying SimpleRectangle.
toSimpleRect: Rectangle a -> SimpleRectangle
toSimpleRect _ {a} = a

||| "Shoehorns" a Rectangle (a) into a Maybe (Rectangle b). Just _ if a = b, Nothing o.w.
rectangleShoehorner: Rectangle a -> (b: SimpleRectangle) -> Maybe (Rectangle b)
rectangleShoehorner rect b {a} = case decEq a b of
                                    Yes prfSameSimpleRectangle => Just (replace prfSameSimpleRectangle rect)
                                    No _ => Nothing

--------------------------------------------------------------------------------
--                                 Equality                                   --
--------------------------------------------------------------------------------


Eq (Rectangle a) where
    (==) (SingleRect a) (SingleRect a) = True
    (==) (SingleRect _) (SumRect _ _ _ _) = False
    (==) (SumRect lowerLHS lowerRhs upperLHS upperRHS) (SingleRect _) = False
    (==) (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2) = ?eqSumRectHole
--     (==) (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2) =
--         case decEq (toSimpleRect lowerLHS1) (toSimpleRect lowerLHS2) of
--             Yes pfLHS => 
--                 case ((replace pfLHS lowerLHS1) == lowerLHS2) of
--                     True => 
--                         case decEq (toSimpleRect lowerRHS1) (toSimpleRect lowerRHS2) of
--                             Yes pfRHS => 
--                                 case ((replace pfRHS lowerRHS1) == lowerRHS2) of
--                                     True => case decEq (toSimpleRect upperLHS1) (toSimpleRect upperLHS2) of
--                                                 Yes pfULHS => case ((replace pfULHS upperLHS1) == upperLHS2) of
--                                                                     True => case decEq (toSimpleRect upperRHS1) (toSimpleRect upperRHS2) of -- todo: we shouldn't need to check this, make it a property.
--                                                                                 Yes pfURHS => case ((replace pfURHS upperRHS1) == upperRHS2) of
--                                                                                                 True => True
--                                                                                                 _ => False
--                                                                                 No _ => False
--                                                                     False => False
--                                                 No _ => False
--                                     _ => False
--                             No _ => False
--                     _ => False
--             No _ => False

-- -- ||| Proofs that two SumRects are actually the same Rectangle.
-- -- data EqualSumRects : Rectangle a -> Rectangle a -> Type where
-- --     SameParts:  (lowerLHS: Rectangle (MkRect x1 y1)) ->
-- --                 (lowerRHS: Rectangle (MkRect x2 y1)) ->
-- --                 (upperLHS: Rectangle (MkRect x1 y2)) ->
-- --                 (upperRHS: Rectangle (MkRect x2 y2)) ->
-- --                 {x: Nat} -> {pfx: plus x1 x2 = x} ->
-- --                 {y: Nat} -> {pfy: plus y1 y2 = y} ->
-- --                 EqualSumRects (SumRect lowerLHS lowerRHS upperLHS upperRHS {x} {y} {pfx} {pfy}) (SumRect lowerLHS lowerRHS upperLHS upperRHS {x} {y} {pfx} {pfy})

-- -- Uninhabited (EqualSumRects (SingleRect a) _) where
-- --     uninhabited (SameParts _ _ _ _) impossible

-- -- Uninhabited (EqualSumRects _ (SingleRect a)) where
-- --     uninhabited (SameParts _ _ _ _) impossible

-- -- ||| Lemma for EqualSumRects r1 r2 -> (r1 = r2)
-- -- equalSumRectsAreEqual: EqualSumRects r1 r2 -> (r1 = r2)
-- -- equalSumRectsAreEqual (SameParts _ _ _ _) = Refl

-- lhsTypeMustMatch:   {a: SimpleRectangle} -> 
--                     {b: SimpleRectangle} -> 
--                     (contra: (a = b) -> Void) -> 
--                     (r1: Rectangle a) -> 
--                     (r2: Rectangle b) -> 
--                     (((SumRect r1 _ _ _) = (SumRect r2 _ _ _)) -> Void)


-- -- ||| Decision procedure for determining if two SumRects are the same.
-- -- decSumRects: 

-- DecEq (Rectangle a) where
--   decEq (SingleRect _) (SingleRect _) = Yes Refl
--   decEq (SingleRect _) (SumRect _ _ _ _) = No absurd
--   decEq (SumRect _ _ _ _) (SingleRect _) = No absurd
--   decEq (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2) = 
--     case decEq (toSimpleRect lowerLHS1) (toSimpleRect lowerLHS2) of
--         Yes pfLHSType => 
--             case decEq (replace pfLHSType lowerLHS1) lowerLHS2 of
--                 Yes pfLHSEqual => 
--                     case decEq (toSimpleRect lowerRHS1) (toSimpleRect lowerRHS2) of
--                         Yes pfRHSType => 
--                             case decEq (replace pfRHSType lowerRHS1) lowerRHS2 of
--                                 Yes pfLRHSEqual => 
--                                     case decEq (toSimpleRect upperLHS1) (toSimpleRect upperLHS2) of
--                                         Yes pfULHSType => 
--                                             case decEq (replace pfULHSType upperLHS1) upperLHS2 of
--                                                 Yes pfULHSEqual => 
--                                                     case decEq (toSimpleRect upperRHS1) (toSimpleRect upperRHS2) of -- todo: we shouldn't need to check this, make it a property.
--                                                         Yes pfURHSType => 
--                                                             case decEq (replace pfURHSType upperRHS1) upperRHS2 of
--                                                                 Yes pfURHSEqual => Yes ?yesH -- (replace pfLHSEqual (replace pfLRHSEqual (replace pfULHSEqual (replace pfURHSEqual Refl))))
--                                                                 No contraURHS => No ?hNoURHS
--                                                         No contraURHSType => No ?hNoURHSType
--                                                 No contraULHSEqual => No ?hNoULHS
--                                         No contraULHSType => No ?hNoULHSType
--                                 No contraLRHSEqual => No ?hNoLRHS
--                         No contraLRHSType => No ?hNoURHSType
--                 No contraLLHSEqual => No ?hNoLLHS
--         No contraLLHSType => No (?hNoLLHSType contraLLHSType)


-- --------------------------------------------------------------------------------
-- --                                 Views                                      --
-- --------------------------------------------------------------------------------


-- -- -- ||| Helper function for comparing rects with a proof that the length and width are equal
-- -- -- rectShoeHorner : {t: Type} -> (a: Rectangle x1 y1) -> (b: Rectangle x2 y2) -> (f: Rectangle x2 y2 -> Rectangle x2 y2 -> t) -> (pfx: x1 = x2) -> (pfy: y1 = y2) -> t
-- -- -- rectShoeHorner a b f pfx pfy = let newRect = replace2 pfx pfy a in
-- -- --                                     f newRect b

-- -- -- ||| Helper function for comparing inhomogeneous rects                                
-- -- -- rectComparer : {t: Type} -> {x1:Nat} -> {x2:Nat} -> {y1:Nat} -> {y2:Nat} -> (a: Rectangle x1 y1) -> (b: Rectangle x2 y2) -> (f: Rectangle x2 y2 -> Rectangle x2 y2 -> t) -> Maybe t
-- -- -- rectComparer {x1} {x2} {y1} {y2} a b f = case decEq x1 x2 of
-- -- --                                                     Yes pfx => case decEq y1 y2 of
-- -- --                                                                 Yes pfy => Just (rectShoeHorner a b f pfx pfy)
-- -- --                                                                 No _ => Nothing
-- -- --                                                     No _ => Nothing





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

-- -- -- ||| Helper function for pulling a tuple of (length, height) out as a dependent pair
-- -- -- rectToDepPair : Rectangle x y -> (a:(Nat,Nat)**(Rectangle (fst a) (snd a)))
-- -- -- rectToDepPair rect = let a = (rectangleWidth rect, rectangleHeight rect) in
-- -- --                         (a ** rect)
-- -- -- --rectToDepPair rect = ((rectangleWidth rect), (rectangleHeight rect)) ** rect

-- -- -- ||| Helper lemma stating that equality of Nats implies equality of rectangle types.
-- -- -- equalNatsgiveEqualRects : (x1=x2) -> (y1=y2) -> ((Rectangle x1 y1) = (Rectangle x2 y2))
-- -- -- equalNatsgiveEqualRects a b = rewrite b in (rewrite a in Refl)

-- -- -- implementation [rectUninhabited1] Uninhabited (SingleRect x y = SumRect lhsLow rhsLow lhsHigh rhsHigh) where
-- -- --     uninhabited Refl impossible

-- -- -- implementation [rectUninhabitsed2] Uninhabited (SumRect lhsLow rhsLow lhsHigh rhsHigh = SingleRect x y) where
-- -- --     uninhabited Refl impossible    


-- -- -- ||| Proof that a SumRect is not a SingleRect
-- -- -- data IsSingle : Rectangle x y -> Type where
-- -- --     ItIsSingle : IsSingle (SingleRect x y)

-- -- -- implementation [singlecantbesumrect] Uninhabited (IsSingle (SumRect a b c d)) where
-- -- --     uninhabited IsSingle impossible

-- -- -- using implementation singlecantbesumrect
-- -- --     ||| A decision procedure for IsSingle
-- -- --     isItSingle : (rect: Rectangle x y) -> Dec (IsSingle rect)
-- -- --     isItSingle (SingleRect x y) = Yes ItIsSingle
-- -- --     isItSingle (SumRect _ _ _ _) = No absurd

-- -- -- ||| A PrimitiveSumRect is a specific SumRect where the constituents are SingleRects    
-- -- -- data PrimitiveSumRect : Rectangle x1 y1 -> Rectangle x2 y1 -> Rectangle x1 y2 -> Rectangle x2 y2 -> Type where
-- -- --     MkPrimSumRect : PrimitiveSumRect (SingleRect x1 y1) (SingleRect x2 y1) (SingleRect x1 y2) (SingleRect x2 y2)

-- -- -- ||| Proofs of equality for rectangles.
-- -- -- data EqualRect : Rectangle x y -> Rectangle x y -> Type where
-- -- --     ||| There is only one SingleRect of Rectangle x y.
-- -- --     EqualSingle : EqualRect (SingleRect x y) (SingleRect x y)
-- -- --     ||| SumRects are equal if their constituent parts are equal.
-- -- --     EqualSum: (EqualRect lhsLow1 lhsLow2) -> (EqualRect rhsLow1 rhsLow2) -> (EqualRect lhsHigh1 lhsHigh2) -> (EqualRect rhsHigh1 rhsHigh2) ->
-- -- --                 EqualRect (SumRect lhsLow1 rhsLow1 lhsHigh1 rhsHigh1) (SumRect lhsLow2 rhsLow2 lhsHigh2 rhsHigh2)

-- -- -- implementation [singleAndSumNotEqual] Uninhabited (EqualRect (SingleRect x y) (SumRect a b c d)) where
-- -- --     uninhabited EqualRect impossible

-- -- -- data EqualPrimitiveSumRect : Rectangle x y -> Rectangle x y -> Type where    
-- -- -- -- using implementation rectUninhabited1
-- -- -- --     DecEq (Rectangle x y) where    
-- -- -- --         decEq (SingleRect x y) (SingleRect x y) = Yes Refl
-- -- -- --         decEq (SingleRect (x1+x2) (y1+y2)) (SumRect lhsLow1 rhsLow1 lhsHigh1 rhsHigh1) = ?h
-- -- -- --         decEq (SumRect lhsLow1 rhsLow1 lhsHigh1 rhsHigh1) (SumRect lhsLow2 rhsLow2 lhsHigh2 rhsHigh2) = ?hi

-- -- -- --  decEq {x} {y} {lhsLow: Rectangle x1 y1} {lhsHigh: Rectangle x1 y2} {rhsLow: Rectangle x2 y1} {rhsHigh: Rectangle x2 y2} {pfx: x = x1 + x2} {pfy: y = y1 + y2} (SumRect lhsLow rhsLow lhsHigh rhsHigh) (SumRect lhsLow rhsLow lhsHigh rhsHigh) = ?h
-- -- -- --  decEq (SingleRect x y) (SumRect _ _ _ _) = ?deh1
-- -- -- --  decEq (SumRect lhsLow rhsLow lhsHigh rhsHigh) (SingleRect x y) = ?deh2

-- -- -- ||| Definition of containment for a coordinate (x1,y1) in a rectangle x y.
-- -- -- data ContainedCoordinate : (rect:Rectangle x y) -> Type where
-- -- --     ||| The type defines containment here, not the nature of the rectangle. We make LTE explicit to give the compiler a break :) Maybe not necessary.
-- -- --     IsInRectangle : (x1:Nat) -> (y1:Nat) -> (pfX: (LTE x1 x)) -> (pfY : LTE y1 y) -> ContainedCoordinate rect



-- -- -- ||| A simple datatype to convey which quadrant a sumrect component is in, without having to reference the constuctor
-- -- -- data RectangleQuadrant = 
-- -- --     LHSLow |
-- -- --     LHSHigh |
-- -- --     RHSLow |
-- -- --     RHSHigh

-- -- -- ||| Simple helper method mapping a quadrant to Nothing for a SingleRect and to the appropriate component for a SumRect
-- -- -- quadrantToRect: RectangleQuadrant -> (Rectangle x y) -> Maybe (a:(Nat,Nat)**(Rectangle (fst a) (snd a)))
-- -- -- quadrantToRect _ (SingleRect _ _) = Nothing
-- -- -- quadrantToRect x (SumRect lhsLow rhsLow lhsHigh rhsHigh) = case x of
-- -- --                                                             LHSLow => Just (rectToDepPair lhsLow)
-- -- --                                                             LHSHigh => Just (rectToDepPair lhsHigh)
-- -- --                                                             RHSLow => Just (rectToDepPair rhsLow)
-- -- --                                                             RHSHigh => Just (rectToDepPair rhsHigh)

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


-- -- -- ||| Lemma stating that a SumRect will always map to a quadrant
-- -- -- ifNoQuadrantThenNotSumRect : {rect: Rectangle x y} -> {x1: Nat} -> {y1: Nat} -> {auto pfx: LTE x1 x} -> {auto pfy: LTE y1 y} -> (rect = SumRect _ _ _ _) -> (coordToQuadrant rect x1 y1 = Nothing) -> Void
-- -- -- ifNoQuadrantThenNotSumRect {rect} {x1} {y1} prfSumRect prfNoCoord = ?ifNoQuadrantThenNotSumRect_rhs


                                                                                                
-- -- -- ||| Lemma stating that if coordToQuadrant rect x y = Nothing then rect is a SingleRect                                                                                                
-- -- -- ifNoQuadrantThenSingleRect : {rect: Rectangle x y} -> {x1: Nat} -> {y1: Nat} -> {auto pfx: LTE x1 x} -> {auto pfy: LTE y1 y} -> (coordToQuadrant rect x1 y1 = Nothing) -> (rect = SingleRect x y)
-- -- -- --ifNoQuadrantThenSingleRect {rect = (SingleRect x y)} prf = Refl
-- -- -- --ifNoQuadrantThenSingleRect {rect = (SumRect lhsLow rhsLow lhsHigh rhsHigh)} prf impossible
-- -- -- -- ifNoQuadrantThenSingleRect {rect = (SingleRect x y)} {x1 = x1} {y1 = y1} prf = Refl

-- -- -- -- generateUniformGrid : (x:Nat) -> (y:Nat) -> Rectangle (x,y)
-- -- -- -- generateUniformGrid Z Z = SingleRect Z Z
-- -- -- -- generateUniformGrid (S Z) (S Z) = SingleRect (S Z) (S Z)
-- -- -- -- generateUniformGrid (S k) (S j) = rewrite ((plus j 1) = S j) in SumRect (generateUniformGrid k j) (generateUniformGrid (S Z) j) (generateUniformGrid k (S Z)) (SingleRect (S Z) (S Z))

-- -- -- ||| Definition of congruence for rectangles.
-- -- -- data CongruentRectangle : Rectangle x1 y1 -> Rectangle x2 y2 -> Type where
-- -- --     ||| Congruence for two single rectangles means the side lengths are the same.
-- -- --     CongruentSingle :   CongruentRectangle (SingleRect x y) (SingleRect x y)
-- -- --     ||| Congruence for a two sum-rectangles means the sum components are congruent.
-- -- --     CongruentSum :      (pflhsLow : CongruentRectangle lhsLow1 lhsLow2) ->
-- -- --                         (pfrhsLow : CongruentRectangle rhsLow1 rhsLow2) ->                       
-- -- --                         (pflhsHigh : CongruentRectangle lhsHigh1 lhsHigh2) ->                            
-- -- --                         (pfrhsHigh : CongruentRectangle rhsHigh1 rhsHigh2) ->
-- -- --                         CongruentRectangle (SumRect lhsLow1 rhsLow1 lhsHigh1 rhsHigh1) (SumRect lhsLow2 rhsLow2 lhsHigh2 rhsHigh2)

-- -- -- congruenceIsTransitive : {a: Rectangle x1 y1} -> {b: Rectangle x2 y2} -> {c: Rectangle x3 y3} -> (CongruentRectangle a b) -> (CongruentRectangle b c) -> (CongruentRectangle a c)
-- -- -- congruenceIsTransitive CongruentSingle CongruentSingle = CongruentSingle
-- -- -- congruenceIsTransitive (CongruentSum _ _ _ _) CongruentSingle impossible
-- -- -- congruenceIsTransitive CongruentSingle (CongruentSum _ _ _ _) impossible
-- -- -- congruenceIsTransitive (CongruentSum e f g h) (CongruentSum i j k l) = 
-- -- --     CongruentSum (congruenceIsTransitive e i) (congruenceIsTransitive f j) (congruenceIsTransitive g k) (congruenceIsTransitive h l)
               
-- -- -- equivalentRectangleLemma : (x1: Nat) -> (x: Nat) -> (y1: Nat) -> (y: Nat) -> (gtpfX : LTE x1 x) -> (gtpfY : LTE y1 y) -> (Rectangle x y = (Rectangle ((x1) + (x - x1)) ((y1) + (y - y1))))
-- -- -- equivalentRectangleLemma Z Z Z Z _ _ = Refl
-- -- -- equivalentRectangleLemma Z Z Z (S k) gtpfX gtpfY = Refl
-- -- -- equivalentRectangleLemma _ _ (S k) Z gtpfX gtpfY = absurd gtpfY
-- -- -- equivalentRectangleLemma Z Z (S k) (S j) gtpfX gtpfY = equalNatsgiveEqualRects Refl ( (negativeCancellationLemma (S k) (S j) (gtpfY)))-- ewrite (equalNatsgiveEqualRects Refl (negativeCancellationLemma (S k) (S j) gtpfY)) in ?h
-- -- -- equivalentRectangleLemma Z (S k) Z Z gtpfX gtpfY = Refl
-- -- -- equivalentRectangleLemma Z (S k) Z (S j) gtpfX gtpfY = Refl
-- -- -- equivalentRectangleLemma Z (S k) (S j) (S i) gtpfX gtpfY = equalNatsgiveEqualRects Refl ( (negativeCancellationLemma (S j) (S i) (gtpfY)))
-- -- -- equivalentRectangleLemma (S k) Z _ _ gtpfX gtpfY = absurd gtpfX
-- -- -- equivalentRectangleLemma (S k) (S j) Z Z gtpfX gtpfY = equalNatsgiveEqualRects ( (negativeCancellationLemma (S k) (S j) (gtpfX))) Refl
-- -- -- equivalentRectangleLemma (S k) (S j) Z (S i) gtpfX gtpfY = equalNatsgiveEqualRects ( (negativeCancellationLemma (S k) (S j) (gtpfX))) Refl
-- -- -- equivalentRectangleLemma (S k) (S j) (S i) (S n) gtpfX gtpfY = equalNatsgiveEqualRects ( (negativeCancellationLemma (S k) (S j) (gtpfX))) ( (negativeCancellationLemma (S i) (S n) (gtpfY)))

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
