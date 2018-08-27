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
    SumRect:    (lowerLHS: Rectangle (MkRect x1 y1)) ->
                (lowerRhs: Rectangle (MkRect x2 y1)) ->
                (upperLHS: Rectangle (MkRect x1 y2)) ->
                (upperRHS: Rectangle (MkRect x2 y2)) ->
                {x: Nat} -> {pfx: plus x1 x2 = x} ->
                {y: Nat} -> {pfy: plus y1 y2 = y} ->
                Rectangle (MkRect x y)

--     ||| Given a x-by-y1 rectangle, add an x-by-y2 rectangle to the top.
--     AddToTop: {y: Nat} -> {y1: Nat} -> {y2:Nat} ->
--         {auto pfy: (plus y1 y2 = y)} ->
--         (bottom: (Rectangle (MkSimpleRect x y1))) -> 
--         (top: (Rectangle (MkSimpleRect x y2))) -> 
--         Rectangle (MkSimpleRect x y)

--     AddToRight: {x: Nat} -> {x1: Nat} -> {x2:Nat} ->
--                 {auto pfx: (plus x1 x2 = x)} ->
--                 (left: (Rectangle (MkSimpleRect x1 y))) -> 
--                 (right: Rectangle (MkSimpleRect x2 y)) -> 
--                 Rectangle (MkSimpleRect x y)
-- --------------------------------------------------------------------------------
-- --                                 Uninhabited/Void                           --
-- --------------------------------------------------------------------------------

        
-- --------------------------------------------------------------------------------
-- --                         Simple helper lemmas                               --
-- --------------------------------------------------------------------------------

rectangleWidth: (rect: Rectangle a) -> Nat
rectangleWidth {a} rect = width a

rectangleHeight: (rect: Rectangle a) -> Nat
rectangleHeight {a} rect = height a

-- toSimpleRect : Rectangle a -> SimpleRect
-- toSimpleRect {a} _ = a

-- rewriteRect: {a : SimpleRect} -> {b: SimpleRect} -> (a = b) -> Rectangle a -> Rectangle b
-- rewriteRect prf rect = replace prf rect

-- -- --------------------------------------------------------------------------------
-- -- --                                 Equality                                   --
-- -- --------------------------------------------------------------------------------

-- ||| Proofs that two Rectangles have the same size.
-- data SameSizedRects: Rectangle a -> Rectangle b -> Type where
--     ||| Two Rectangles have the same size <=> their underlying SimpleRects are equal.
--     SameSize: {a: SimpleRect} -> {b: SimpleRect} -> (pf: a = b) -> (rA: Rectangle a) -> (rB: Rectangle b) -> SameSizedRects rA rB

-- ||| Lemma stating that two SameSizedRects have the same underyling SimpleRect
-- sameSizesAreSameSimpleRects: {a: SimpleRect} -> {b: SimpleRect} -> {rA: Rectangle a} -> {rB: Rectangle b} -> SameSizedRects rA rB -> (a=b)
-- sameSizesAreSameSimpleRects (SameSize pf _ _) = pf

-- ||| Decision procedure for determining if two Rects have the same size.
-- sameSizeDecision: (rA: Rectangle a) -> (rB: Rectangle b) -> Dec (SameSizedRects rA rB)
-- sameSizeDecision {a} {b} rA rB = case decEq a b of
--                                     Yes pf => Yes (SameSize pf rA rB)
--                                     No contra => No (\ssRects => contra ((sameSizesAreSameSimpleRects) ssRects))

-- ||| Helper function for deciding whether to apply a function that only works on two Rectangles of the same type.
-- decideToApplyToTwoRects: {t:Type} -> (rA: Rectangle a) -> (rb: Rectangle b) -> (f: Rectangle b -> Rectangle b -> t) -> Maybe t
-- decideToApplyToTwoRects rA rB f = 
--     case sameSizeDecision rA rB of
--         Yes (SameSize pf rA rB) => let rA' = rewriteRect pf rA in
--                                     Just (f rA' rB)
--         No _ => Nothing

-- ||| Implementation of procedural equality for Rectangle.        
-- Eq (Rectangle a) where
--   (==) (SingleRect _) (SingleRect _) = True
--   (==) (SingleRect (MkSimpleRect _ _)) (AddToTop _ _) = False
--   (==) (SingleRect (MkSimpleRect _ _)) (AddToRight _ _) = False
--   (==) (AddToTop _ _) (SingleRect (MkSimpleRect _ _)) = False
--   (==) (AddToTop _ _) (AddToRight _ _) = False
--   (==) (AddToTop {y} {y1=y1A} {y2=y2A} {pfy=pfyA} bottom1 top1) (AddToTop {y} {y1=y1B} {y2=y2B} {pfy=pfyB} bottom2 top2) =
--      case sameSizeDecision bottom1 bottom2 of
--         Yes (SameSize pfBottomIsSameSize bottom1 bottom2) => ?h
--         No contra => False
--   (==) (AddToRight z w) rB = ?Eq_rhs_3
--   (/=) x y = ?Neq_rhs
-- --     (==) (SingleRect a) (SingleRect a) = True
-- --     (==) (SingleRect _) (SumRect _ _ _ _) = False
-- --     (==) (SumRect _ _ _ _) (SingleRect _) = False
-- --     (==) (SumRect lhsLow1 rhsLow1 lhsHigh1 rhsHigh1) (SumRect lhsLow2 rhsLow2 lhsHigh2 rhsHigh2) = 
-- --         case decideToApplyToTwoRects lhsLow1 lhsLow2 (==) of
-- --             Nothing => False
-- --             Just False => False
-- --             Just True => 
-- --                 case decideToApplyToTwoRects rhsLow1 rhsLow2 (==) of
-- --                     Nothing => False
-- --                     Just False => False
-- --                     Just True =>
-- --                         case decideToApplyToTwoRects lhsHigh1 lhsHigh2 (==) of
-- --                             Nothing => False
-- --                             Just False => False
-- --                             Just True =>
-- --                                 case decideToApplyToTwoRects rhsHigh1 rhsHigh2 (==) of
-- --                                     Nothing => False
-- --                                     Just False => False
-- --                                     Just True => True

-- -- Uninhabited (SameSizedSimpleRect (MkSimpleRect x y) (MkSimpleRect (S x) y)) where
-- --   uninhabited x = rewrite (x = S x) in ?h


-- -- ||| Proofs that two rectangles have the same size.
-- -- data SameSizedRects : (Rectangle a) -> (Rectangle b) -> Type where
-- --     SameSize : {a: SimpleRect x1 y1} -> {b: SimpleRect x1 y1} -> (rectA: Rectangle a) -> (rectB: Rectangle b) -> SameSizedRects rectA rectB  

-- -- ||| Proof that, given (x: Rectangle a) and (y: Rectangle b), we can rewerite y: Rectangle a <=> rectangleHeight a == rectangleHeight b && rectangleWidth a == rectangleWidth b
-- -- rectangleRewrite : {a: SimpleRect x1 y1} -> {b: SimpleRect x2 y2} -> (rectA: Rectangle a) -> (rectB: Rectangle b) -> (pfLength: x1 = x2) -> (pfWidth: y1 = y2) -> SameSizedRects rectA rectB

-- -- using (rect: SimpleRect x y)
-- --     implementation [rectEq] Eq (Rectangle rect) where
-- --         (==) (SingleRect rect) (SingleRect rect) = True
-- --         (==) (SingleRect (MkRect x y)) (SumRect lhsLow rhsLow lhsHigh rhsHigh) = False
-- --         (==) (SumRect lhsLow rhsLow lhsHigh rhsHigh) (SingleRect (MkRect x y)) = False
-- --         (==) (SumRect lhsLow1 rhsLow1 lhsHigh1 rhsHigh1) (SumRect lhsLow2 rhsLow2 lhsHigh2 rhsHigh2) = ?rhsEq_5


-- -- --------------------------------------------------------------------------------
-- -- --                            Decidable Equality                              --
-- -- --------------------------------------------------------------------------------

-- -- using (rect: SimpleRect x y)
-- --         implementation [rectDecEq] DecEq (Rectangle rect) where
-- --             decEq x1 x2 = ?DecEq_rhs_1


-- -- -- |||
-- -- -- replace2 : {a : _} -> {a1 : _} -> {a2 : _} ->
-- -- --            {b : _} -> {b1 : _} -> {b2 : _} ->
-- --            {P : a -> b -> Type} ->
-- --            (a1 = a2) -> (b1 = b2) -> P a1 b1 -> P a2 b2
-- -- replace2 Refl Refl p = p



-- -- -- using (x1: Nat)
-- -- --     using (x2: Nat)
-- -- --         using (contra: Not (x1 = x2))
-- -- --             using (a: Rectangle x1 y1)
-- -- --                 using (b: Rectangle x2 y2)
-- -- --                     getContra: x1 = x2 -> Void
-- -- --                     getContra pf = contra pf
-- -- --                     implementation [mustHaveSameWidth] Uninhabited (SameSizedRects a b) where
-- -- --                         uninhabited (SameSize pfx pfy a b) = getContra pfx

-- -- -- -- ifSameSizedRectsThenEqualX : {a: Rectangle x1 y1} -> {b: Rectangle x2 y2} -> SameSizedRects a b -> (x1 = x2)
-- -- -- -- ifSameSizedRectsThenEqualX {a} {b} (SameSize pfx pfy a b) = pfx

-- -- -- -- ifSameSizedRectsThenEqualY : {a: Rectangle x1 y1} -> {b: Rectangle x2 y2} -> SameSizedRects a b -> (y1 = y2)
-- -- -- -- ifSameSizedRectsThenEqualY {a} {b} (SameSize pfx pfy a b) = pfy

-- -- -- -- sameSizedRectsMustBeSameWidth: {x1: Nat} -> {x2: Nat} -> {a: Rectangle x1 y1} -> {b: Rectangle x2 y2} -> (Not (x1=x2)) -> (SameSizedRects a b -> Void)
-- -- -- -- -- sameSizedRectsMustBeSameWidth contra = 

-- -- -- areSameSized : (a: Rectangle x1 y1) -> (b: Rectangle x2 y2) -> Dec (SameSizedRects a b)
-- -- -- areSameSized {x1} {y1} {x2} {y2} a b = case decEq x1 x2 of
-- -- --                                             Yes pfx => case decEq y1 y2 of
-- -- --                                                              Yes pfy => Yes (SameSize pfx pfy a b)
-- -- --                                                              No contra => No ?noh
-- -- --                                             No contra => No ?noh2

-- -- ||| Trivial lemma for rewriting the types of rectangles of equal size.
-- -- equalSizedRectsHaveSameType : (a: Rectangle x1 y1) -> (b: Rectangle x2 y2) -> ((rectangleWidth a) = (rectangleWidth b)) -> ((rectangleHeight a) = (rectangleHeight b))-> ((x1,y1) = (x2,y2))
-- -- equalSizedRectsHaveSameType {x1} {y1} {x2} {y2} a b prf prf1 = rewrite prf in (rewrite prf1 in Refl)

-- -- ||| Helper function for comparing rects with a proof that the length and width are equal
-- -- rectShoeHorner : {t: Type} -> (a: Rectangle x1 y1) -> (b: Rectangle x2 y2) -> (f: Rectangle x2 y2 -> Rectangle x2 y2 -> t) -> (pfx: x1 = x2) -> (pfy: y1 = y2) -> t
-- -- rectShoeHorner a b f pfx pfy = let newRect = replace2 pfx pfy a in
-- --                                     f newRect b

-- -- ||| Helper function for comparing inhomogeneous rects                                
-- -- rectComparer : {t: Type} -> {x1:Nat} -> {x2:Nat} -> {y1:Nat} -> {y2:Nat} -> (a: Rectangle x1 y1) -> (b: Rectangle x2 y2) -> (f: Rectangle x2 y2 -> Rectangle x2 y2 -> t) -> Maybe t
-- -- rectComparer {x1} {x2} {y1} {y2} a b f = case decEq x1 x2 of
-- --                                                     Yes pfx => case decEq y1 y2 of
-- --                                                                 Yes pfy => Just (rectShoeHorner a b f pfx pfy)
-- --                                                                 No _ => Nothing
-- --                                                     No _ => Nothing

-- -- implementation Eq (Rectangle x y) where
-- --   (==) (SingleRect x y) (SingleRect x y) = True
-- --   (==) (SingleRect x y) (SumRect lhsLow rhsLow lhsHigh rhsHigh) = False
-- --   (==) (SumRect lhsLow rhsLow lhsHigh rhsHigh) (SingleRect x y) = False
-- --   (==) (SumRect a b c d) (SumRect e f g h) = case rectComparer a e (==) of
-- --                                                 Nothing => False
-- --                                                 Just False => False
-- --                                                 Just True => case rectComparer b f (==) of
-- --                                                                 Nothing => False
-- --                                                                 Just False => False
-- --                                                                 Just True => case rectComparer c g (==) of
-- --                                                                     Nothing => False
-- --                                                                     Just False => False
-- --                                                                     Just True => case rectComparer d h (==) of
-- --                                                                                     Nothing => False
-- --                                                                                     Just False => False
-- --                                                                                     Just True => True

-- --   (/=) x y = ?Eq_rhs_2



-- -- --

-- -- ||| Create a row of 1x1 rectangles, length x and width 1. Built using lower rects as a matter of convention. It "shouldn't" matter :)
-- -- rowMaker : (x:Nat) -> Rectangle x (S Z)
-- -- rowMaker Z = SingleRect Z (S Z)
-- -- rowMaker (S Z) = SingleRect (S Z) (S Z)
-- -- rowMaker (S k) = ?rowHole --rewrite (S k = plus (S Z) k) in (rewrite (S Z = plus Z (S Z)) in (SumRect (SingleRect (S Z) (S Z)) (rowMaker k) (SingleRect (S Z) Z) (SingleRect k Z)))

-- -- -- ||| Create a row of length 1 and width y. Built using left rects as a matter of convention. It "shouldn't" matter :)
-- -- -- colMaker : (y:Nat) -> Rectangle (S Z) y
-- -- -- colMaker Z = SingleRect (S Z) Z
-- -- -- colMaker (S Z) = SingleRect (S Z) (S Z)
-- -- -- colMaker (S k) = SumRect (SingleRect (S Z) (S Z)) (SingleRect Z (S Z)) (colMaker k) (SingleRect Z k)

-- -- ||| View of a rectangle as a sum of rows
-- -- data RectangleRow : (Rectangle x y) -> Type where
-- --     ||| Row representation of an empty row rectangle of length x.
-- --     Empty: (x:Nat) -> RectangleRow (SingleRect x Z)
-- --     ||| A single vector of x 1x1 rows.
-- --     SingleRow : (x:Nat) -> RectangleRow (SingleRect x (S Z))
-- --     ||| A SingleRect x y is y rows of length x.
-- --     Rows : Vect y (RectangleRow (SingleRect x (S Z))) -> RectangleRow (SingleRect x y)
-- --     ||| A row representation of a SumRect is the sum of four RectangleRows
-- --     SumRows: {lhsLoRect: Rectangle x1 y1} -> {rhsLoRect: Rectangle x2 y1} -> {lhsHiRect: Rectangle x1 y2} -> {rhsHiRect: Rectangle x2 y2} ->
-- --              RectangleRow lhsLoRect -> RectangleRow rhsLoRect -> RectangleRow lhsHiRect -> RectangleRow rhsHiRect ->
-- --              RectangleRow (SumRect lhsLoRect rhsLoRect lhsHiRect rhsHiRect)

            
-- -- rectToRectangleRow_rhs_4 : (x:Nat) -> (y:Nat) -> Vect y (RectangleRow (SingleRect x 1))
-- -- rectToRectangleRow_rhs_4 x Z = []
-- -- rectToRectangleRow_rhs_4 x (S k) = (SingleRow x) :: (rectToRectangleRow_rhs_4 x k)

-- -- ||| Covering function for RectangleRow
-- -- rectToRectangleRow : (rect: Rectangle x y) -> RectangleRow rect             
-- -- rectToRectangleRow {x = x} {y = Z} (SingleRect x Z) = Empty x
-- -- rectToRectangleRow {x = x} {y = (S k)} (SingleRect x (S k)) = 
-- --     let vect = rectToRectangleRow_rhs_4 x (S k) in
-- --         Rows vect
-- -- rectToRectangleRow (SumRect lhsLow rhsLow lhsHigh rhsHigh) = 
-- --     SumRows (rectToRectangleRow lhsLow) (rectToRectangleRow rhsLow) (rectToRectangleRow lhsHigh) (rectToRectangleRow rhsHigh)

-- -- ||| Helper function for pulling a tuple of (length, height) out as a dependent pair
-- -- rectToDepPair : Rectangle x y -> (a:(Nat,Nat)**(Rectangle (fst a) (snd a)))
-- -- rectToDepPair rect = let a = (rectangleWidth rect, rectangleHeight rect) in
-- --                         (a ** rect)
-- -- --rectToDepPair rect = ((rectangleWidth rect), (rectangleHeight rect)) ** rect

-- -- ||| Helper lemma stating that equality of Nats implies equality of rectangle types.
-- -- equalNatsgiveEqualRects : (x1=x2) -> (y1=y2) -> ((Rectangle x1 y1) = (Rectangle x2 y2))
-- -- equalNatsgiveEqualRects a b = rewrite b in (rewrite a in Refl)

-- -- implementation [rectUninhabited1] Uninhabited (SingleRect x y = SumRect lhsLow rhsLow lhsHigh rhsHigh) where
-- --     uninhabited Refl impossible

-- -- implementation [rectUninhabitsed2] Uninhabited (SumRect lhsLow rhsLow lhsHigh rhsHigh = SingleRect x y) where
-- --     uninhabited Refl impossible    


-- -- ||| Proof that a SumRect is not a SingleRect
-- -- data IsSingle : Rectangle x y -> Type where
-- --     ItIsSingle : IsSingle (SingleRect x y)

-- -- implementation [singlecantbesumrect] Uninhabited (IsSingle (SumRect a b c d)) where
-- --     uninhabited IsSingle impossible

-- -- using implementation singlecantbesumrect
-- --     ||| A decision procedure for IsSingle
-- --     isItSingle : (rect: Rectangle x y) -> Dec (IsSingle rect)
-- --     isItSingle (SingleRect x y) = Yes ItIsSingle
-- --     isItSingle (SumRect _ _ _ _) = No absurd

-- -- ||| A PrimitiveSumRect is a specific SumRect where the constituents are SingleRects    
-- -- data PrimitiveSumRect : Rectangle x1 y1 -> Rectangle x2 y1 -> Rectangle x1 y2 -> Rectangle x2 y2 -> Type where
-- --     MkPrimSumRect : PrimitiveSumRect (SingleRect x1 y1) (SingleRect x2 y1) (SingleRect x1 y2) (SingleRect x2 y2)

-- -- ||| Proofs of equality for rectangles.
-- -- data EqualRect : Rectangle x y -> Rectangle x y -> Type where
-- --     ||| There is only one SingleRect of Rectangle x y.
-- --     EqualSingle : EqualRect (SingleRect x y) (SingleRect x y)
-- --     ||| SumRects are equal if their constituent parts are equal.
-- --     EqualSum: (EqualRect lhsLow1 lhsLow2) -> (EqualRect rhsLow1 rhsLow2) -> (EqualRect lhsHigh1 lhsHigh2) -> (EqualRect rhsHigh1 rhsHigh2) ->
-- --                 EqualRect (SumRect lhsLow1 rhsLow1 lhsHigh1 rhsHigh1) (SumRect lhsLow2 rhsLow2 lhsHigh2 rhsHigh2)

-- -- implementation [singleAndSumNotEqual] Uninhabited (EqualRect (SingleRect x y) (SumRect a b c d)) where
-- --     uninhabited EqualRect impossible

-- -- data EqualPrimitiveSumRect : Rectangle x y -> Rectangle x y -> Type where    
-- -- -- using implementation rectUninhabited1
-- -- --     DecEq (Rectangle x y) where    
-- -- --         decEq (SingleRect x y) (SingleRect x y) = Yes Refl
-- -- --         decEq (SingleRect (x1+x2) (y1+y2)) (SumRect lhsLow1 rhsLow1 lhsHigh1 rhsHigh1) = ?h
-- -- --         decEq (SumRect lhsLow1 rhsLow1 lhsHigh1 rhsHigh1) (SumRect lhsLow2 rhsLow2 lhsHigh2 rhsHigh2) = ?hi

-- -- --  decEq {x} {y} {lhsLow: Rectangle x1 y1} {lhsHigh: Rectangle x1 y2} {rhsLow: Rectangle x2 y1} {rhsHigh: Rectangle x2 y2} {pfx: x = x1 + x2} {pfy: y = y1 + y2} (SumRect lhsLow rhsLow lhsHigh rhsHigh) (SumRect lhsLow rhsLow lhsHigh rhsHigh) = ?h
-- -- --  decEq (SingleRect x y) (SumRect _ _ _ _) = ?deh1
-- -- --  decEq (SumRect lhsLow rhsLow lhsHigh rhsHigh) (SingleRect x y) = ?deh2

-- -- ||| Definition of containment for a coordinate (x1,y1) in a rectangle x y.
-- -- data ContainedCoordinate : (rect:Rectangle x y) -> Type where
-- --     ||| The type defines containment here, not the nature of the rectangle. We make LTE explicit to give the compiler a break :) Maybe not necessary.
-- --     IsInRectangle : (x1:Nat) -> (y1:Nat) -> (pfX: (LTE x1 x)) -> (pfY : LTE y1 y) -> ContainedCoordinate rect



-- -- ||| A simple datatype to convey which quadrant a sumrect component is in, without having to reference the constuctor
-- -- data RectangleQuadrant = 
-- --     LHSLow |
-- --     LHSHigh |
-- --     RHSLow |
-- --     RHSHigh

-- -- ||| Simple helper method mapping a quadrant to Nothing for a SingleRect and to the appropriate component for a SumRect
-- -- quadrantToRect: RectangleQuadrant -> (Rectangle x y) -> Maybe (a:(Nat,Nat)**(Rectangle (fst a) (snd a)))
-- -- quadrantToRect _ (SingleRect _ _) = Nothing
-- -- quadrantToRect x (SumRect lhsLow rhsLow lhsHigh rhsHigh) = case x of
-- --                                                             LHSLow => Just (rectToDepPair lhsLow)
-- --                                                             LHSHigh => Just (rectToDepPair lhsHigh)
-- --                                                             RHSLow => Just (rectToDepPair rhsLow)
-- --                                                             RHSHigh => Just (rectToDepPair rhsHigh)

-- -- ||| Simple helper method mapping a rect to Nothing for a SingleRect and to the appropriate RectangleQuadrant for a SumRect
-- -- coordToQuadrant : Rectangle x y -> (x1:Nat) -> (y1:Nat) -> {auto pfx: LTE x1 x} -> {auto pfy: LTE y1 y} -> Maybe RectangleQuadrant
-- -- coordToQuadrant (SingleRect x y) x1 y1 = Nothing
-- -- coordToQuadrant (SumRect lhsLow rhsLow lhsHigh rhsHigh) x1 y1 = case (isLTE x1 (rectangleWidth lhsLow)) of
-- --                                                                     Yes _ => case (isLTE y1 (rectangleHeight lhsLow)) of
-- --                                                                                         Yes _ => Just LHSLow
-- --                                                                                         No _ => Just LHSHigh
-- --                                                                     No (contraXIsRight) => case (isLTE y1 (rectangleHeight lhsLow)) of
-- --                                                                                                 Yes _ => Just RHSLow
-- --                                                                                                 No _ => Just RHSHigh

-- -- ||| Representation of a ContainedCoordinate in a SumRect as a ContainedCoordinate in one of its composite rects
-- -- coordInQuadrantView: (rect: Rectangle x y) -> ContainedCoordinate rect -> (subRect: Rectangle a b ** (ContainedCoordinate subRect))

-- -- --coordInQuadrantView {auto pfx: plus x1 x2 = x} {auto pfy: plus y1 y2 = y} (SumRect lhsLow rhsLow lhsHigh rhsHigh) cc = ?coordInQuadrantView_rhs_2


-- -- ||| Lemma stating that a SumRect will always map to a quadrant
-- -- ifNoQuadrantThenNotSumRect : {rect: Rectangle x y} -> {x1: Nat} -> {y1: Nat} -> {auto pfx: LTE x1 x} -> {auto pfy: LTE y1 y} -> (rect = SumRect _ _ _ _) -> (coordToQuadrant rect x1 y1 = Nothing) -> Void
-- -- ifNoQuadrantThenNotSumRect {rect} {x1} {y1} prfSumRect prfNoCoord = ?ifNoQuadrantThenNotSumRect_rhs


                                                                                                
-- -- ||| Lemma stating that if coordToQuadrant rect x y = Nothing then rect is a SingleRect                                                                                                
-- -- ifNoQuadrantThenSingleRect : {rect: Rectangle x y} -> {x1: Nat} -> {y1: Nat} -> {auto pfx: LTE x1 x} -> {auto pfy: LTE y1 y} -> (coordToQuadrant rect x1 y1 = Nothing) -> (rect = SingleRect x y)
-- -- --ifNoQuadrantThenSingleRect {rect = (SingleRect x y)} prf = Refl
-- -- --ifNoQuadrantThenSingleRect {rect = (SumRect lhsLow rhsLow lhsHigh rhsHigh)} prf impossible
-- -- -- ifNoQuadrantThenSingleRect {rect = (SingleRect x y)} {x1 = x1} {y1 = y1} prf = Refl

-- -- -- generateUniformGrid : (x:Nat) -> (y:Nat) -> Rectangle (x,y)
-- -- -- generateUniformGrid Z Z = SingleRect Z Z
-- -- -- generateUniformGrid (S Z) (S Z) = SingleRect (S Z) (S Z)
-- -- -- generateUniformGrid (S k) (S j) = rewrite ((plus j 1) = S j) in SumRect (generateUniformGrid k j) (generateUniformGrid (S Z) j) (generateUniformGrid k (S Z)) (SingleRect (S Z) (S Z))

-- -- ||| Definition of congruence for rectangles.
-- -- data CongruentRectangle : Rectangle x1 y1 -> Rectangle x2 y2 -> Type where
-- --     ||| Congruence for two single rectangles means the side lengths are the same.
-- --     CongruentSingle :   CongruentRectangle (SingleRect x y) (SingleRect x y)
-- --     ||| Congruence for a two sum-rectangles means the sum components are congruent.
-- --     CongruentSum :      (pflhsLow : CongruentRectangle lhsLow1 lhsLow2) ->
-- --                         (pfrhsLow : CongruentRectangle rhsLow1 rhsLow2) ->                       
-- --                         (pflhsHigh : CongruentRectangle lhsHigh1 lhsHigh2) ->                            
-- --                         (pfrhsHigh : CongruentRectangle rhsHigh1 rhsHigh2) ->
-- --                         CongruentRectangle (SumRect lhsLow1 rhsLow1 lhsHigh1 rhsHigh1) (SumRect lhsLow2 rhsLow2 lhsHigh2 rhsHigh2)

-- -- congruenceIsTransitive : {a: Rectangle x1 y1} -> {b: Rectangle x2 y2} -> {c: Rectangle x3 y3} -> (CongruentRectangle a b) -> (CongruentRectangle b c) -> (CongruentRectangle a c)
-- -- congruenceIsTransitive CongruentSingle CongruentSingle = CongruentSingle
-- -- congruenceIsTransitive (CongruentSum _ _ _ _) CongruentSingle impossible
-- -- congruenceIsTransitive CongruentSingle (CongruentSum _ _ _ _) impossible
-- -- congruenceIsTransitive (CongruentSum e f g h) (CongruentSum i j k l) = 
-- --     CongruentSum (congruenceIsTransitive e i) (congruenceIsTransitive f j) (congruenceIsTransitive g k) (congruenceIsTransitive h l)


-- -- negativeCancellationLemma: (left: Nat) -> (right: Nat) -> (gtPf: LTE left right) -> right = plus left (minus right left)
-- -- negativeCancellationLemma Z Z _ = Refl
-- -- negativeCancellationLemma Z (S k) _ = Refl
-- -- negativeCancellationLemma (S k) Z (gtPf) = absurd gtPf
-- -- negativeCancellationLemma (S k) (S j) (gtPf) =  rewrite (negativeCancellationLemma k j (fromLteSucc gtPf) ) in Refl
               
-- -- equivalentRectangleLemma : (x1: Nat) -> (x: Nat) -> (y1: Nat) -> (y: Nat) -> (gtpfX : LTE x1 x) -> (gtpfY : LTE y1 y) -> (Rectangle x y = (Rectangle ((x1) + (x - x1)) ((y1) + (y - y1))))
-- -- equivalentRectangleLemma Z Z Z Z _ _ = Refl
-- -- equivalentRectangleLemma Z Z Z (S k) gtpfX gtpfY = Refl
-- -- equivalentRectangleLemma _ _ (S k) Z gtpfX gtpfY = absurd gtpfY
-- -- equivalentRectangleLemma Z Z (S k) (S j) gtpfX gtpfY = equalNatsgiveEqualRects Refl ( (negativeCancellationLemma (S k) (S j) (gtpfY)))-- ewrite (equalNatsgiveEqualRects Refl (negativeCancellationLemma (S k) (S j) gtpfY)) in ?h
-- -- equivalentRectangleLemma Z (S k) Z Z gtpfX gtpfY = Refl
-- -- equivalentRectangleLemma Z (S k) Z (S j) gtpfX gtpfY = Refl
-- -- equivalentRectangleLemma Z (S k) (S j) (S i) gtpfX gtpfY = equalNatsgiveEqualRects Refl ( (negativeCancellationLemma (S j) (S i) (gtpfY)))
-- -- equivalentRectangleLemma (S k) Z _ _ gtpfX gtpfY = absurd gtpfX
-- -- equivalentRectangleLemma (S k) (S j) Z Z gtpfX gtpfY = equalNatsgiveEqualRects ( (negativeCancellationLemma (S k) (S j) (gtpfX))) Refl
-- -- equivalentRectangleLemma (S k) (S j) Z (S i) gtpfX gtpfY = equalNatsgiveEqualRects ( (negativeCancellationLemma (S k) (S j) (gtpfX))) Refl
-- -- equivalentRectangleLemma (S k) (S j) (S i) (S n) gtpfX gtpfY = equalNatsgiveEqualRects ( (negativeCancellationLemma (S k) (S j) (gtpfX))) ( (negativeCancellationLemma (S i) (S n) (gtpfY)))

-- -- -- createSubdivision : Rectangle x y -> (x1:Nat) -> (y1: Nat) ->  {auto pfx: LTE x1 x} -> {auto pfy : LTE y1 y} -> Rectangle x y
-- -- -- createSubdivision (SingleRect x y) x1 y1 {pfx} {pfy} = rewrite (equivalentRectangleLemma x1 x y1 y pfx pfy) in ((SumRect (SingleRect x1 y1) (SingleRect (x - x1) y1) (SingleRect x1 (y - y1)) (SingleRect (x - x1) (y - y1))))
-- -- -- createSubdivision (SumRect lhsLow rhsLow lhsHigh rhsHigh) x1 y1 = let rect = (SumRect lhsLow rhsLow lhsHigh rhsHigh) in 
-- -- --                                                                     case coordToQuadrant rect x1 y1 of
-- -- --                                                                         Nothing => ?h2
-- -- --                                                                         (Just x) => case x of
-- -- --                                                                                         LHSLow => SumRect (createSubdivision lhsLow x1 y1) rhsLow lhsHigh rhsHigh
-- -- --                                                                                         LHSHigh => ?h_2
-- -- --                                                                                         RHSLow => ?h_3
-- -- --                                                                                         RHSHigh => ?h_4


-- -- -- getRectangularSubdivision :   (xAnchor:Nat) -> 
-- -- --                               (yAnchor: Nat) -> 
-- -- --                               Rectangle (x,y) ->
-- -- --                               {auto pfX : LTE xAnchor x} -> 
-- -- --                               {auto pfY : LTE yAnchor y} ->
-- -- --                               {auto pfEqx : (plus xAnchor (x-xAnchor)) = x} ->
-- -- --                               {auto pfEqy : (plus yAnchor (y-yAnchor)) = y} ->
-- -- --                               Rectangle (x,y)
-- -- -- getRectangularSubdivision {x} {y} xAnchor yAnchor _ = ?h -- SumRect (SingleRect xAnchor yAnchor) (SingleRect (x-xAnchor) yAnchor) (SingleRect xAnchor (y-yAnchor)) (SingleRect (x-xAnchor) (y-yAnchor))