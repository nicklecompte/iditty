module Graphics.PrimitiveTypes.Rectangles.Rectangles

import Graphics.PrimitiveTypes.Rectangles.SimpleRects


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
--                                 Equality                                   --
--------------------------------------------------------------------------------

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
