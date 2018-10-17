module Graphics.PrimitiveTypes.Rectangles.Rectangles

import Graphics.PrimitiveTypes.Rectangles.SimpleRects
import Decidable.Order

%access public export
%default total

--------------------------------------------------------------------------------
--                                 Definitions                                --
--------------------------------------------------------------------------------

||| A datatype representing a generic gridded rectangle. 
||| It can either be a primitive rectangle, the horizontal sum of two rectangles,
||| or the vertical sum of two rectangles. 
||| 0-length/width is allowed. 
||| The idea is to create a self-contained analytical geometry with only constructive geometric primitives. 
data Rectangle : SimpleRectangle -> Type where
    ||| A basic Rectangle with width and height. In practice, this may be a "base rectangle." For a drawing, consider this a canvas.
    SingleRect : (a:SimpleRectangle) -> Rectangle a
    ||| A Rectangle built by the sum of two Rectangles aligned on the horizontal edge. 
    ||| The sizes must align by having the same width.
    HorizontalSum:
                {x: Nat} -> {y1: Nat} -> {y2: Nat} ->
                (lowerRect: Rectangle (MkRect x y1)) ->
                (upperRect: Rectangle (MkRect x y2)) ->
                Rectangle (MkRect x (plus y1 y2))
    ||| A Rectangle built by the sum of two Rectangles aligned on the vertical edge. 
    ||| The sizes must align by having the same height.                
    VerticalSum:
                {x1: Nat} -> {x2: Nat} -> {y: Nat} ->
                (leftRect: Rectangle (MkRect x1 y)) ->
                (rightRect: Rectangle (MkRect x2 y)) ->
                Rectangle (MkRect (plus x1 x2) y)

-- ||| A simple datatype to convey which quadrant a sumrect component is in, without having to reference the constuctor
-- data RectangleQuadrant = 
--     LHSLow |
--     LHSHigh |
--     RHSLow |
--     RHSHigh             
    
    

--------------------------------------------------------------------------------
--                                 Uninhabited/Void                           --
--------------------------------------------------------------------------------

implementation [uninhabitedSingleHorizontal] Uninhabited (SingleRect _ = HorizontalSum _ _) where
    uninhabited Refl impossible
        
implementation [uninhabitedHorizontalSingle] Uninhabited (HorizontalSum _ _ = SingleRect _) where
    uninhabited Refl impossible

implementation [uninhabitedSingleVertical] Uninhabited (SingleRect _ = VerticalSum _ _) where
    uninhabited Refl impossible
        
implementation [uninhabitedVerticalSingle] Uninhabited (VerticalSum _ _ = SingleRect _) where
    uninhabited Refl impossible

implementation [uninhabitedHorizontalVertical] Uninhabited (HorizontalSum _ _ = VerticalSum _ _) where
    uninhabited Refl impossible
        
implementation [uninhabitedVerticalHorizontal] Uninhabited (VerticalSum _ _ = HorizontalSum _ _) where
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
