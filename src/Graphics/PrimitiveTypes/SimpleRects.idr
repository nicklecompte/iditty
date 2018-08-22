module Graphics.PrimitiveTypes.SimpleRects

import Data.Vect

%access public export
%default total

--------------------------------------------------------------------------------
--                                 Definitions                                --
--------------------------------------------------------------------------------


||| A datatype representing a very simple rectangle.
record SimpleRect where
    constructor MkSimpleRect
    width: Nat
    height: Nat

data ThinnerOrThinAs : (thinner:SimpleRect) -> (thicker:SimpleRect) -> Type where
    ZeroWidth : {y1:Nat} -> (thicker: SimpleRect) -> ThinnerOrThinAs (MkSimpleRect Z y1) thicker
    IfThinnerHoldsThenSuccHolds : (ThinnerOrThinAs (MkSimpleRect x1 y1) (MkSimpleRect x2 y2)) -> 
                                    ThinnerOrThinAs (MkSimpleRect (S x1) y1) (MkSimpleRect (S x2) y2)

data ShorterOrShortAs : (shorter:SimpleRect) -> (taller:SimpleRect) -> Type where
    ZeroHeight : {x1:Nat} -> (taller: SimpleRect) -> ShorterOrShortAs (MkSimpleRect x1 Z) taller
    IfShorterHoldsThenSuccHolds : (ShorterOrShortAs (MkSimpleRect x1 y1) (MkSimpleRect x2 y2)) -> 
                                    ShorterOrShortAs (MkSimpleRect x1 (S y1)) (MkSimpleRect x2 (S y2))

-------------------------------------------------------------------------------
--                                 Axioms                                    --
--------------------------------------------------------------------------------


Uninhabited ((MkSimpleRect x y) = (MkSimpleRect (S x) y)) where
    uninhabited Refl impossible

Uninhabited ((MkSimpleRect (S x) y) = (MkSimpleRect x y)) where
    uninhabited Refl impossible

Uninhabited ((MkSimpleRect x y) = (MkSimpleRect x (S y))) where
    uninhabited Refl impossible

Uninhabited ((MkSimpleRect x (S y)) = (MkSimpleRect x y)) where
    uninhabited Refl impossible

--------------------------------------------------------------------------------
--                         Simple helper lemmas                               --
--------------------------------------------------------------------------------

||| If SimpleRects are equal, their heights are equal.
equalRectToEqualHeight: {a: SimpleRect} -> {b: SimpleRect} -> (a = b) -> (height a = height b)
equalRectToEqualHeight Refl = Refl

||| If SimpleRects are equal, their widths are equal.
equalRectToEqualWidth: {a: SimpleRect} -> {b: SimpleRect} -> (a = b) -> (width a = width b)
equalRectToEqualWidth Refl = Refl

||| Add one to the width.
increaseSimpleWidth: SimpleRect -> SimpleRect
increaseSimpleWidth (MkSimpleRect width height) = (MkSimpleRect (S width) height)

||| Increasing the width increases the width :)
increaseWidthIncreases: {a: SimpleRect} -> ((width a) = w) -> ((width (increaseSimpleWidth a)) = S w)
increaseWidthIncreases {a = (MkSimpleRect w k)} Refl = Refl

||| Can't increase a width to zero.
implementation [cantIncreaseWidthToZero] Uninhabited ((increaseSimpleWidth a) = (MkSimpleRect Z y)) where
    uninhabited {a = (MkSimpleRect _ _)} Refl impossible

||| Increasing width preserves equality.
increaseSimpleWidthPreservesEquality: (a: SimpleRect) -> (b: SimpleRect) -> (a=b) -> ((increaseSimpleWidth a) = (increaseSimpleWidth b))
increaseSimpleWidthPreservesEquality b b Refl = Refl

||| Increasing width is injective.
increaseSimpleWidthIsInjective: (a: SimpleRect) -> (b: SimpleRect) -> ((increaseSimpleWidth a) = (increaseSimpleWidth b)) -> (a=b) 
increaseSimpleWidthIsInjective (MkSimpleRect width height) (MkSimpleRect width height) Refl = Refl

||| Add one to the height.
increaseSimpleHeight: SimpleRect -> SimpleRect
increaseSimpleHeight (MkSimpleRect width height) = (MkSimpleRect width (S height))

||| Increasing the width increases the width :)
increaseHeightIncreases: {a: SimpleRect} -> ((height a) = h) -> ((height (increaseSimpleHeight a)) = S h)
increaseHeightIncreases {a = (MkSimpleRect w k)} Refl = Refl

||| Can't increase a width to zero.
implementation [cantIncreaseHeightToZero] Uninhabited ((increaseSimpleHeight a) = (MkSimpleRect x Z)) where
    uninhabited {a = (MkSimpleRect _ _)} Refl impossible

||| Increasing height preserves equality.
increaseSimpleHeightPreservesEquality: (a: SimpleRect) -> (b: SimpleRect) -> (a=b) -> ((increaseSimpleHeight a) = (increaseSimpleHeight b))
increaseSimpleHeightPreservesEquality b b Refl = Refl

||| Increasing height is injective.
increaseSimpleHeightIsInjective: (a: SimpleRect) -> (b: SimpleRect) -> ((increaseSimpleHeight a) = (increaseSimpleHeight b)) -> (a=b) 
increaseSimpleHeightIsInjective (MkSimpleRect width height) (MkSimpleRect width height) Refl = Refl


----------------------------------------------------------------------------------
--                                   Equality                                   --
----------------------------------------------------------------------------------

||| Equality for simple rects is trivial - if they're the same size, they're the same rect.
Eq (SimpleRect) where
    (==) (MkSimpleRect x1 y1) (MkSimpleRect x2 y2) = (x1 == x2) && (y1 == y2)

h : (contraH : (height1 = height2) -> Void) -> (pfW : width1 = width2) -> (MkSimpleRect width1 height1 = MkSimpleRect width2 height2) -> Void
h contraH pfW prf = contraH (equalRectToEqualHeight prf)

||| DecidableEquality for SimpleRects is a bit tricker but still pretty simple - it's a matter of prop equality of the construtor arguments.
DecEq (SimpleRect) where
  decEq (MkSimpleRect width1 height1) (MkSimpleRect width2 height2) = case decEq width1 width2 of
                                                                           Yes pfW => case decEq height1 height2 of
                                                                                            Yes pfH => Yes (rewrite pfW in (rewrite pfH in Refl))
                                                                                            No contraH => No (\prf => contraH (equalRectToEqualHeight prf))
                                                                           No contraW => No (\prf => contraW (equalRectToEqualWidth prf))

                                                                           