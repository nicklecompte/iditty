module Graphics.PrimitiveTypes.SimpleRects

import Decidable.Order
import Common.ArithmeticHelpers

%access public export
%default total

--------------------------------------------------------------------------------
--                                 Definitions                                --
--------------------------------------------------------------------------------

||| Really just Nat*Nat, but given a more descriptive name so I don't get confused via overutilization of primitives. 
||| Smarter devs may have different opinions :)
record SimpleRectangle where
  constructor MkRect
  width: Nat
  height: Nat


--- name hints
% name SimpleRectangle rect1, rect2, rect3, rect4

----------------------------------------------------------------------------------
--                                  Uninhabited                                 --
----------------------------------------------------------------------------------



----------------------------------------------------------------------------------
--                                   Comparison                                 --
----------------------------------------------------------------------------------

||| Lemma stating that rect1 = rect2 ==> (x rect1) = (x rect2)
equalSimpleRectsMustHaveEqualWidth : {rect1: SimpleRectangle} -> {rect2: SimpleRectangle} -> (pfRect: rect1 = rect2) -> ((width rect1) = (width rect2))
equalSimpleRectsMustHaveEqualWidth {rect1 = (MkRect k j)} {rect2 = (MkRect k j)} Refl = Refl

||| Lemma stating that (x1 /= x2) -> (MkRect x1 _) /= (MkRect x2 _)
equalSimpleRectsMustHaveEqualHeight : {rect1: SimpleRectangle} -> {rect2: SimpleRectangle} -> (pfRect: rect1 = rect2) -> ((height rect1) = (height rect2))
equalSimpleRectsMustHaveEqualHeight {rect1 = (MkRect k j)} {rect2 = (MkRect k j)} Refl = Refl

Eq (SimpleRectangle) where
  (==) rect1 rect2 = ((width rect1) == (width rect2)) && ((height rect1) == (height rect2))

DecEq (SimpleRectangle) where
  decEq (MkRect x1 y1) (MkRect x2 y2) = case decEq x1 x2 of
                                          Yes pfx => case decEq y1 y2 of
                                                      Yes pfy => Yes (rewrite pfx in (rewrite pfy in Refl))
                                                      No contray => No (\rectEquality => (contray (equalSimpleRectsMustHaveEqualHeight rectEquality)))
                                          No contrax => No (\rectEquality => (contrax (equalSimpleRectsMustHaveEqualWidth rectEquality))) -- decEq rect1 rect2 = case decEq (x rect1) (x rect2) of

data StrictlyContainedRectangle: (smaller: SimpleRectangle) -> (bigger: SimpleRectangle) -> Type where
  IsContained: (rect1: SimpleRectangle) -> (rect2: SimpleRectangle) -> {pfx: LT (width rect1) (width rect2)} -> {pfy: LT (height rect1) (height rect2)} -> StrictlyContainedRectangle rect1 rect2

Uninhabited (StrictlyContainedRectangle a a) where
  uninhabited (IsContained a a {pfx} {pfy}) = absurd pfx -- using Uninhabited (LT a a)

using (a: SimpleRectangle)
  using (b: SimpleRectangle)
    using (containment: StrictlyContainedRectangle a b)
      implementation [strictContainedNotSymmetric] Uninhabited (StrictlyContainedRectangle b a) where
        uninhabited x = ?h

data SimpleRectanglePartialOrdering: (smaller: SimpleRectangle) -> (bigger: SimpleRectangle) -> Type where
  Equal: (rect: SimpleRectangle) -> SimpleRectanglePartialOrdering rect rect
  Contained: StrictlyContainedRectangle a b -> SimpleRectanglePartialOrdering a b

Preorder SimpleRectangle SimpleRectanglePartialOrdering where
  transitive r r r (Equal r) (Equal r) = Equal r
  transitive r r r1 (Equal r) (Contained (IsContained r r1 {pfx} {pfy})) = (Contained (IsContained r r1 {pfx} {pfy}))
  transitive r r1 r1 (Contained x) (Equal r1) = Contained x
  transitive r1 r2 r3 (Contained (IsContained r1 r2 {pfx=pfx12} {pfy=pfy12})) (Contained (IsContained r2 r3 {pfx=pfx23} {pfy=pfy23})) =
    Contained (IsContained r1 r3 {pfx = ltTransitive pfx12 pfx23} {pfy = ltTransitive pfy12 pfy23})
  reflexive a = Equal a

Poset SimpleRectangle SimpleRectanglePartialOrdering where
  antisymmetric b b (Equal b) (Equal b) = Refl
  antisymmetric b b (Equal b) (Contained x) = Refl
  antisymmetric a a (Contained x) (Equal a) = Refl
  antisymmetric a b (Contained (IsContained a b {pfx=pfx1})) (Contained (IsContained b a {pfx=pfx2})) = absurd (ltGoesOneWay pfx1 pfx2)


