module Graphics.PrimitiveTypes.SimpleRects

import Decidable.Order

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
% name SimpleRectangle rect1, rect2, rect3, rectToRectangleRow_rhs_4

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
  --                       Yes pfx => case decEq (y rect1) (y rect2) of
  --                                   Yes pfy => Yes Refl
  --                                   No contraY => No ?noYH
  --                       No contraX => No ?noH

data SimpleRectanglePartialOrdering: (smaller: SimpleRectangle) -> (bigger: SimpleRectangle) -> Type where
  Equal: SimpleRectanglePartialOrdering rect rect
  Contained: {pfx: LT x1 x2} -> {pfy: LT y1 y2} -> SimpleRectanglePartialOrdering (MkRect x1 y1) (MkRect x2 y2)

||| `LT` is transitive
ltTransitive : LT n m -> LT m p -> LT n p
ltTransitive (LTESucc LTEZero) (LTESucc (LTESucc x)) = LTESucc (LTEZero)
ltTransitive (LTESucc (LTESucc x)) (LTESucc (LTESucc y)) = LTESucc (lteTransitive (LTESucc x) (lteSuccRight y))

Preorder SimpleRectangle SimpleRectanglePartialOrdering where
  transitive (MkRect x2 y2) (MkRect x2 y2) (MkRect x2 y2) Equal Equal = Equal
  transitive (MkRect x2 y2) (MkRect x2 y2) (MkRect x3 y3) Equal (Contained {pfx} {pfy}) = (Contained {pfx} {pfy})
  transitive (MkRect x1 y1) (MkRect x2 y2) (MkRect x2 y2) (Contained {pfx} {pfy}) Equal = (Contained {pfx} {pfy})
  transitive (MkRect x1 y1) (MkRect x2 y2) (MkRect x3 y3) (Contained {pfx=pfx12} {pfy=pfy12}) (Contained {pfx=pfx23} {pfy=pfy23}) = Contained {pfx = (ltTransitive pfx12 pfx23)} {pfy = (ltTransitive pfy12 pfy23)}
  reflexive a = Equal

  -- transitive (MkRect k j) (MkRect k j) (MkRect k j) Equal Equal = Equal
  -- transitive (MkRect k j) (MkRect k j) (MkRect i n) Equal (Contained {pfx} {pfy}) = (Contained {pfx} {pfy}) 
  -- transitive (MkRect width height) (MkRect k j) (MkRect k j) (Contained {pfx} {pfy}) Equal = (Contained {pfx} {pfy})
  -- transitive (MkRect width height) (MkRect k j) (MkRect i n) (Contained {pfx=pfx1} {pfy=pfy1}) (Contained {pfx=pfx2} {pfy=pfy2}) = 
  --   Contained {pfx = (lteTransitive pfx1 pfx2)} {pfy = (lteTransitive pfy1 pfy2)}
--  reflexive a = Equal

-- Poset SimpleRectangle SimpleRectanglePartialOrdering where
--   antisymmetric (MkRect x2 y2) (MkRect x2 y2) Equal Equal = Refl
--   antisymmetric (MkRect x2 y2) (MkRect x2 y2) Equal Contained = ?Poset_rhs_4
--   antisymmetric (MkRect x1 y1) (MkRect x1 y1) Contained Equal = ?Poset_rhs_2
--   antisymmetric (MkRect x1 y1) (MkRect x2 y2) Contained Contained = ?Poset_rhs_5

