module Iditty.Common.ArithmeticHelpers

%access public export
%default total
{-
Some helper lemmas for Nat that aren't in Prelude.
-}

||| `LT` is transitive
ltTransitive : LT n m -> LT m p -> LT n p
ltTransitive (LTESucc LTEZero) (LTESucc (LTESucc x)) = LTESucc (LTEZero)
ltTransitive (LTESucc (LTESucc x)) (LTESucc (LTESucc y)) = LTESucc (lteTransitive (LTESucc x) (lteSuccRight y))

successorNotLessThanSelf: {x: Nat} -> (LTE (S x) x ) -> Void
successorNotLessThanSelf {x = Z} LTEZero impossible
successorNotLessThanSelf {x = Z} (LTESucc _) impossible
successorNotLessThanSelf {x = (S k)} (LTESucc x) = successorNotLessThanSelf {x=k} x

||| LT is not reflexive.
Uninhabited (LT a a) where
  uninhabited (LTESucc x) = successorNotLessThanSelf x

||| LT is not symmetric.
ltGoesOneWay: {a:Nat} -> {b:Nat} -> (LT a b) -> (LT b a) -> Void
ltGoesOneWay {a = Z} {b = Z} LTEZero _ impossible
ltGoesOneWay {a = Z} {b = Z} (LTESucc _) _ impossible
ltGoesOneWay {a = Z} {b = (S _)} _ LTEZero impossible
ltGoesOneWay {a = Z} {b = (S _)} _ (LTESucc _) impossible
ltGoesOneWay {a = (S k)} {b = (S j)} (LTESucc x) (LTESucc y) = ltGoesOneWay {a=k} {b=j} x y


||| If a <= b, then b = a + (b - a)
negativeCancellationLemma: (left: Nat) -> (right: Nat) -> (gtPf: LTE left right) -> right = plus left (minus right left)
negativeCancellationLemma Z Z _ = Refl
negativeCancellationLemma Z (S k) _ = Refl
negativeCancellationLemma (S k) Z (gtPf) = absurd gtPf
negativeCancellationLemma (S k) (S j) (gtPf) =  rewrite (negativeCancellationLemma k j (fromLteSucc gtPf) ) in Refl


