module Common.TwoDArray

import Data.Vect

interface I_2DBoundedData ty where
    x: ty -> Nat
    y: ty -> Nat

interface I_2DBoundedData ty => ITwoDArray ty where
    Update: (base:ty) -> (x1:Nat) -> (y1:Nat) -> (pfx: LTE x1 (x base)) -> (pfy: LTE y1 (y base)) -> ty
    Empty : ty

-- data TwoDArray : Type -> (x:Nat) -> (y:Nat) -> Type where
--     Empty : (ty:Type) -> (x:Nat) -> (y:Nat) -> TwoDArray ty x y
--     Update : TwoDArray ty x y -> (x1:Nat) -> (y1:Nat) -> ty -> {auto pfx: LTE x1 x} -> {auto pfy : LTE y1 y} -> TwoDArray ty x y
--     FromVect : Vect y (Vect x a) -> TwoDArray a x y
