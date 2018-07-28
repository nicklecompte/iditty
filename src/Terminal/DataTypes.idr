module Terminal.DataTypes

import Data.Vect

public export
record Coordinate (xsize:Nat) (ysize:Nat) where
    constructor MkCoord
    x : Fin xsize
    y : Fin ysize

||| A string constrained to be a maximum length. Useful for textboxes to guarantee things don't bleed over.
public export
data LengthLimitedString : (lengthMax: Nat) -> Type where
    Empty: LengthLimitedString Z
    FromVect: (Vect x Char) -> {auto pf: LTE x y} -> LengthLimitedString y
