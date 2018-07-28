module Terminal.Image

import Data.Vect
import DataTypes
import Rectangles

data AreaBorderComponent =
    HorizontalWall
    | VerticalWall
    | ULHCorner
    | BLHCorner
    | URHCorner
    | BRHCorner
    | TJunctionDown
    | TJunctionLeft
    | TJunctionRight
    | TJunctionUp
    | FourWayJunction

interface RectangularBorder a where
    Mapping : AreaBorderComponent -> a



-- data AreaBorderType = 
--     Dashes
--     | DoubleDashes
--    | Custom of 

interface RectangularArea a (x:Nat) (y:Nat) where
    GetRectangle : Rectangle x y --((x,y):(Nat,Nat) ** Rectangle (x,y))

singleDashesMapping : AreaBorderComponent -> Char
singleDashesMapping HorizontalWall = '─'
singleDashesMapping VerticalWall = '│'
singleDashesMapping URHCorner = '┐'
singleDashesMapping BLHCorner = '└'
singleDashesMapping ULHCorner = '┌'
singleDashesMapping BRHCorner = '┘'
singleDashesMapping TJunctionDown = '┬'
singleDashesMapping TJunctionLeft = '┤'
singleDashesMapping TJunctionRight = '├'
singleDashesMapping TJunctionUp = '┴'
singleDashesMapping FourWayJunction = '┼'

--RectangularArea

public export
data WordWrapOptions =
    SplitWordUnvarnished
    | SplitWordWithHyphen
    | SplitWordWithCustomChar Char
    | DontSplitWords

public export
record TextBox (x:Nat) (y:Nat) where
    constructor CreateTextBox
    boundingRect : Rectangle x y
    content : LengthLimitedString (x*y)
    wordWrap: WordWrapOptions

public export
data ScrollingTextBox : (boundingRect : Rectangle x y) -> (text: String) -> Type

public export
data MenuListOptions =
    Unlabelled
    | Numeric
    | AlphabeticalUpper
    | AlphabeticalLower
    | RomanUpper
    | RomanLower    

public export
data RectangularPictureLayer : (boundingRect: Rectangle x y) -> graphicsType -> Type where
    Empty : RectangularPictureLayer boundingRect graphicsType

public export
data RectangularPicture : (boundingRect: Rectangle x y) -> graphicsType -> Type where
    Base : RectangularPictureLayer boundingRect graphicsType -> RectangularPicture boundingRect graphicsType
    Layered : {smallerRect: (Rectangle x1 y1)} ->
              {auto pfx1: LTE x1 x} -> 
              {auto pfy1 : LTE y1 y} -> 
              Coordinate (x-x1) (y-y1) -> 
              RectangularPictureLayer smallerRect graphicsType ->
              RectangularPicture boundingRect graphicsType -> 
              RectangularPicture boundingRect graphicsType