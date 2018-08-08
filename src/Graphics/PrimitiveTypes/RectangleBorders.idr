module Graphics.PrimitiveTypes.RectangleBorders

import Graphics.PrimitiveTypes.Rectangles

%access public export

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