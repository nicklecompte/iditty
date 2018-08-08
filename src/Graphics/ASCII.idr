module Graphics.ASCII

import Graphics.PrimitiveTypes.Rectangles
import Graphics.PrimitiveTypes.RectangleBorders


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