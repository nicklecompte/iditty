module Terminal.TerminalBase

import Data.Vect
import DataTypes
import Image
import Rectangles

||| An interface representing a terminal window.
||| @ technology a type representing the technology (Windows terminal, bash, SDL, JavaScript)
||| @ graphicsType e.g. Char, (Char,Color), SDL tile
||| @ boundingRect the bounding rectangle of the terminal window
public export
interface TerminalWindow technology graphicsType (boundingRect: Rectangle xsize ysize) where
    ||| Somewhat slow way to print a specific character within the terminal window.
    ||| We use (0,0) as the bottom LHS corner.
    PrintCharacter : (x:Fin xsize) -> (y:Fin ysize) -> graphicsType-> IO()
    ||| Send a RectangularPicture to be outputted to the terminal. 
    PrintPicture : RectangularPicture boundingRect graphicsType -> IO()
    PressKey : IO() -> Char
    ReleaseKey : IO ()
    ClearScreen : IO()