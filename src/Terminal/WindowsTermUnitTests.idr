module Main

import WinTerm
import IO


main : IO ()
main = do createWindow
          drawAt 5 5 'a'
          drawAt 5 6 'b'
          getLine
          drawAt 5 7 'c'