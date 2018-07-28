module Terminal.AsciiGraphics

import Rectangles

-- buildRectangleRowString: (x:Nat) -> V
-- buildRectangleRowString Z = "+"
-- buildRectangleRowString (S k) = buildRectangleRowHelper Z (S k) where
--                                     buildRectangleRowHelper (current:)

-- showHelper : (Rectangle (x,y)) -> String -> String                 
-- showHelper {x = Z} {y = Z} (SingleRect Z Z) builder = builder ++ "+"
-- showHelper {x = Z} {y = (S k)} (SingleRect Z (S k)) builder = builder ++ ?h
-- showHelper {x = (S k)} {y = y} (SingleRect (S k) y) builder = ?showHelper_rhs_4
-- showHelper {x = (x1 + x2)} {y = (y1 + y2)} (SumRect lhsLow rhsLow lhsHigh rhsHigh) builder = ?showHelper_rhs_2

-- Show (Rectangle (x,y)) where                
--   show {x} {y} rect = ?showRhs1 

--   showPrec d x = ?Show_rhs_2
