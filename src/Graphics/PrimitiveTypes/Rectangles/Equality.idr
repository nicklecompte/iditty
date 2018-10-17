module Graphics.PrimitiveTypes.Rectangles.Equality

import Graphics.PrimitiveTypes.Rectangles.SimpleRects
import Graphics.PrimitiveTypes.Rectangles.Rectangles
import Graphics.PrimitiveTypes.Rectangles.SumRectComparison

%access public export
%default total

||| Boolean / structural equality for Rectangles.
||| The rules here are:
||| 1) SingleRects are always equal to each other (provided they are the same type)
||| 2) SumRects and SingleRects are never equal to each other.
||| 3) SumRects are equal iff their constituent parts are equal - this means they must be EqualSizedSumRects in particular.
Eq (Rectangle a) where                        
    (==) (SingleRect a) (SingleRect a) = True
    (==) (SingleRect _) (HorizontalSum _ _) = False
    (==) (SingleRect _) (VerticalSum _ _) = False
    (==) (HorizontalSum _ _) (SingleRect _) = False
    (==) (VerticalSum _ _) (SingleRect _) = False  
    (==) (VerticalSum _ _) (HorizontalSum _ _) = False
    (==) (HorizontalSum _ _) (VerticalSum _ _) = False
    (==) (VerticalSum a b) (VerticalSum c d) = ?eqHole1 -- (a == c) && (b == d)
    (==) (HorizontalSum a b) (HorizontalSum c d) = ?eqHole2 -- (a == c) && (b == d)

-- ----------------------------------------------------------------------------
-- --                           Decidable equality                           --            
-- ----------------------------------------------------------------------------

-- ||| If two SumRects are not equal sized, then they aren't equal.
-- notEqualSumRectContra : 
--     (notEqualSizedSumRects : 
--         EqualSizedSumRects 
--             (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) 
--             (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) 
--         -> Void) -> 
--     (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1 
--         = SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2
--     ) 
--     -> Void
-- notEqualSumRectContra notEqualSizedSumRects equalSumRects = 
--     notEqualSizedSumRects (equalSumRectsAreEqualSized equalSumRects)

-- ||| If two SumRects are equal, their constituent Rectangles are equal
-- sumRectPartEqualityLemma:
--     {lowerLHS1: Rectangle ll} -> {lowerLHS2: Rectangle ll} ->
--     {lowerRHS1: Rectangle lr} -> {lowerRHS2: Rectangle lr} ->
--     {upperLHS1: Rectangle ul} -> {upperLHS2: Rectangle ul} ->
--     {upperRHS1: Rectangle ur} -> {upperRHS2: Rectangle ur} ->
--     ((SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) =
--      (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2) 
--     ) ->
--         ((lowerLHS1=lowerLHS2),(lowerRHS1=lowerRHS2),(upperLHS1=upperLHS2),(upperRHS1=upperRHS2))
-- sumRectPartEqualityLemma Refl = (Refl,Refl,Refl,Refl)

-- noHolellhs : 
--     {lowerLHS1: Rectangle ll} -> {lowerLHS2: Rectangle ll} ->
--     {lowerRHS1: Rectangle lr} -> {lowerRHS2: Rectangle lr} ->
--     {upperLHS1: Rectangle ul} -> {upperLHS2: Rectangle ul} ->
--     {upperRHS1: Rectangle ur} -> {upperRHS2: Rectangle ur} ->    
--     (llhsContra : lowerLHS1 = lowerLHS2 -> Void) -> 
--     (sumRectEq : 
--         (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) =
--         (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2)) -> 
--     Void
-- noHolellhs {lowerLHS1} {lowerLHS2} llhsContra sumRectEq =
--     let (pfLL,_,_,_) = sumRectPartEqualityLemma {lowerLHS1} {lowerLHS2} sumRectEq in
--         llhsContra pfLL


-- noHolelrhs : 
--     {lowerLHS1: Rectangle ll} -> {lowerLHS2: Rectangle ll} ->
--     {lowerRHS1: Rectangle lr} -> {lowerRHS2: Rectangle lr} ->
--     {upperLHS1: Rectangle ul} -> {upperLHS2: Rectangle ul} ->
--     {upperRHS1: Rectangle ur} -> {upperRHS2: Rectangle ur} ->    
--     (lrhsContra : lowerRHS1 = lowerRHS2 -> Void) -> 
--     (sumRectEq : 
--         (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) =
--         (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2)) -> 
--     Void
-- noHolelrhs {lowerRHS1} {lowerRHS2} lrhsContra sumRectEq =
--     let (_,pfLR,_,_) = sumRectPartEqualityLemma {lowerRHS1} {lowerRHS2} sumRectEq in
--         lrhsContra pfLR   

-- noHoleulhs : 
--     {lowerLHS1: Rectangle ll} -> {lowerLHS2: Rectangle ll} ->
--     {lowerRHS1: Rectangle lr} -> {lowerRHS2: Rectangle lr} ->
--     {upperLHS1: Rectangle ul} -> {upperLHS2: Rectangle ul} ->
--     {upperRHS1: Rectangle ur} -> {upperRHS2: Rectangle ur} ->    
--     (ulhsContra : upperLHS1 = upperLHS2 -> Void) -> 
--     (sumRectEq : 
--         (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) =
--         (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2)) -> 
--     Void
-- noHoleulhs {upperLHS1} {upperLHS2} ulhsContra sumRectEq =
--     let (_,_,pfUL,_) = sumRectPartEqualityLemma {upperLHS1} {upperLHS2} sumRectEq in
--         ulhsContra pfUL
    
    
-- noHoleurhs : 
--     {lowerLHS1: Rectangle ll} -> {lowerLHS2: Rectangle ll} ->
--     {lowerRHS1: Rectangle lr} -> {lowerRHS2: Rectangle lr} ->
--     {upperLHS1: Rectangle ul} -> {upperLHS2: Rectangle ul} ->
--     {upperRHS1: Rectangle ur} -> {upperRHS2: Rectangle ur} ->    
--     (urhsContra : upperRHS1 = upperRHS2 -> Void) -> 
--     (sumRectEq : 
--         (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 pfxLow1 pfxHigh1 pfyLeft1 pfyRight1) =
--         (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 pfxLow2 pfxHigh2 pfyLeft2 pfyRight2)) -> 
--     Void
-- noHoleurhs {upperRHS1} {upperRHS2} urhsContra sumRectEq =
--     let (_,_,_,pfUR) = sumRectPartEqualityLemma {upperRHS1} {upperRHS2} sumRectEq in
--         urhsContra pfUR   

-- DecEq (Rectangle a) where
--     decEq (SingleRect a) (SingleRect a) = Yes Refl
--     decEq (SingleRect _) (SumRect _ _ _ _ _ _ _ _) = No absurd
--     decEq (SumRect _ _ _ _ _ _ _ _) (SingleRect _) = No absurd
--     decEq 
--         (SumRect 
--             lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} 
--             {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) 
--         (SumRect 
--             lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} 
--             {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2}) =
--         case decEqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2}) of
--             Yes eqSizedSumRects =>
--                 let (pfLlhs,pfLrhs,pfUlhs,pfUrhs) = getSameSizeProofsEqSizedSumRect eqSizedSumRects in
--                     let (lowerLHS1', lowerRHS1',upperLHS1',upperRHS1') = (replace pfLlhs lowerLHS1, replace pfLrhs lowerRHS1, replace pfUlhs upperLHS1, replace pfUrhs upperRHS1) in
--                         case decEq lowerLHS1' lowerLHS2 of
--                             Yes llhsEqual =>
--                                 case decEq lowerRHS1' lowerRHS2 of
--                                     Yes lrhsEqual =>
--                                         case decEq upperLHS1' upperLHS2 of
--                                             Yes ulhsEqual => case decEq upperRHS1' upperRHS2 of
--                                                 Yes urhsEqual => Yes ?yesHole
--                                                 No urhsContra => ?a4 --No (\sumRectEq => urhsContra (equalSumRectsHaveEqualURHS sumRectEq))
--                                             No ulhsContra => ?a3 -- No (\sumRectEq => ulhsContra (equalSumRectsHaveEqualULHS sumRectEq))
--                                     No lrhsContra => ?a2 --No (\sumRectEq => lrhsContra (equalSumRectsHaveEqualLRHS sumRectEq))
--                             No llhsContra => No ?a5 --(\sumRectEq => noHolellhs {lowerLHS1=lowerLHS1'} {lowerLHS2} llhsContra sumRectEq)
--             No notEqualSumRects => No (notEqualSumRectContra notEqualSumRects)
