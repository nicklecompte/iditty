module Graphics.PrimitiveTypes.Rectangles.Equality

import Graphics.PrimitiveTypes.Rectangles.SimpleRects
import Graphics.PrimitiveTypes.Rectangles.Rectangles
import Graphics.PrimitiveTypes.Rectangles.SumRectComparison

%access public export
%default total

Eq (Rectangle a) where
    (==) (SingleRect a) (SingleRect a) = True
    (==) (SingleRect _) (SumRect _ _ _ _) = False
    (==) (SumRect lowerLHS lowerRhs upperLHS upperRHS) (SingleRect _) = False
    (==) (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2}) =
        case (decEqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2})) of
            Yes eqSizedSumRects =>
                let (pfLlhs,pfLrhs,pfUlhs,pfUrhs) = getSameSizeProofsEqSizedSumRect eqSizedSumRects in
                    ((replace pfLlhs lowerLHS1) == lowerLHS2) && ((replace pfLrhs lowerRHS1) == lowerRHS2) && ((replace pfUlhs upperLHS1) == upperLHS2) && ((replace pfUrhs upperRHS1) == upperRHS2)
            No _ => False


notEqualSumRectContra : (notEqualSizedSumRects : EqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2) -> Void) -> (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 = SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2) -> Void
notEqualSumRectContra notEqualSizedSumRects equalSumRects = notEqualSizedSumRects (equalSumRectsAreEqualSized equalSumRects)


noHolellhs : {lowerLHS1 : Rectangle rlLHS} -> {lowerLHS2 : Rectangle rlRHS1} ->
    (pfLlhs : rlLHS = rlLHS1) -> 
    (llhsContra : (replace pfLlhs lowerLHS1 = lowerLHS2) -> Void) -> 
    (eqSizedSumRects : EqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2)) -> 
    (sumRectEq : SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 = SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2) -> 
    Void
noHolellhs {lowerLHS1} {lowerLHS2} pfLlhs llhsContra eqSizedSumRects sumRectEq = 
    let pfEqualLLHS = (rewrite pfLlhs in (equalSumRectsHaveEqualLLHS sumRectEq)) in
        ?noHolellhs_rhs 

DecEq (Rectangle a) where
    decEq (SingleRect a) (SingleRect a) = Yes Refl
    decEq (SingleRect _) (SumRect _ _ _ _) = No absurd
    decEq (SumRect lowerLHS lowerRhs upperLHS upperRHS) (SingleRect _) = No absurd
    decEq (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2}) =
        case decEqualSizedSumRects (SumRect lowerLHS1 lowerRHS1 upperLHS1 upperRHS1 {x} {y} {pfxLow=pfxLow1} {pfxHigh=pfxHigh1} {pfyLeft=pfyLeft1} {pfyRight=pfyRight1}) (SumRect lowerLHS2 lowerRHS2 upperLHS2 upperRHS2 {x} {y} {pfxLow=pfxLow2} {pfxHigh=pfxHigh2} {pfyLeft=pfyLeft2} {pfyRight=pfyRight2}) of
            Yes eqSizedSumRects =>
                let (pfLlhs,pfLrhs,pfUlhs,pfUrhs) = getSameSizeProofsEqSizedSumRect eqSizedSumRects in
                    case decEq (replace pfLlhs lowerLHS1) lowerLHS2 of
                        Yes llhsEqual =>
                            case decEq (replace pfLrhs lowerRHS1) lowerRHS2 of
                                Yes lrhsEqual =>
                                    case decEq (replace pfUlhs upperLHS1) upperLHS2 of
                                        Yes ulhsEqual => case decEq (replace pfUrhs upperRHS1) upperRHS2 of
                                            Yes urhsEqual => Yes ?yesHole
                                            No urhsContra => ?a4 --No (\sumRectEq => urhsContra (equalSumRectsHaveEqualURHS sumRectEq))
                                        No ulhsContra => ?a3 -- No (\sumRectEq => ulhsContra (equalSumRectsHaveEqualULHS sumRectEq))
                                No lrhsContra => ?a2 --No (\sumRectEq => lrhsContra (equalSumRectsHaveEqualLRHS sumRectEq))
                        No llhsContra => No (\sumRectEq => noHolellhs pfLlhs llhsContra eqSizedSumRects sumRectEq)
                                                -- llhsContra ((equalSumRectsHaveEqualLLHS 
                                                --             (replaceLlhsSumrect (sumRectEq))))) --(noHolellhs {lowerLHS1 = (replace pfLlhs lowerLHS1)} {lowerLHS2} llhsContra)
            No notEqualSumRects => No (notEqualSumRectContra notEqualSumRects)
