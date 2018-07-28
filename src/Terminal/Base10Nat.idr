module Terminal.Base10Nat

%access public export
%default total

data ZeroDigit = Zero

data NonZeroDigit = 
    One |
    ||| (S (S Z))
    Two |
    ||| (S (S (S Z)))
    Three | 
    ||| and so on :)
    Four |
    Five |
    Six |
    Seven |
    Eight |
    Nine

data NatBase10 : Type where
    SingleDigit : (Either ZeroDigit NonZeroDigit) -> NatBase10
    Multidigit : (firstDigit: NonZeroDigit) -> (numberOfZerosAfterFirstDigit: NatBase10) -> (remainingDigitsAfterZeros: NatBase10) -> NatBase10

toString : NatBase10 -> Stsing
toInt (SingleDigit (Left Zero)) = "0"
toInt (SingleDigit (Right One)) = "1"
toInt (SingleDigit (Right Two)) = "2"
toInt (SingleDigit (Right Three)) = "3"
toInt (SingleDigit (Right Four)) = "4"
toInt (SingleDigit (Right Five)) = "5"
toInt (SingleDigit (Right Six)) = "6"
toInt (SingleDigit (Right Seven)) = "7"
toInt (SingleDigit (Right Eight)) = "8"
toInt (SingleDigit (Right Nine)) = "9"
--toInt (Multidigit firstDigit numberOfZerosAfterFirstDigit remainingDigitsAfterZeros) = (toString (SingleDigit (Right firstDigit)))

-- appendNatBase10 : NatBase10 -> NatBase10 -> NatBase10
-- appendNatBase10 (SingleDigit (Left Zero)) y = y
-- appendNatBase10 (SingleDigit (Right r)) y = Multidigit r y
-- appendNatBase10 (Multidigit x (SingleDigit (Left Zero))) y = Multidigit x  (appendNatBase10 (SingleDigit (Left Zero)) y)
-- appendNatBase10 (Multidigit x (SingleDigit (Right r))) y = Multidigit x (appendNatBase10 (SingleDigit (Right r)) y)
-- appendNatBase10 (Multidigit x (Multidigit z w)) y = Multidigit x (appendNatBase10 (Multidigit z w) y)

-- getLastDigit : NatBase10 -> Either ZeroDigit NonZeroDigit
-- getLastDigit (SingleDigit x) = x
-- getLastDigit (Multidigit x y) = getLastDigit y

-- data IsLastDigitNine : NatBase10 -> Type where
--     NineItself : IsLastDigitNine (SingleDigit (Right Nine))
--     TwoDigit : IsLastDigitNine (Multidigit x (SingleDigit (Right Nine)))


-- -- data IsNatBase10Succ : NatBase10 -> Type where
-- --     OneIsSucc : IsNatBase10Succ

-- getSucc : NatBase10 -> NatBase10
-- getSucc (SingleDigit (Left Zero)) = (SingleDigit (Right One))
-- getSucc (SingleDigit (Right One)) = (SingleDigit (Right Two))
-- getSucc (SingleDigit (Right Two)) = (SingleDigit (Right Three))
-- getSucc (SingleDigit (Right Three)) = (SingleDigit (Right Four))
-- getSucc (SingleDigit (Right Four)) = (SingleDigit (Right Five))
-- getSucc (SingleDigit (Right Five)) = (SingleDigit (Right Six))
-- getSucc (SingleDigit (Right Six)) = (SingleDigit (Right Seven))
-- getSucc (SingleDigit (Right Seven)) = (SingleDigit (Right Eight))
-- getSucc (SingleDigit (Right Eight)) = (SingleDigit (Right Nine))
-- getSucc (SingleDigit (Right Nine)) = Multidigit One (SingleDigit (Left Zero))
-- getSucc (Multidigit x y) = ?getSucc_rhs_2

--||| Functionally equivalent to a Nat, but designed to be moderately fast on moderately-sized natural numbers (~ 10^3 in the time to sip a tea, not to brew one)
-- data Base10Nat =
--     ||| Zero. The same as Z in Nat
--     Zero | 
--     ||| S Z
--     One |
--     ||| (S (S Z))
--     Two |
--     ||| (S (S (S Z)))
--     Three | 
--     ||| and so on :)
--     Four |
--     Five |
--     Six |
--     Seven |
--     Eight |
--     Nine |
--     ||| Composing Base10Nats Left-Right. Multidigit Eight Zero = 89. Multidigit (Multidigit One (Multidigit Two Three)) (Multidigit Five Six) is the int 12,356.
--     Multidigit Base10Nat Base10Nat -- |
-- --    ||| Successor function for ordinality/all math/ etc. -
-- --    Succ Base10Nat

-- ||| View for breaking a multidigit Base10Nat into its first (n-1) then last digits
-- data LastBase10NatDigitView : Base10Nat -> Type where
--     ZeroV : LastBase10NatDigitView Zero
--     OneV : LastBase10NatDigitView One
--     TwoV : LastBase10NatDigitView Two
--     ThreeV : LastBase10NatDigitView Three
--     FourV : LastBase10NatDigitView Four
--     FiveV : LastBase10NatDigitView Five
--     SixV : LastBase10NatDigitView Six
--     SevenV : LastBase10NatDigitView Seven
--     EightV : LastBase10NatDigitView Eight
--     NineV : LastBase10NatDigitView Nine
--     MultidigitZero : LastBase10NatDigitView (Multidigit x Zero)
--     MultidigitOne : LastBase10NatDigitView (Multidigit x One)
--     MultidigitTwo : LastBase10NatDigitView (Multidigit x Two)
--     MultidigitThree : LastBase10NatDigitView (Multidigit x Three)
--     MultidigitFour : LastBase10NatDigitView (Multidigit x Four)
--     MultidigitFive : LastBase10NatDigitView (Multidigit x Five)
--     MultidigitSix : LastBase10NatDigitView (Multidigit x Six)
--     MultidigitSeven : LastBase10NatDigitView (Multidigit x Seven)
--     MultidigitEight : LastBase10NatDigitView (Multidigit x Eight)
--     MultidigitNine : LastBase10NatDigitView (Multidigit x Nine)

-- -- lastDigit : (n: Base10Nat) -> (last: Base10Nat)
-- -- lastDigit x = ?h12

-- lastDigitDecomposition : Base10Nat -> (Maybe Base10Nat, Base10Nat)
-- lastDigitDecomposition Zero = (Nothing,Zero)
-- lastDigitDecomposition One = (Nothing,One)
-- lastDigitDecomposition Two = (Nothing,Two)
-- lastDigitDecomposition Three = (Nothing,Three)
-- lastDigitDecomposition Four = (Nothing,Four)
-- lastDigitDecomposition Five = (Nothing,Five)
-- lastDigitDecomposition Six = (Nothing,Six)
-- lastDigitDecomposition Seven = (Nothing,Seven)
-- lastDigitDecomposition Eight = (Nothing,Eight)
-- lastDigitDecomposition Nine = (Nothing,Nine)
-- lastDigitDecomposition (Multidigit x Zero) = (Just x,Zero)
-- lastDigitDecomposition (Multidigit x One) = (Just x,One)
-- lastDigitDecomposition (Multidigit x Two) = (Just x,Two)
-- lastDigitDecomposition (Multidigit x Three) = (Just x,Three)
-- lastDigitDecomposition (Multidigit x Four) = (Just x,Four)
-- lastDigitDecomposition (Multidigit x Five) = (Just x,Five)
-- lastDigitDecomposition (Multidigit x Six) = (Just x,Six)
-- lastDigitDecomposition (Multidigit x Seven) = (Just x,Seven)
-- lastDigitDecomposition (Multidigit x Eight) = (Just x,Eight)
-- lastDigitDecomposition (Multidigit x Nine) = (Just x,Nine)
-- lastDigitDecomposition (Multidigit w (Multidigit x y)) = case lastDigitDecomposition y of
--                                             (Nothing, b) => (Just (Multidigit w x),b)
--                                             (Just a, b) => (Just (Multidigit w (Multidigit x a)),b)

--                                 -- Zero => (Just x,Zero)
--                                 -- One => (Just x,One)
--                                 -- Two => (Just x, Two)
--                                 -- Three => (Just x, Three)
--                                 -- Four => (Just x, Four)
--                                 -- Five => (Just x, Five)
--                                 -- Six => (Just x, Six)
--                                 -- Seven => (Just x, Seven)
--                                 -- Eight => (Just x, Eight)
--                                 -- Nine => (Just x, Nine)
--                                 -- (Multidigit w z) => case lastDigitDecomposition z of
--                                 --                         (Nothing, b) => (Just (Multidigit x w),b)
--                                 --                         (Just a, b) => (Just (Multidigit x (Multidigit w a)),b)


-- ||| Axioms defining which digits are successors of the other
-- data Base10NatDigitSucc : Base10Nat -> Base10Nat -> Type where
--     OneSucc : Base10NatDigitSucc Zero One
--     TwoSucc : Base10NatDigitSucc One Two
--     ThreeSucc : Base10NatDigitSucc Two Three
--     FourSucc : Base10NatDigitSucc Three Four
--     FiveSucc : Base10NatDigitSucc Four Five
--     SixSucc : Base10NatDigitSucc Five Six
--     SevenSucc : Base10NatDigitSucc Six Seven
--     EightSucc : Base10NatDigitSucc Seven Eight
--     NineSucc : Base10NatDigitSucc Eight Nine
--     TenSucc : Base10NatDigitSucc Nine (Multidigit One Zero)
--    Multidigit : 
--    MultidigitSuccNine : Base10NatSucc (Multidigit  Nine) 

    -- 
    -- 
    -- ||| (S (S (S (S Z))))
    -- ||| and so on :)
    -- 
    -- 
-- --------------------------------------------------------------------------------
-- -- Wasteland of Uninhabited (x = y) for all these constructors :(
-- --------------------------------------------------------------------------------
    
-- ------------- Zero --------------

-- Uninhabited (Zero = One) where
--     uninhabited Refl impossible
      
-- Uninhabited (One = Zero) where
--     uninhabited Refl impossible

-- Uninhabited (Zero = Two) where
--     uninhabited Refl impossible
      
-- Uninhabited (Two = Zero) where
--     uninhabited Refl impossible

-- Uninhabited (Zero = Three) where
--     uninhabited Refl impossible
      
-- Uninhabited (Three = Zero) where
--     uninhabited Refl impossible

-- Uninhabited (Zero = Four) where
--     uninhabited Refl impossible
      
-- Uninhabited (Four = Zero) where
--     uninhabited Refl impossible    

-- Uninhabited (Zero = Five) where
--     uninhabited Refl impossible
      
-- Uninhabited (Five = Zero) where
--     uninhabited Refl impossible

-- Uninhabited (Zero = Six) where
--     uninhabited Refl impossible
      
-- Uninhabited (Six = Zero) where
--     uninhabited Refl impossible

-- Uninhabited (Zero = Seven) where
--     uninhabited Refl impossible
      
-- Uninhabited (Seven = Zero) where
--     uninhabited Refl impossible

-- Uninhabited (Zero = Eight) where
--     uninhabited Refl impossible
      
-- Uninhabited (Eight = Zero) where
--     uninhabited Refl impossible    

-- Uninhabited (Zero = Nine) where
--     uninhabited Refl impossible
          
-- Uninhabited (Nine = Zero) where
--     uninhabited Refl impossible    

-- -- Uninhabited (Zero = (Succ n)) where
-- --     uninhabited Refl impossible
          
-- -- Uninhabited ((Succ n) = Zero) where
-- --     uninhabited Refl impossible
    

-- --------- One ---------


-- Uninhabited (One = Two) where
--     uninhabited Refl impossible
      
-- Uninhabited (Two = One) where
--     uninhabited Refl impossible

-- Uninhabited (One = Three) where
--     uninhabited Refl impossible
      
-- Uninhabited (Three = One) where
--     uninhabited Refl impossible

-- Uninhabited (One = Four) where
--     uninhabited Refl impossible
      
-- Uninhabited (Four = One) where
--     uninhabited Refl impossible    

-- Uninhabited (One = Five) where
--     uninhabited Refl impossible
      
-- Uninhabited (Five = One) where
--     uninhabited Refl impossible

-- Uninhabited (One = Six) where
--     uninhabited Refl impossible
      
-- Uninhabited (Six = One) where
--     uninhabited Refl impossible

-- Uninhabited (One = Seven) where
--     uninhabited Refl impossible
      
-- Uninhabited (Seven = One) where
--     uninhabited Refl impossible

-- Uninhabited (One = Eight) where
--     uninhabited Refl impossible
      
-- Uninhabited (Eight = One) where
--     uninhabited Refl impossible    

-- Uninhabited (One = Nine) where
--     uninhabited Refl impossible
          
-- Uninhabited (Nine = One) where
--     uninhabited Refl impossible    


-- ------------- Two ------------    

-- Uninhabited (Two = Three) where
--     uninhabited Refl impossible
      
-- Uninhabited (Three = Two) where
--     uninhabited Refl impossible

-- Uninhabited (Two = Four) where
--     uninhabited Refl impossible
      
-- Uninhabited (Four = Two) where
--     uninhabited Refl impossible    

-- Uninhabited (Two = Five) where
--     uninhabited Refl impossible
      
-- Uninhabited (Five = Two) where
--     uninhabited Refl impossible

-- Uninhabited (Two = Six) where
--     uninhabited Refl impossible
      
-- Uninhabited (Six = Two) where
--     uninhabited Refl impossible

-- Uninhabited (Two = Seven) where
--     uninhabited Refl impossible
      
-- Uninhabited (Seven = Two) where
--     uninhabited Refl impossible

-- Uninhabited (Two = Eight) where
--     uninhabited Refl impossible
      
-- Uninhabited (Eight = Two) where
--     uninhabited Refl impossible    

-- Uninhabited (Two = Nine) where
--     uninhabited Refl impossible
          
-- Uninhabited (Nine = Two) where
--     uninhabited Refl impossible    


-- --------- Three ------------    

-- Uninhabited (Three = Four) where
--     uninhabited Refl impossible
      
-- Uninhabited (Four = Three) where
--     uninhabited Refl impossible    

-- Uninhabited (Three = Five) where
--     uninhabited Refl impossible
      
-- Uninhabited (Five = Three) where
--     uninhabited Refl impossible

-- Uninhabited (Three = Six) where
--     uninhabited Refl impossible
      
-- Uninhabited (Six = Three) where
--     uninhabited Refl impossible

-- Uninhabited (Three = Seven) where
--     uninhabited Refl impossible
      
-- Uninhabited (Seven = Three) where
--     uninhabited Refl impossible

-- Uninhabited (Three = Eight) where
--     uninhabited Refl impossible
      
-- Uninhabited (Eight = Three) where
--     uninhabited Refl impossible    

-- Uninhabited (Three = Nine) where
--     uninhabited Refl impossible
          
-- Uninhabited (Nine = Three) where
--     uninhabited Refl impossible    



-- ---------------- Four --------------

-- Uninhabited (Four = Five) where
--     uninhabited Refl impossible
      
-- Uninhabited (Five = Four) where
--     uninhabited Refl impossible

-- Uninhabited (Four = Six) where
--     uninhabited Refl impossible
      
-- Uninhabited (Six = Four) where
--     uninhabited Refl impossible

-- Uninhabited (Four = Seven) where
--     uninhabited Refl impossible
      
-- Uninhabited (Seven = Four) where
--     uninhabited Refl impossible

-- Uninhabited (Four = Eight) where
--     uninhabited Refl impossible
      
-- Uninhabited (Eight = Four) where
--     uninhabited Refl impossible    

-- Uninhabited (Four = Nine) where
--     uninhabited Refl impossible
          
-- Uninhabited (Nine = Four) where
--     uninhabited Refl impossible    



-- ------------------ Five --------------    

-- Uninhabited (Five = Six) where
--     uninhabited Refl impossible
      
-- Uninhabited (Six = Five) where
--     uninhabited Refl impossible

-- Uninhabited (Five = Seven) where
--     uninhabited Refl impossible
      
-- Uninhabited (Seven = Five) where
--     uninhabited Refl impossible

-- Uninhabited (Five = Eight) where
--     uninhabited Refl impossible
      
-- Uninhabited (Eight = Five) where
--     uninhabited Refl impossible    

-- Uninhabited (Five = Nine) where
--     uninhabited Refl impossible
          
-- Uninhabited (Nine = Five) where
--     uninhabited Refl impossible    



-- ------------ Six -------------

-- Uninhabited (Six = Seven) where
--     uninhabited Refl impossible
      
-- Uninhabited (Seven = Six) where
--     uninhabited Refl impossible

-- Uninhabited (Six = Eight) where
--     uninhabited Refl impossible
      
-- Uninhabited (Eight = Six) where
--     uninhabited Refl impossible    

-- Uninhabited (Six = Nine) where
--     uninhabited Refl impossible
          
-- Uninhabited (Nine = Six) where
--     uninhabited Refl impossible    

-- ------------ Seven -------------

-- Uninhabited (Seven = Eight) where
--     uninhabited Refl impossible
      
-- Uninhabited (Eight = Seven) where
--     uninhabited Refl impossible    

-- Uninhabited (Seven = Nine) where
--     uninhabited Refl impossible
          
-- Uninhabited (Nine = Seven) where
--     uninhabited Refl impossible    


-- ------------ Eight -------------

-- Uninhabited (Eight = Nine) where
--     uninhabited Refl impossible
          
-- Uninhabited (Nine = Eight) where
--     uninhabited Refl impossible        


-- ------ We've already done Nine :) -----

-- ---- Mutlidigit - can't be equal to any of the parameterless constructors ----

-- Uninhabited ((Multidigit _ _) = Zero) where
--     uninhabited Refl impossible
      
-- Uninhabited (Zero = (Multidigit _ _)) where
--     uninhabited Refl impossible

-- Uninhabited ((Multidigit _ _) = One) where
--     uninhabited Refl impossible
      
-- Uninhabited (One = (Multidigit _ _)) where
--     uninhabited Refl impossible

-- Uninhabited ((Multidigit _ _) = Two) where
--     uninhabited Refl impossible
      
-- Uninhabited (Two = (Multidigit _ _)) where
--     uninhabited Refl impossible

-- Uninhabited ((Multidigit _ _) = Three) where
--     uninhabited Refl impossible
      
-- Uninhabited (Three = (Multidigit _ _)) where
--     uninhabited Refl impossible

-- Uninhabited ((Multidigit _ _) = Four) where
--     uninhabited Refl impossible
      
-- Uninhabited (Four = (Multidigit _ _)) where
--     uninhabited Refl impossible    

-- Uninhabited ((Multidigit _ _) = Five) where
--     uninhabited Refl impossible
      
-- Uninhabited (Five = (Multidigit _ _)) where
--     uninhabited Refl impossible

-- Uninhabited ((Multidigit _ _) = Six) where
--     uninhabited Refl impossible
      
-- Uninhabited (Six = (Multidigit _ _)) where
--     uninhabited Refl impossible

-- Uninhabited ((Multidigit _ _) = Seven) where
--     uninhabited Refl impossible
      
-- Uninhabited (Seven = (Multidigit _ _)) where
--     uninhabited Refl impossible

-- Uninhabited ((Multidigit _ _) = Eight) where
--     uninhabited Refl impossible
      
-- Uninhabited (Eight = (Multidigit _ _)) where
--     uninhabited Refl impossible    

-- Uninhabited ((Multidigit _ _) = Nine) where
--     uninhabited Refl impossible
          
-- Uninhabited (Nine = (Multidigit _ _)) where
--     uninhabited Refl impossible    




--------------------------------------------------------------------------------
-- Proof that zero is not the successor of any Base10Nat
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Proofs that the other parameterless constructors of Base10Nat [One,Two,Three...] have unique successors
--------------------------------------------------------------------------------


    -- | Ten
    -- | Eleven
    -- | Twelve
    -- | Thirteen
    -- | Fourteen
    -- | Fifteen
    -- | Sixteen

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------
    
-- Eq Base10Nat where
--   (==) Zero Zero = True
--   (==) One One = True
--   (==) Two Two = True
--   (==) Three Three = True
--   (==) Four Four = True
--   (==) Five Five = True
--   (==) Six Six = True
--   (==) Seven Seven = True
--   (==) Eight Eight = True
--   (==) Nine Nine = True
--   (==) Zero _ = False
--   (==) One _ = False
--   (==) Two _ = False
--   (==) Three _ = False
--   (==) Four _ = False
--   (==) Five _ = False
--   (==) Six _ = False
--   (==) Seven _ = False
--   (==) Eight _ = False
--   (==) Nine _ = False
--   (==) (Multidigit x z) Zero = False
--   (==) (Multidigit x z) One = False
--   (==) (Multidigit x z) Two = False
--   (==) (Multidigit x z) Three = False
--   (==) (Multidigit x z) Four = False
--   (==) (Multidigit x z) Five = False
--   (==) (Multidigit x z) Six = False
--   (==) (Multidigit x z) Seven = False
--   (==) (Multidigit x z) Eight = False
--   (==) (Multidigit x z) Nine = False
--   (==) (Multidigit x z) (Multidigit y w) = (x == y) && (z == w)
-- --   (==) (Succ n ) x = ?h1
-- --   (==) x (Succ n) = ?h2
--   (/=) x y = not (x == y)
