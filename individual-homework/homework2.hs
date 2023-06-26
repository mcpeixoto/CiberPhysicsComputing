{-# LANGUAGE FlexibleInstances #-} -- For accepting (Vars -> Double) as a type
module TPC where
import Test.QuickCheck --- QuickCheck
import Control.Monad (liftM, liftM2, liftM3)

-- For being able to print to the memory
instance Show (Vars -> Double) where
    show m = let 
                x = m X 
                y = m Y 
                z = m Z
                in
                "X = " ++ show x ++ ", Y = " ++ show y ++ ", Z = " ++ show z

-- Define Linear terms
data Vars = X | Y | Z deriving (Show, Eq)

data LTerm = Leaf (Either Vars Double) | Plus LTerm LTerm | Mult Double LTerm deriving Show

sem :: LTerm -> (Vars -> Double) -> Double
sem (Leaf (Left x)) e = e x
sem (Leaf (Right r)) e = r
sem (Mult s t) e = s * (sem t e)
sem (Plus t1 t2) e = (sem t1 e) + (sem t2 e)

-- Define Boolean terms
data BTerm = Leq LTerm LTerm | Conj BTerm BTerm | Neg BTerm deriving Show

bsem :: BTerm -> (Vars -> Double) -> Bool
bsem (Leq t1 t2) e = if (sem t1 e) <= (sem t2 e) then True else False
bsem (Neg b) e = not (bsem b e)
bsem (Conj b1 b2) e = (bsem b1 e) && (bsem b2 e)

--------------------------------------------------------------------------

-- Memory
chMem :: Vars -> Double -> (Vars -> Double) -> (Vars -> Double)
chMem x r m = \a -> if a /= x then m a else r

data ProgTerm = Asg Vars LTerm | Seq ProgTerm ProgTerm | Write String ProgTerm | Wh BTerm ProgTerm | If BTerm ProgTerm ProgTerm deriving Show

-----------------------------------------------------
-- Implementation of the semantics of the language --
-----------------------------------------------------

wsem :: ProgTerm -> (Vars -> Double) -> (String, (Vars -> Double))
-- Asigment - Given a variable and a linear term, it changes the value of the variable in the memory
wsem (Asg x t) m = ([],chMem x (sem t m) m)
-- Sequence - Given two programs, it executes the first one and then the second one with the memory output of the first one
wsem (Seq p1 p2) m = let (msg1, m1) = wsem p1 m in 
  let (msg2, m2) = wsem p2 m1 in 
    (msg1 ++ msg2, m2)
-- Write - Given a string and a program, it executes the program and then prints the string concatenated with the 'string' output of the program
wsem (Write msg p) m = let (msg1, m1) = wsem p m in 
  (msg ++ msg1, m1)
-- If - Given a boolean term and two programs, it executes the first one if the boolean term is true, otherwise it executes the second one
wsem (If b p1 p2) m = if (bsem b m) then wsem p1 m else wsem p2 m
-- While - Given a boolean term and a program, it executes the program while the boolean term is true
-- This will iteractively execute the program, modifying the memory, until the boolean term is false
wsem (Wh b p) m = if (bsem b m) then let (msg1, m1) = wsem p m in 
  let (msg2, m2) = wsem (Wh b p) m1 in 
    (msg1 ++ msg2, m2) else ([], m)

------------------------------------------------------------------------------------------------------------
------------------------------------------------ QuickCheck ------------------------------------------------
------------------------------------------------------------------------------------------------------------

---------------------------
-- Generation Functions ---
---------------------------

instance CoArbitrary Vars where
  coarbitrary X = variant 0
  coarbitrary Y = variant 1
  coarbitrary Z = variant 2

-- data LTerm = Leaf (Either Vars Double) | Plus LTerm LTerm | Mult Double LTerm deriving Show
instance Arbitrary LTerm where
  arbitrary = sized arbLTerm

arbLTerm :: Int -> Gen LTerm
arbLTerm 0 = do -- 'Stop' condition
  x <- elements [X,Y,Z]
  d <- arbitrary -- For doubles
  oneof [return (Leaf (Left x)),return (Leaf (Right d))] -- For Vars and Doubles
arbLTerm n = do
  x <- elements [X,Y,Z]
  y <- elements [X,Y,Z]
  z <- elements [X,Y,Z]
  d <- arbitrary -- For doubles
  oneof [return (Leaf (Left x)),return (Leaf (Right d)), liftM2 Plus (arbLTerm (n `div` 2)) (arbLTerm (n `div` 2)), liftM2 Mult arbitrary (arbLTerm (n `div` 2))]

-- data BTerm = Leq LTerm LTerm | Conj BTerm BTerm | Neg BTerm deriving Show
instance Arbitrary BTerm where
  arbitrary = sized arbBTerm

arbBTerm :: Int -> Gen BTerm
arbBTerm 0 = do -- 'Stop' condition
  x <- elements [X,Y,Z]
  d <- arbitrary -- For doubles
  oneof [return (Leq (Leaf (Left x)) (Leaf (Left x))), return (Leq (Leaf (Left x)) (Leaf (Right d))), return (Leq (Leaf (Right d)) (Leaf (Left x))), return (Leq (Leaf (Right d)) (Leaf (Right d)))]
arbBTerm n = do
  x <- elements [X,Y,Z]
  y <- elements [X,Y,Z]
  z <- elements [X,Y,Z]
  d <- arbitrary -- For doubles
  oneof [return (Leq (Leaf (Left x)) (Leaf (Left x))), return (Leq (Leaf (Left x)) (Leaf (Right d))), return (Leq (Leaf (Right d)) (Leaf (Left x))), return (Leq (Leaf (Right d)) (Leaf (Right d))), liftM2 Conj (arbBTerm (n `div` 2)) (arbBTerm (n `div` 2)), liftM Neg (arbBTerm (n `div` 2))]


-- data ProgTerm = Asg Vars LTerm | Seq ProgTerm ProgTerm | Write String ProgTerm | Wh BTerm ProgTerm | If BTerm ProgTerm ProgTerm deriving Show
instance Arbitrary ProgTerm where
  arbitrary = sized arbProgTerm

arbProgTerm :: Int -> Gen ProgTerm
arbProgTerm 0 = do -- 'Stop' condition
  x <- elements [X,Y,Z]
  d <- arbitrary -- For doubles
  oneof [return (Asg x (Leaf (Left x))), return (Asg x (Leaf (Right d)))]
arbProgTerm n = do
  x <- elements [X,Y,Z]
  y <- elements [X,Y,Z]
  z <- elements [X,Y,Z]
  d <- arbitrary -- For doubles
  oneof [return (Asg x (Leaf (Left x))), return (Asg x (Leaf (Right d))), liftM2 Seq (arbProgTerm (n `div` 2)) (arbProgTerm (n `div` 2)), liftM2 Write (arbitrary) (arbProgTerm (n `div` 2)), liftM3 If (arbBTerm (n `div` 2)) (arbProgTerm (n `div` 2)) (arbProgTerm (n `div` 2)), liftM2 Wh (arbBTerm (n `div` 2)) (arbProgTerm (n `div` 2))]

------------------------------------------------------
--- Testing  write_m(write_n(p)) ∼ write_{m++n}(p) ---
------------------------------------------------------

memEq :: (Vars -> Double) -> (Vars -> Double) -> Bool
-- Given two memories, it checks if they are the same
memEq m1 m2 = (m1 X == m2 X) && (m1 Y == m2 Y) && (m1 Z == m2 Z)

prop_write :: String -> String -> ProgTerm -> (Vars -> Double) -> Bool
-- Given two strings, it runs the semantics of the program Write s1 (Write s2 p) and Write (s1 ++ s2) p (as specified in the property)
-- and checks if the output string is the same and if the memory is the same
prop_write s1 s2 p m = let (s, m') = wsem (Write s1 (Write s2 p)) m
                           (s', m'') = wsem (Write (s1 ++ s2) p) m in
                                s == s' && memEq m' m''

--------------------------------------------------------------------------

-- Run it
runTests :: IO ()
runTests = verboseCheckWith (stdArgs { maxSuccess = 100 }) prop_write
-- Note that the execution may be stuck in some cases, we suspect is due to the generation of infinite while loops