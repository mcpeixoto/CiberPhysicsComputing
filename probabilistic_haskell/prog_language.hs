{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module ProgTerm where
--importTest.QuickCheck
--import Test.QuickCheck
--import qualified GHC.TypeLits as LTerm
--import GHC.Cmm (CmmNode(res))

import Probability
import Data.Function (on)

-------- Defining LTerms, just as developed during the lectures ----------
-- Define the type of variables
-- Vars can be either X, Y or Z
data Vars = X | Y | Z deriving (Show, Eq, Ord)

instance Eq (Vars -> Double) where
  f == g = (f X, f Y, f Z) == (g X, g Y, g Z)
  
instance Ord (Vars -> Double) where
  compare f g = compare (f X) (g X) `mappend` compare (f Y) (g Y) `mappend` compare (f Z) (g Z)
-- LTerms can be either a Leaf, a Plus or a Mult
-- Leaf can be either a variable or a constant (Double)
-- Plus is the sum of two LTerms
-- Mult is the product of a Double and a LTerm
data LTerm = Leaf (Either Vars Double) | Plus LTerm LTerm | Mult Double LTerm
        deriving (Show, Eq, Ord)

-- Defining the memory function (sigma) 
sigma :: Vars -> Double
sigma X = 0
sigma Y = 1
sigma Z = -100

-- Define the semantics of LTerms
sem :: LTerm -> (Vars -> Double) -> Double
-- Leaf (Left x) returns the value of x in the memory function
sem (Leaf (Left x)) e = e x
-- Leaf (Right r) returns the value of r (constant)
sem (Leaf (Right r)) e = r
-- Mult s t returns the product of s and the semantics of t
sem (Mult s t) e = s * (sem t e)
-- Plus t1 t2 returns the sum of the semantics of t1 and t2
sem (Plus t1 t2) e = (sem t1 e) + (sem t2 e)
--------------------------------------------------------------------------------------

------------------ Defining BTerms, just as developed during the lectures ------------
-- Define the type of BTerms
-- BTerms can be either a Leq, a Conj or a Neg
-- Leq is the less or equal comparison of two LTerms
-- Conj is the conjunction of two BTerms
-- Neg is the negation of a BTerm
data BTerm = Leq LTerm LTerm | Conj BTerm BTerm | Neg BTerm deriving (Show,Eq, Ord)

-- Define the semantics of BTerms
bsem :: BTerm -> (Vars -> Double) -> Bool
-- Leq t1 t2 returns True if the semantics of t1 is less or equal than the semantics of t2, False otherwise
bsem (Leq t1 t2) e = if (sem t1 e) <= (sem t2 e) then True else False
-- Neg b returns the negation of the semantics of b
bsem (Neg b) e = not (bsem b e)
-- Conj b1 b2 returns the conjunction of the semantics of b1 and b2 
bsem (Conj b1 b2) e = (bsem b1 e) && (bsem b2 e)
--------------------------------------------------------------------------------------

------------------ Defining ProgTerms, just as developed during the lectures ------------
-- Defining the type of ProgTerms
-- ProgTerms can be either an Asg, a Seq, an Ife, a Wh or a Wr
-- Asg is the assignment of a LTerm to a variable
-- Seq is the sequential composition of two ProgTerms
-- Ife is the if-then-else statement
-- Wh is the while statement
-- Prob is the probabilistic statement
data ProgTerm = Asg Vars LTerm | Seq ProgTerm ProgTerm
        | Ife BTerm ProgTerm ProgTerm | Wh BTerm ProgTerm | Prob ProgTerm Float ProgTerm deriving (Show, Eq, Ord)

-- Defining an auxiliary function to change the memory function
-- This function is necessary since the semantics of ProgTerms allows the assign statement
-- this statement changes the memory
-- this function receives a variable, a value and a memory function and returns a new memory function
chMem :: Vars -> Double -> (Vars -> Double) -> (Vars -> Double)
-- the new memory function is equal to m, except for the value of x, which is r
chMem x r m = \a -> if a /= x then m a else r

-- Defining the semantics of ProbTerms using the Dist monad
psem :: ProgTerm -> (Vars -> Double) -> Dist (Vars-> Double)
-- Asg x t returns the memory function with the value of x changed to t
psem (Asg x t) m = return (chMem x (sem t m) m)
-- Seq p q returns the memory function resulting from executing q after p 
-- after p it is generated a distibution of memory functions, which is used to execute q
psem (Seq p q) m = do m' <- psem p m
                      psem q m'
--psem (Seq p q) m = let m' = psem p m in psem q m'
-- Ife b p q returns the memory function resulting from executing p if the semantics of b is True, 
-- otherwise it returns the memory function resulting from executing q
psem (Ife b p q) m = let v = bsem b m in if v then psem p m else psem q m
-- Wh b p returns the memory function resulting from executing p and Wh b p, if the semantics of b is True, 
-- otherwise it returns the memory function m
psem (Wh b p) m = let v = bsem b m in if v then psem (Seq p (Wh b p)) m else return m
-- Prob p r q returns the memory function resulting from executing p with probability r and q with probability 1-r
psem (Prob p r q) m = do m' <- psem p m -- m' is the memory function resulting from executing p
                         m'' <- psem q m -- m'' is the memory function resulting from executing q
                         choose r m' m'' -- choose returns a distribution of memory functions, with probability r of m' and 1-r of m''






---------------------------------------------------------------------------------------------------
--------------------------------------Testing the semantics----------------------------------------
---------------------------------------------------------------------------------------------------




-- create an instance to show (vars -> double) (memory)
instance Show (Vars -> Double) where
  show m = let x = m X
               y = m Y
               z = m Z in
               "X = " ++ show x ++ ", Y = " ++ show y ++ ", Z = " ++ show z


-- instance to Ord (vars -> double)


--------------------------------------------------------------------------------------
--------------------------------------Testing semantics--------------------------------
x = Leaf (Left X)
y = Leaf (Left Y)
z = Leaf (Left Z)

-- x + 2 * y
t = Plus x (Mult 2 y)

-- wh x <= x do x=x+y; y=y+1
-- x<=x -- BTerm
lexx = Leq x x


-- x=x+y -- ProgTerm
xMaisy = (Asg X (Plus x y))
-- y=y+1
yMaisUm = Asg Y (Plus y (Leaf (Right 1)))
-- wh x <= x do x=x+y; y=y+1
teste = Wh lexx (Seq xMaisy yMaisUm) 

-- Prob xMaisy 0.5 yMaisUM
teste_p = Prob xMaisy 0.5 yMaisUm

-- if x <= y then Prob x = x + 1 0.2 x = 30 else Prob y = y + 1 0.6 y = 40
teste2 = Ife (Leq x y) (Prob (Asg X (Plus x (Leaf (Right 1)))) 0.2 (Asg X (Leaf (Right 30)))) (Prob (Asg Y (Plus y (Leaf (Right 1)))) 0.6 (Asg Y (Leaf (Right 40))))



-- if x <= y then x = x + 1 else y = y + 1 
teste3 = Ife (Leq x y) (Asg X (Plus x (Leaf (Right 1)))) (Asg Y (Plus y (Leaf (Right 1))))



testWhile :: ProgTerm
testWhile = Wh (Leq (Leaf (Left X)) (Leaf (Right 10)) ) (Asg X (Plus (Leaf (Left X)) (Leaf (Right 1))))


