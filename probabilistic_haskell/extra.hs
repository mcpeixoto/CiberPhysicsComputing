{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE DeriveFunctor #-}


module ProgTerm where

import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Trans.Class (lift)
import Probability
import Data.Function (on)
import Data.List (sort)
import Data.Ord (comparing)
-- Define the type of variables
-- Vars can be either X, Y, or Z
data Vars = X | Y | Z deriving (Show, Eq, Ord)

instance Eq (Vars -> Double) where
  f == g = (f X, f Y, f Z) == (g X, g Y, g Z)
  
instance Ord (Vars -> Double) where
  compare f g = compare (f X) (g X) `mappend` compare (f Y) (g Y) `mappend` compare (f Z) (g Z)
-- Define the type of LTerms
-- LTerms can be either a Leaf, a Plus, or a Mult
data LTerm = Leaf (Either Vars Double) | Plus LTerm LTerm | Mult Double LTerm
        deriving (Show, Eq, Ord)




-- Define the type of BTerms
-- BTerms can be either a Leq, a Conj, or a Neg
data BTerm = Leq LTerm LTerm | Conj BTerm BTerm | Neg BTerm
        deriving (Show, Eq, Ord)

-- Define the type of ProgTerms
-- ProgTerms can be either an Asg, a Seq, an Ife, a Wh, or a Prob
data ProgTerm = Asg Vars LTerm | Seq ProgTerm ProgTerm | Ife BTerm ProgTerm ProgTerm | Wh BTerm ProgTerm | Prob ProgTerm Float ProgTerm
        deriving (Show, Eq, Ord)

-- Define the semantics of LTerms
sem :: LTerm -> (Vars -> Double) -> Double
sem (Leaf (Left x)) e = e x
sem (Leaf (Right r)) _ = r
sem (Mult s t) e = s * sem t e
sem (Plus t1 t2) e = sem t1 e + sem t2 e

-- Define the semantics of BTerms
bsem :: BTerm -> (Vars -> Double) -> Bool
bsem (Leq t1 t2) e = sem t1 e <= sem t2 e
bsem (Neg b) e = not (bsem b e)
bsem (Conj b1 b2) e = bsem b1 e && bsem b2 e

-- Define an auxiliary function to change the memory function
chMem :: Vars -> Double -> (Vars -> Double) -> (Vars -> Double)
chMem x r m = \a -> if a /= x then m a else r


-- Define the semantics of ProgTerms using the MaybeT and Dist monads
psem :: ProgTerm -> (Vars -> Double) -> Dist (Maybe (Vars -> Double))

-- Evaluates an assignment statement by updating the memory with the result of evaluating the term.
psem (Asg x t) m = return (Just (chMem x (sem t m) m))

-- Evaluates a sequence of programs by executing the first program, updating the memory,
-- and then executing the second program with the updated memory.
psem (Seq p q) m = do
  m' <- psem p m
  case m' of
    Just m'' -> psem q m''
    Nothing -> return Nothing

-- Evaluates an if-else statement by evaluating the condition, and then executing either
-- the first program or the second program based on the condition's result.
psem (Ife b p q) m = do
  v <- return (Just (bsem b m))
  case v of
    Just True -> psem p m
    Just False -> psem q m
    Nothing -> return Nothing

-- Evaluates a while loop by evaluating the condition, and if it's true,
-- executes the program inside the loop and repeats the process.
-- If the condition is false or the evaluation fails, the loop ends.
psem (Wh b p) m = do
  v <- return (Just (bsem b m))
  case v of
    Just True -> do
      m' <- psem p m
      case m' of
        Just m'' -> psem (Wh b p) m''
        Nothing -> return Nothing
    Just False -> return (Just m)
    Nothing -> return Nothing

-- Evaluates a probabilistic choice statement by evaluating both the true and false branches
-- and choosing one based on the given probability. The memory is passed to both branches.
psem (Prob p r q) m
  | r < 0 || r > 1 = return Nothing
  | otherwise = do
      mp <- psem p m
      mq <- psem q m
      case (mp, mq) of
        (Just mp', Just mq') -> choose r mp mq
        _ -> return Nothing


-- Defining the memory function (sigma) 
sigma :: Vars -> Double
sigma X = 0
sigma Y = 1
sigma Z = -100


---------------------------------------------------------------------------------------------------
--------------------------------------Testing the semantics----------------------------------------
---------------------------------------------------------------------------------------------------
instance Show (Vars -> Double) where
  show m = let x = m X
               y = m Y
               z = m Z in
               "X = " ++ show x ++ ", Y = " ++ show y ++ ", Z = " ++ show z


-- Define the 'div' function
div2 :: Double -> Double -> Dist (Maybe Double)
div2 _ 0 = return Nothing
div2 x y = return (Just (x / y))

-- Function to test the behavior of 'div2'
testDiv :: Dist (Maybe Double)
testDiv = do
  x <- uniform [1, 2, 3]
  y <- uniform [0, 1, 2, 3]
  div2 x y

-- Test function for the if-else statement
testIfElse :: ProgTerm
testIfElse = Ife (Leq (Leaf (Left X)) (Leaf (Right 10))) (Asg Y (Leaf (Right 1))) (Asg Y (Leaf (Right 0)))

-- Test function for the probabilistic choice statement
testProbChoice :: ProgTerm
testProbChoice = Prob (Asg X (Leaf (Right 1))) 0.2 (Asg X (Leaf (Right 2)))

-- Test function for the while loop
testWhile :: ProgTerm
testWhile = Wh (Leq (Leaf (Left X)) (Leaf (Right 10)) ) (Asg X (Plus (Leaf (Left X)) (Leaf (Right 1))))
-- This function should increment X until it reaches 10
