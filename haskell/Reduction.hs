module Reduction where

import Terms
import Data.List

-- Reduction
-- There are two reasonable approaches: to separate typechecking from
-- reduction, or to combine them.  Combining means only one pass is needed, and
-- the pattern matchings are complete, but modularity is sacrificed.  We choose
-- to separate them to better parallel the agda version, and for better
-- extensibility (other operations on welltyped terms can be defined)

-- Right means it's a value
step :: Term -> Either Term Term
step m@(Lam _ _) = Right m
step (App m1 m2) = case step m1 of
    Left m1' -> Left (App m1' m2)
    Right v1@(Lam _ m) -> case step m2 of
        Left m2' -> Left (App v1 m2')
        Right m2' -> Left (m2' `substInto` m)
    _ -> undefined
step Zero = Right Zero
step (Suc m) = case step m of
    Left m' -> Left (Suc m')
    Right v -> Right (Suc v)
step (CaseNat m n1 n2) = case step m of
    Left m' -> Left (CaseNat m' n1 n2)
    Right Zero -> Left n1
    Right (Suc v) -> Left (v `substInto` n2)
    _ -> undefined
step (Pair m1 m2) = case step m1 of
    Left m1' -> Left (Pair m1' m2)
    Right v1 -> case step m2 of
        Left m2' -> Left (Pair v1 m2')
        Right v2 -> Right (Pair v1 v2)
step (CaseProduct m n) = case step m of
    Left m' -> Left (CaseProduct m' n)
    Right (Pair v1 v2) -> Left (v2 `substInto` (v1 `substInto` n))
    _ -> undefined
step m@(Mu m') = Left (m `substInto` m')
step _ = undefined

steps :: Term -> [Term]
steps m = case step m of
    Left m' -> m' : steps m'
    Right v -> [v]

unquoteNat :: Term -> Word
unquoteNat Zero = 0
unquoteNat (Suc m) = 1 + unquoteNat m
unquoteNat _ = undefined

-- Examples of evaluations

main :: IO ()
main = mapM_ putStrLn $ intersperse "—→" $
    map (prettyPrintTerm 2) (steps (App (App plus' two') two'))
