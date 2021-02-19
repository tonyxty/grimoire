{-# LANGUAGE FlexibleInstances #-}
module Inference where

import Terms
import Safe
import Data.Either.Combinators
import Control.Monad.Fail ()

data TermS = RefS Var
           | AppS TermS TermI
           | Synthesize Type TermI

data TermI = LamI TermI
           | ZeroI
           | SucI TermI
           | CaseNatI TermI TermI TermI
           | PairI TermI TermI
           | CaseProductI TermS TermI
           | MuI TermI
           | Inherit TermS

type TypeError = String
type TC a = Either TypeError a

instance MonadFail (Either TypeError) where
    fail = Left

var :: Context -> Var -> TC Type
var g x = maybeToRight "DBI out of bound" (atMay g x)

synthesize :: Context -> TermS -> TC (Type, Term)
synthesize g (RefS x) = do
    a <- var g x
    return (a, Ref x)
synthesize g (AppS m1 m2) = do
    (Arrow a b, m1') <- synthesize g m1
    m2' <- inherit g a m2
    return (b, App m1' m2')
synthesize g (Synthesize a m) = do
    m' <- inherit g a m
    return (a, m')

inherit :: Context -> Type -> TermI -> TC Term
inherit g (Arrow a b) (LamI m) = do
    m' <- inherit (a : g) b m
    return (Lam a m')
inherit _ Nat ZeroI = return Zero
inherit g Nat (SucI m) = do
    m' <- inherit g Nat m
    return (Suc m')
inherit g a (CaseNatI m n1 n2) = do
    m' <- inherit g Nat m
    n1' <- inherit g a n1
    n2' <- inherit (Nat : g) a n2
    return (CaseNat m' n1' n2')
inherit g (Product a1 a2) (PairI m1 m2) = do
    m1' <- inherit g a1 m1
    m2' <- inherit g a2 m2
    return (Pair m1' m2')
inherit g a (CaseProductI m n) = do
    (Product a1 a2, m') <- synthesize g m
    n' <- inherit (a2 : a1 : g) a n
    return (CaseProduct m' n')
inherit g a (MuI m) = do
    m' <- inherit (a : g) a m
    return (Mu m')
inherit g a (Inherit m) = do
    (a', m') <- synthesize g m
    if a == a' then
        return m'
    else
        Left "type mismatch"
inherit _ _ _ = Left "type mismatch"

refI :: Var -> TermI
refI x = Inherit (RefS x)

plusI :: TermI
plusI = MuI (LamI (LamI (
        CaseNatI (refI 1)
                 (refI 0)
                 (SucI (Inherit (AppS (AppS (RefS 3) (refI 0)) (refI 1)))))))

plusS :: TermS
plusS = Synthesize (Arrow Nat (Arrow Nat Nat)) plusI

main :: IO ()
main = do
    case synthesize [] plusS of
        Left e -> error e
        Right (_, m) -> putStrLn $ prettyPrintTerm 2 m
