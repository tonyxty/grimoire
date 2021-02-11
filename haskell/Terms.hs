module Terms where

data Type = Nat | Arrow !Type !Type deriving (Eq)
type Context = [Type]
type Var = Int

data Term = Ref !Var
          | Lam Type Term
          | App Term Term
          | Zero
          | Suc Term
          | CaseNat Term Term Term
          | Mu Term

-- Helpers

prettyPrintType :: Type -> String
prettyPrintType Nat = "ℕ"
prettyPrintType (Arrow a b) =
    '(' : prettyPrintType a ++ " → " ++ prettyPrintType b ++ ")"

prettyPrintTerm :: Int -> Term -> String
prettyPrintTerm _ (Ref x) = '#' : show x
prettyPrintTerm i (Lam a m) = "λ " ++ prettyPrintType a ++ " ⇒\n" ++
    replicate i ' ' ++ prettyPrintTerm (2 + i) m
prettyPrintTerm i (App m1 m2) =
    '(' : prettyPrintTerm i m1 ++ ") ∙ (" ++ prettyPrintTerm i m2 ++ ")"
prettyPrintTerm _ Zero = "zero"
prettyPrintTerm i (Suc m) = "suc (" ++ prettyPrintTerm i m ++ ")"
prettyPrintTerm i (CaseNat m n1 n2) =
    "case " ++ prettyPrintTerm i m ++ '\n' :
        replicate i ' ' ++ "[ Z ⇒ " ++ prettyPrintTerm (2 + i) n1 ++ " ]\n" ++
        replicate i ' ' ++ "[ S ⇒ " ++ prettyPrintTerm (2 + i) n2 ++ " ]"
prettyPrintTerm i (Mu m) = "μ " ++ prettyPrintTerm i m

quoteNat :: Word -> Term
quoteNat 0 = Zero
quoteNat n = Suc (quoteNat (n - 1))

-- Substitution

type Rename = Var -> Var

ext :: Rename -> Rename
ext _ 0 = 0
ext f x = 1 + f (x - 1)

rename :: Rename -> Term -> Term
rename f (Ref x) = Ref (f x)
rename f (Lam a m) = Lam a (rename (ext f) m)
rename f (App m1 m2) = App (rename f m1) (rename f m2)
rename _ Zero = Zero
rename f (Suc m) = Suc (rename f m)
rename f (CaseNat m n1 n2) = CaseNat (rename f m) (rename f n1)
    (rename (ext f) n2)
rename f (Mu m) = Mu (rename (ext f) m)

type Subst = Var -> Term

extSubst :: Subst -> Subst
extSubst _ 0 = Ref 0
extSubst s x = rename (1+) (s (x - 1))

substByTerm :: Term -> Subst
substByTerm m 0 = m
substByTerm _ x = Ref (x - 1)

subst :: Subst -> Term -> Term
subst s (Ref x) = s x
subst s (Lam a m) = Lam a (subst (extSubst s) m)
subst s (App m1 m2) = App (subst s m1) (subst s m2)
subst _ Zero = Zero
subst s (Suc m) = Suc (subst s m)
subst s (CaseNat m n1 n2) = CaseNat (subst s m) (subst s n1)
    (subst (extSubst s) n2)
subst s (Mu m) = Mu (subst (extSubst s) m)

substInto :: Term -> Term -> Term
substInto m = subst (substByTerm m)

-- Examples

two' :: Term
two' = quoteNat 2

suc' :: Term
suc' = Lam Nat (Suc (Ref 0))

plus' :: Term
plus' = Mu (Lam Nat (Lam Nat (
            CaseNat (Ref 1)
                    (Ref 0)
                    (Suc (App (App (Ref 3) (Ref 0)) (Ref 1))))))
