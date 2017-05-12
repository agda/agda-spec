-- TODO: use StrictTotalOrder for QName representation

module Syntax (QName : Set) where

open import Data.Nat.Base
open import Data.List.Base

-- Well-scoped de Bruijn indices
-- n is the length of the context

data Var : ℕ → Set where
  vzero : ∀{n} → Var (suc n)
  vsuc : ∀{n} (x : Var n) → Var (suc n)

-- Example: in context x,y,z (so n = 3)
-- x  is  vsuc (vsuc vzero) : Var 3
-- y  is      vsuc vzero  : Var 3
-- z  is         vzero  : Var 3

-- Qualified names

DRName   = QName  -- datatype / record name
FuncName = QName  -- function name
ProjName = QName  -- projection name (overloaded)
ConsName = QName  -- datatype / record constructor name (overloaded)

-- Data or record constructors

data ConHead : Set where
  dataCon : DRName → ConHead
  recCon  : DRName → (fs : List ProjName) → ConHead

-- Sorts are Set₀, Set₁, ...

data Sort : Set where
  uni : (ℓ : ℕ) → Sort

-- In the following definition of well-scoped syntax,
-- n is always the length of the context.

mutual

  data Term (n : ℕ) : Set where
    var : (x : Var n) (es : Elims n) → Term n
    con : (c : ConHead) (vs : Args n) → Term n     -- Fully applied
    def : (f : FuncName) (es : Elims n) → Term n
    lam : (v : Term (suc n)) → Term n
    -- Types
    dat  : (d : DRName) (vs : Args n) → Term n     -- Fully applied
    sort : (s : Sort) → Term n
    pi   : (u : Term n) (v : Term (suc n)) → Term n

  data Elim (n : ℕ) : Set where
    apply : (u : Term n)   → Elim n
    proj  : (π : ProjName) → Elim n

  Elims : (n : ℕ) → Set
  Elims n = List (Elim n)

  Args : (n : ℕ) → Set
  Args n = List (Term n)

-- Example: (A : Set) (x : A) → A
-- is represented by

exTyId : Term 0
exTyId = pi (sort (uni 0)) (pi (var vzero []) (var (vsuc vzero) []))

-- Looking up a field in a field-value collection

-- TODO: Do we want to ensure |fs| = |vs| ?
data LookupField {a} {A : Set a} : (fs : List ProjName) (vs : List A) (f : ProjName) (v : A) → Set where

  here : ∀{f fs v vs}
    → LookupField (f ∷ fs) (v ∷ vs) f v

  there : ∀{f f' fs v v' vs}
    → LookupField fs vs f v
    → LookupField (f' ∷ fs) (v' ∷ vs) f v

-- Renamings represented as functions

Renaming : (Γ Δ : ℕ) → Set
Renaming Γ Δ = Var Δ → Var Γ

weak : ∀{Γ} → Renaming (suc Γ) Γ
weak x = vsuc x

-- If    Γ   ⊢ ρ         : Δ
-- then  Γ,x ⊢ liftRen ρ : Δ,x.

liftRen : ∀{Γ Δ} → Renaming Γ Δ → Renaming (suc Γ) (suc Δ)
liftRen ρ vzero    = vzero
liftRen ρ (vsuc x) = vsuc (ρ x)

-- We need sized types to show termination of rename.
{-# TERMINATING #-}

mutual
  rename : ∀{Γ Δ} (ρ : Renaming Γ Δ) (t : Term Δ) → Term Γ
  rename ρ (var x es) = var (ρ x) (map (renameElim ρ) es)
  rename ρ (con c vs) = con c (map (rename ρ) vs)
  rename ρ (def f es) = def f (map (renameElim ρ) es)
  rename ρ (lam t)    = lam (rename (liftRen ρ) t)
  rename ρ (dat d vs) = dat d (map (rename ρ) vs)
  rename ρ (sort s)   = sort s
  rename ρ (pi u v)   = pi (rename ρ u) (rename (liftRen ρ) v)

  renameElim : ∀{Γ Δ} (ρ : Renaming Γ Δ) (e : Elim Δ) → Elim Γ
  renameElim ρ (apply u) = apply (rename ρ u)
  renameElim ρ (proj π)  = proj π

-- Substitutions represented as functions

-- σ : Subst Γ Δ  applies to a term living in context Δ
-- and turns it into a term living in context Γ

Substitution : (Γ Δ : ℕ) → Set
Substitution Γ Δ = Var Δ → Term Γ

liftSub : ∀{Γ Δ} (σ : Substitution Γ Δ) → Substitution (suc Γ) (suc Δ)
liftSub σ vzero    = var vzero []
liftSub σ (vsuc x) = rename weak (σ x)

-- Substitute for the last variable (vzero)

sg : ∀{Γ} (u : Term Γ) → Substitution Γ (suc Γ)
sg {Γ} u vzero    = u
sg {Γ} u (vsuc x) = var x []

data All₂ {A B : Set} (R : A → B → Set) : List A → List B → Set where
  nil  : All₂ R [] []
  cons : ∀{x y xs ys}
    → R x y
    → All₂ R xs ys
    → All₂ R (x ∷ xs) (y ∷ ys)

mutual

  data Apply {Γ} : (t : Term Γ) (es : Elims Γ) (v : Term Γ) → Set where

    empty : ∀{t}
      → Apply t [] t

    var : ∀{x es es'}
      → Apply (var x es) es' (var x (es ++ es'))

    def : ∀{f es es'}
      → Apply (def f es) es' (def f (es ++ es'))

    proj : ∀{ c πs vs π es u v}
      → LookupField πs vs π u
      → Apply u es v
      → Apply (con (recCon c πs) vs) (proj π ∷ es) v

    lam : ∀{t t' u v es}
      → SubstTerm (sg u) t t'
      → Apply t' es v
      → Apply (lam t) (apply u ∷ es) v

  data SubstTerm {Γ Δ} (σ : Substitution Γ Δ) : Term Δ → Term Γ → Set where

    var : ∀{x : Var Δ} {es : Elims Δ} {v : Term Γ} {es' : Elims Γ}
      → All₂ (SubstElim σ) es es'
      → Apply (σ x) es' v
      → SubstTerm σ (var x es) v

    con : ∀{c : ConHead} {vs : Args Δ} {vs' : Args Γ}
      → All₂ (SubstTerm σ) vs vs'
      → SubstTerm σ (con c vs) (con c vs')

    def : ∀{f : FuncName} {es : Elims Δ} {es' : Elims Γ}
      → All₂ (SubstElim σ) es es'
      → SubstTerm σ (def f es) (def f es')

    lam : ∀{v : Term (suc Δ)} {v'}
      → SubstTerm (liftSub σ) v v'
      → SubstTerm σ (lam v) (lam v')

    dat : ∀{d : DRName} {vs : Args Δ} {vs' : Args Γ}
      → All₂ (SubstTerm σ) vs vs'
      → SubstTerm σ (dat d vs) (dat d vs')

    pi : ∀{U V U' V'}
      → SubstTerm σ U U'
      → SubstTerm (liftSub σ) V V'
      → SubstTerm σ (pi U V) (pi U' V')

    sort : ∀{s : Sort}
      → SubstTerm σ (sort s) (sort s)

  data SubstElim {Γ Δ} (σ : Substitution Γ Δ) : Elim Δ → Elim Γ → Set where

    apply : ∀{u u'}
      → SubstTerm σ u u'
      → SubstElim σ (apply u) (apply u')

    proj : ∀{π}
      → SubstElim σ (proj π) (proj π)
