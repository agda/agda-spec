-- TODO: use StrictTotalOrder for QName representation

module Syntax (QName : Set) where

open import Data.Nat.Base
open import Data.List.Base

-- Well-scoped de Bruijn indices
-- n is the length of the context

data Var : ℕ → Set where
  vz : ∀{n} → Var (suc n)
  vs : ∀{n} (x : Var n) → Var (suc n)

-- Example: in context x,y,z (so n = 3)
-- x  is  vs (vs vz) : Var 3
-- y  is      vs vz  : Var 3
-- z  is         vz  : Var 3

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
    con : (c : ConHead) (vs : Args n) → Term n
    def : (f : FuncName) (es : Elims n) → Term n
    lam : (v : Term (suc n)) → Term n
    -- Types
    dat  : (d : DRName) (vs : Args n) → Term n
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
exTyId = pi (sort (uni 0)) (pi (var vz []) (var (vs vz) []))

-- Looking up a field in a field-value collection

-- TODO: Do we want to ensure |fs| = |vs| ?
data LookupField {a} {A : Set a} : (fs : List ProjName) (vs : List A) (f : ProjName) (v : A) → Set where

  here : ∀{f fs v vs}
    → LookupField (f ∷ fs) (v ∷ vs) f v

  there : ∀{f f' fs v v' vs}
    → LookupField fs vs f v
    → LookupField (f' ∷ fs) (v' ∷ vs) f v

-- Substitutions represented as functions

-- σ : Subst Γ Δ  applies to a term living in context Δ
-- and turns it into a term living in context Γ

Substitution : (Γ Δ : ℕ) → Set
Substitution Γ Δ = Var Δ → Term Γ

-- Substitute for the last variable (vz)

sg : ∀{Γ} (u : Term Γ) → Substitution Γ (suc Γ)
sg {Γ} u vz     = u
sg {Γ} u (vs x) = var x []

data All₂ {A B : Set} (R : A → B → Set) : List A → List B → Set where
  nil  : All₂ R [] []
  cons : ∀{x y xs ys}
    → R x y
    → All₂ R xs ys
    → All₂ R (x ∷ xs) (y ∷ ys)

mutual

  data Apply {Γ} : (t : Term Γ) (es : Elims Γ) (v : Term Γ) → Set where

    var : ∀{x es es'}
      → Apply (var x es) es' (var x (es ++ es'))

    proj : ∀{ c πs vs π es u v}
      → LookupField πs vs π u
      → Apply u es v
      → Apply (con (recCon c πs) vs) (proj π ∷ es) v

    def : ∀{f es es'}
      → Apply (def f es) es' (def f (es ++ es'))

    lam : ∀{t t' u v es}
      → SubstTerm (sg u) t t'
      → Apply t' es v
      → Apply (lam t) (apply u ∷ es) v

    -- TODO: congruences

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

--    lam : ∀{v : Term (suc Δ)}
--      → All₂ (SubstElim σ) es es'
--      → SubstTerm σ (def f es) (def f es')

    dat : ∀{d : DRName} {vs : Args Δ} {vs' : Args Γ} 
      → All₂ (SubstTerm σ) vs vs'
      → SubstTerm σ (dat d vs) (dat d vs')

    sort : ∀{s : Sort}
      → SubstTerm σ (sort s) (sort s)

  data SubstElim {Γ Δ} (σ : Substitution Γ Δ) : Elim Δ → Elim Γ → Set where
