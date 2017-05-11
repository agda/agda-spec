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

DataName = QName  -- datatype name
RecName  = QName  -- record name
FuncName = QName  -- function name
ProjName = QName  -- projection name (overloaded)
ConsName = QName  -- constructor name (overloaded)

-- Data or record constructors

data ConHead : Set where
  dataCon : DataName → ConHead
  recCon  : RecName → (fs : List ProjName) → ConHead

-- Sorts are Set₀, Set₁, ...

data Sort : Set where
  uni : (ℓ : ℕ) → Sort

-- In the following definition of well-scoped syntax,
-- n is always the length of the context.

mutual

  data Term (n : ℕ) : Set where
    var : (x : Var n) (es : Elims n) → Term n
    con : (c : ConHead) (vs : Args n) → Term n
    def : (f : QName) (es : Elims n) → Term n
    lam : (v : Term (suc n)) → Term n
    -- Types
    dat  : (d : QName) (vs : Args n) → Term n  -- TODO: Should we distinguish data and record names?
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
data LookupField {a} {A : Set a} : (fs : List QName) (vs : List A) (f : QName) (v : A) → Set where

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

mutual

  data Apply {Γ} : (t : Term Γ) (es : Elims Γ) (v : Term Γ) → Set where

    beta : ∀{t t' u v es}
      → SubstTerm (sg u) t t'
      → Apply t' es v
      → Apply (lam t) (apply u ∷ es) v

    proj : ∀{ c πs vs π es u v}
      → LookupField πs vs π u
      → Apply u es v
      → Apply (con (recCon c πs) vs) (proj π ∷ es) v

    var : ∀{x es es'}
      → Apply (var x es) es' (var x (es ++ es'))

    con : ∀{c vs u es v}
      → Apply (con c (vs ∷ʳ u)) es v
      → Apply (con c vs) (apply u ∷ es) v

    -- TODO: congruences

  data SubstTerm {Γ Δ} (σ : Substitution Γ Δ) : Term Δ → Term Γ → Set where

    var : ∀{x : Var Δ} {es : Elims Δ} {v : Term Γ} {es' : Elims Γ}
      → SubstElims σ es es'
      → Apply (σ x) es' v
      → SubstTerm σ (var x es) v

  data SubstElim {Γ Δ} (σ : Substitution Γ Δ) : Elim Δ → Elim Γ → Set where

  data SubstElims {Γ Δ} (σ : Substitution Γ Δ) : Elims Δ → Elims Γ → Set where
    nil  : SubstElims σ [] []
    cons : ∀{e es e' es'}
      → SubstElim σ e e'
      → SubstElims σ es es'
      → SubstElims σ (e ∷ es) (e' ∷ es')
