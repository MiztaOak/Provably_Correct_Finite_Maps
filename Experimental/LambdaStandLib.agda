open import Prelude
open import Level using (Level; Lift; lower)
open import Data.Nat.Base using (ℕ; _+_; suc; zero)
open import NatOrder
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Relation.Binary.Bundles using (StrictTotalOrder)

open import Data.Tree.AVL.Map <-strictTotalOrder
open import Data.Tree.AVL <-strictTotalOrder using (tree)
open import Data.Tree.AVL.Map.Membership.Propositional <-strictTotalOrder
open import Data.Tree.AVL.Indexed.Relation.Unary.All <-strictTotalOrder
open import Data.Tree.AVL.Indexed.Relation.Unary.Any <-strictTotalOrder
open import Data.Tree.AVL.Relation.Unary.Any <-strictTotalOrder using (tree)
open import Data.Tree.AVL.Value (setoid ℕ)
open import Data.Tree.AVL.Indexed <-strictTotalOrder using (Tree; Key⁺)
open import Function.Base using (_∘′_)

module LambdaStandLib where

data Unit : Set where
  unit : Unit

Var : Set
Var = ℕ

data Type : Set where
  int : Type
  unit : Type
  _=>_ : Type → Type → Type


[[_]] : Type → Set
[[ int ]] = ℕ
[[ unit ]] = Unit
[[ τ => τ' ]] = [[ τ ]] → [[ τ' ]]


Ctx : Set
Ctx = Map Type

Env : Ctx → Set
Env (tree c) = All (λ (_ , v) → [[ v ]]) c

_↦_∈_ : ℕ → Type → Ctx → Set
_↦_∈_ k v c = (k , v) ∈ₖᵥ c

envLookup : ∀ {x : Var} {τ : Type} {Γ : Ctx} → x ↦ τ ∈ Γ → Env Γ → [[ τ ]]
envLookup (tree prf) env = eLookup prf env
  where
    eLookup : ∀ {l u : Key⁺} {h : ℕ} {t : Tree (const Type) l u h} {τ : Type} {x : Var}
      → Any (_≈ₖᵥ_ (x , τ) ∘′ toPair) t → All (λ (_ , v) → [[ v  ]]) t  → [[ τ ]]
    eLookup (here (refl , refl)) (node p lt rt) = p
    eLookup (left prf) (node p lt rt) = eLookup prf lt
    eLookup (right prf) (node p lt rt) = eLookup prf rt

data _⊢_ : Ctx → Type → Set where
  T-Int  : ∀ {Γ : Ctx}
             → ℕ
           ------------
             → Γ ⊢ int

  T-Add  : ∀ {Γ : Ctx}
             → Γ ⊢ int
             → Γ ⊢ int
           ------------
             → Γ ⊢ int

  T-Unit : ∀ {Γ : Ctx}
           -------------
             → Γ ⊢ unit

  T-Var  : ∀ {Γ : Ctx} {τ : Type} {x : Var}
             → x ↦ τ ∈ Γ
           --------------------------
             → Γ ⊢ τ

  T-Abs  : ∀ {Γ : Ctx} {x : Var} {τ₁ τ₂ : Type}
             → insert x τ₁ Γ ⊢ τ₂
           ------------------------------------
             → Γ ⊢ (τ₁ => τ₂)

  T-App  : ∀ {Γ : Ctx} {τ₁ τ₂ : Type}
             → Γ ⊢ (τ₁ => τ₂)
             → Γ ⊢ τ₁
           --------------------------
             → Γ ⊢ τ₂

translate : ∀ {Γ : Ctx} {τ : Type} → Env Γ → Γ ⊢ τ → [[ τ ]]
translate _ (T-Int n) = n
translate env (T-Add e₁ e₂) = translate env e₁ + translate env e₂
translate env T-Unit = unit
translate env (T-Var {x = x'} prf) = envLookup prf env
translate env (T-Abs {x = x} e) e' = translate {!!} e
translate env (T-App e₁ e₂) = translate env e₁ (translate env e₂)

-- -}
-- -}
-- -}
-- -}
