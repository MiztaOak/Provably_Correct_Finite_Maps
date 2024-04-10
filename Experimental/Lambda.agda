{-# OPTIONS --erasure #-}

open import Prelude
open import Level using (Level; Lift; lower)
open import Data.Nat.Base using (ℕ; _+_; suc; zero)
open import NatOrder
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Map.BasicMap
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality

open import Map.BOBMapImp ℕOrder hiding (insert)

module Lambda where

data Unit : Set where
  unit : Unit

Var : Set
Var = ℕ

data Type : Set where
  int : Type
  unit : Type
  _=>_ : Type → Type → Type


open BMapAVLInstance Type

[[_]] : Type → Set
[[ int ]] = ℕ
[[ unit ]] = Unit
[[ τ => τ' ]] = [[ τ ]] → [[ τ' ]]


Ctx : Set
Ctx = AVLMap Type

Env : Ctx → Set
Env c = AllM (λ x → [[ proj₂ x ]]) c

envLookup : ∀ {x : Var} {τ : Type} {Γ : Ctx} → x ↦ τ ∈ Γ → Env Γ → [[ τ ]]
envLookup prf env = allMLookup prf env

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
             → (insert x τ₁ Γ) ⊢ τ₂
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
translate env (T-Abs {x = x} e) e' = translate (allMInsert e' env) e
translate env (T-App e₁ e₂) = translate env e₁ (translate env e₂)

-- -}
-- -}
-- -}
-- -}
