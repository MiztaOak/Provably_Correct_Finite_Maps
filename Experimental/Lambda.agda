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

[[_]] : Type → Set₁
[[ int ]] = Lift (Level.suc Level.zero) ℕ
[[ unit ]] = Lift (Level.suc Level.zero) Unit
[[ τ => τ' ]] = [[ τ ]] → [[ τ' ]]


Ctx : Set
Ctx = AVLMap Type

data Env {ℓ : Level} (f : Type → Set ℓ) : Ctx → Set ℓ where
    [] : Env f ∅
    _,_∷_ : ∀ (k : Var) {v : Type}
            → f v
            → {c : Ctx}
            → Env f c
            → Env f (insert k v c)

envLookup : ∀ {x : Var} {τ : Type} {Γ : Ctx} → x ↦ τ ∈ Γ → Env [[_]] Γ → [[ τ ]]
envLookup {x} {τ} prf [] with ∈↦-∅ x τ prf
... | ()
envLookup {x} {τ} {Γ} prf (_,_∷_ x' {τ'} res {c} env) with ∈-ins c x' x τ (λ _ → τ') prf
... | inj₁ refl rewrite ∈insert x {τ} {τ'} c prf = res
... | inj₂ a = envLookup a env

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

translate : ∀ {Γ : Ctx} {τ : Type} → Env [[_]] Γ → Γ ⊢ τ → [[ τ ]]
translate _ (T-Int n) = Level.lift n
translate env (T-Add e₁ e₂) = Level.lift (lower (translate env e₁) + lower (translate env e₂))
translate env T-Unit = Level.lift unit
translate env (T-Var {x = x'} prf) = envLookup prf env
translate env (T-Abs {x = x} e) e' = translate (x , e' ∷ env) e
translate env (T-App e₁ e₂) = translate env e₁ (translate env e₂)

-- -}
-- -}
-- -}
-- -}
