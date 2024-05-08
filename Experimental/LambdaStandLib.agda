open import Prelude
open import Level using (Level; Lift; lower)
open import Data.Nat.Base using (ℕ; _+_; suc; zero)
open import NatOrder
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Relation.Binary.Definitions
open import Data.Product using (∃)

open import Data.Tree.AVL.Map <-strictTotalOrder
open import Data.Tree.AVL <-strictTotalOrder using (tree)
open import Data.Tree.AVL.Map.Membership.Propositional <-strictTotalOrder
open import Data.Tree.AVL.Indexed.Relation.Unary.All <-strictTotalOrder
open import Data.Tree.AVL.Indexed.Relation.Unary.Any <-strictTotalOrder
open import Data.Tree.AVL.Relation.Unary.Any <-strictTotalOrder using (tree)
open import Data.Tree.AVL.Value (setoid ℕ)
open import Data.Tree.AVL.Indexed <-strictTotalOrder
  using (Tree; Key⁺; _<_<_; ⊥⁺<[_]<⊤⁺; _⊕_; _∼_⊔_; joinˡ⁺; [_]; 1#; 0#; [_]ᴿ; ∼+; ∼0; ∼-; joinʳ⁺)
    renaming (insert to insertT)
open import Function.Base using (_∘′_)

open StrictTotalOrder <-strictTotalOrder using (compare)

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

envInsert : ∀ {x : Var} {τ : Type} {Γ : Ctx} → Env Γ → [[ τ ]] → Env (insert x τ Γ)
envInsert {x} {Γ = tree Γ} env p = eInsert env p ⊥⁺<[ x ]<⊤⁺
  where
    alljoinᴸ : ∀ {l u : Key⁺} {hl hr h : ℕ} {x : Var} {τ : Type}
      → {lt⁺ : ∃ λ i → Tree (const Type) l [ x ] (i ⊕ hl)}
      → {rt : Tree (const Type) [ x ] u hr}
      → [[ τ ]]
      → All (λ (_ , v) → [[ v ]]) (proj₂ lt⁺)
      → All (λ (_ , v) → [[ v ]]) rt
      → (bal : hl ∼ hr ⊔ h)
      → All (λ (_ , v) → [[ v ]]) (proj₂ (joinˡ⁺ (x , τ) lt⁺ rt bal))
    alljoinᴸ {lt⁺ = (0# , lt)} p allL allR bal = node p allL allR
    alljoinᴸ {lt⁺ = (1# , lt)} p allL allR ∼+ = node p allL allR
    alljoinᴸ {lt⁺ = (1# , lt)} p allL allR ∼0 = node p allL allR
    alljoinᴸ {lt⁺ = 1# , Tree.node _ _ _ ∼0 } p (node a aL aR) allR ∼- = node a aL (node p aR allR)
    alljoinᴸ {lt⁺ = 1# , Tree.node _ _ _ ∼- } p (node a aL aR) allR ∼- = node a aL (node p aR allR)
    alljoinᴸ {lt⁺ = 1# , Tree.node _ _ (Tree.node _ _ _ _) ∼+ } p (node a aL (node aᴿ aLᴿ aRᴿ)) allR ∼- =
      node aᴿ (node a aL aLᴿ) (node p aRᴿ allR)

    alljoinᴿ : ∀ {l u : Key⁺} {hl hr h : ℕ} {x : Var} {τ : Type}
      → {lt : Tree (const Type) l [ x ] hl}
      → {rt⁺ : ∃ λ i → Tree (const Type) [ x ] u (i ⊕ hr)}
      → [[ τ ]]
      → All (λ (_ , v) → [[ v ]]) lt
      → All (λ (_ , v) → [[ v ]]) (proj₂ rt⁺)
      → (bal : hl ∼ hr ⊔ h)
      → All (λ (_ , v) → [[ v ]]) (proj₂ (joinʳ⁺ (x , τ) lt rt⁺ bal))
    alljoinᴿ {rt⁺ = (0# , rt)} p allL allR bal = node p allL allR
    alljoinᴿ {rt⁺ = (1# , rt)} p allL allR ∼- = node p allL allR
    alljoinᴿ {rt⁺ = (1# , rt)} p allL allR ∼0 = node p allL allR
    alljoinᴿ {rt⁺ = (1# , Tree.node _ _ _ ∼+)} p allL (node a aL aR) ∼+ = node a (node p allL aL) aR
    alljoinᴿ {rt⁺ = (1# , Tree.node _ _ _ ∼0)} p allL (node a aL aR) ∼+ = node a (node p allL aL) aR
    alljoinᴿ {rt⁺ = (1# , Tree.node _ (Tree.node _ _ _ _) _ ∼-)} p allL (node a (node aᴸ aLᴸ aRᴸ) aR) ∼+ =
      node aᴸ (node p allL aLᴸ) (node a aRᴸ aR)

    eInsert : ∀ {l u : Key⁺} {h : ℕ} {t : Tree (const Type) l u h} {τ : Type} {x : Var}
      → All (λ (_ , v) → [[ v ]]) t
      → [[ τ ]]
      → (ord : l < x < u)
      → All (λ (_ , v) → [[ v ]]) (proj₂ (insertT x τ t ord))
    eInsert leaf p ord = node p leaf leaf
    eInsert {τ = τ} {x} (node {kv = x'} {lt} {rt} {bal} p' l r) p (ordᴸ , ordᴿ) with compare x (key x')
    ... | tri< a _ _ = alljoinᴸ {lt⁺ = m } p' (eInsert l p (ordᴸ , [ a ]ᴿ)) r bal
      where
        m = insertT x τ lt (ordᴸ , [ a ]ᴿ)
    ... | tri≈ _ refl _ = node p l r
    ... | tri> _ _ c = alljoinᴿ {rt⁺ = m} p' l (eInsert r p ([ c ]ᴿ , ordᴿ)) bal
      where
        m = insertT x τ rt ([ c ]ᴿ , ordᴿ)

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
translate env (T-Abs {x = x} e) e' = translate (envInsert env e') e
translate env (T-App e₁ e₂) = translate env e₁ (translate env e₂)

-- -}
-- -}
-- -}
-- -}
