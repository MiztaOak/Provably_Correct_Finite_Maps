open import Prelude 
open import Level renaming (suc to s; zero to z)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Data.Product 
open import Relation.Nullary using (¬_)
open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Sum

module OrdSet where
  private
    variable
      ℓ : Level

  inl : ∀ {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → A → A ⊎ B 
  inl = inj₁

  inr : ∀ {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} → B → A ⊎ B
  inr = inj₂

  record OSet (Carrier : Set ℓ) : Set (s (s ℓ)) where
    infix 4 _≺_

    field
      --Carrier : Set

      -- relation for ordering 
      _≺_    : Rel Carrier ℓ

      -- operations for ≺
      compare : ∀ x y → ⌜ (x ≺ y)⌝ ⊎ ((x ≡ y) ⊎ ⌜ (y ≺ x)⌝ )

      -- invariants of ≺ 
      trans : ∀ {x y z : Carrier} → x ≺ y → y ≺ z → x ≺ z
      inreflex : ∀ {x y : Carrier} → x ≺ y → ¬ (x ≡ y) 

  module _ {A : Set ℓ} {R : OSet A} where
    open OSet R

    ext : OSet (Ext A)
    (ext OSet.≺ ⊤) y = Lift ℓ False
    (ext OSet.≺ # x) ⊤ = True
    (ext OSet.≺ # x) (# y) = x ≺ y
    (ext OSet.≺ # x) ⊥ = Lift ℓ False
    (ext OSet.≺ ⊥) ⊤ = True
    (ext OSet.≺ ⊥) (# x) = True
    (ext OSet.≺ ⊥) ⊥ = Lift ℓ False
    OSet.trans ext {# x} {# y} {⊤} e1 e2 = tt
    OSet.trans ext {⊥} {# y} {⊤} e1 e2 = tt
    OSet.trans ext {⊤} {⊥} {⊤} () e2
    OSet.trans ext {# x} {⊥} {⊤} () e2
    OSet.trans ext {⊥} {⊥} {⊤} () e2
    OSet.trans (ext) {# x} {# y} {# z} e1 e2 = trans e1 e2
    OSet.trans (ext) {⊥} {# y} {# z} e1 e2   = tt 
    OSet.trans (ext) {⊥} {⊥} {# z} e1 e2     = tt 
    OSet.trans (ext) {⊥} {⊥} {⊥} e1 e2       = e1 
    OSet.compare ext ⊤ ⊤ = inr (inl refl)
    OSet.compare ext ⊤ (# x) = inr (inr (!{{tt}}))
    OSet.compare ext ⊤ ⊥ = inr (inr (!{{tt}}))
    OSet.compare ext (# x) ⊤ = inl (!{{tt}})
    OSet.compare ext (# x) (# y) with compare x y
    ... | le = le
    ... | eq = eq
    ... | ge = ge
    OSet.compare ext (# x) ⊥ = inr (inr (!{{tt}}))
    OSet.compare ext ⊥ ⊤ = inl (!{{tt}})
    OSet.compare ext ⊥ (# x) = inl (!{{tt}})
    OSet.compare ext ⊥ ⊥ = inr (inl refl)
    OSet.inreflex ext {# x} {.(# x)} prf refl = OSet.inreflex R {x} prf refl
    OSet.inreflex ext {⊥} {.⊥} () refl

  module ExtHelper {A : Set ℓ} {R : OSet A} where
    open OSet R
    open OSet (ext {ℓ} {A} {R}) renaming 
      (_≺_ to _≺Ex_; trans to transEx; compare to compareEx)

    maxEx : ∀ {l u : Ext A} → l ≺Ex u → l ≺Ex ⊤
    maxEx {l} {⊤} prf = prf 
    maxEx {# x} {# y} prf = tt
    maxEx {⊥} {# y} prf = tt
    maxEx {⊤} {⊥} ()
    maxEx {# x} {⊥} ()
    maxEx {⊥} {⊥} ()

    minEx : ∀ {l u : Ext A} → l ≺Ex u → ⊥ ≺Ex u
    minEx {# x} {⊤} prf = tt
    minEx {# x} {# y} prf = tt
    minEx {⊥} {u} prf = prf

  module _ where
    -- Less-or-equal on natural numbers
    LEℕ :  Rel ℕ z 
    LEℕ zero  y     = True
    LEℕ (suc x) zero  = False
    LEℕ (suc x) (suc y) = LEℕ x y

    ≺ℕ : Rel ℕ z 
    ≺ℕ zero zero = False
    ≺ℕ zero (suc y) = True
    ≺ℕ (suc x) zero = False
    ≺ℕ (suc x) (suc y) = ≺ℕ x y

    OSetℕ : OSet ℕ 
    OSet._≺_ OSetℕ = ≺ℕ
    OSet.trans OSetℕ {x} {zero} {zero} e e' = e
    OSet.trans OSetℕ {zero} {zero} {suc z} e e' = tt 
    OSet.trans OSetℕ {zero} {suc y} {suc z} e e' = e
    OSet.trans OSetℕ {suc x} {suc y} {suc z} e e' = OSet.trans OSetℕ {x} {y} {z} e e'
    OSet.compare OSetℕ zero zero = eq
    OSet.compare OSetℕ zero (suc y) = inl (!{{tt}})
    OSet.compare OSetℕ (suc x) zero = inr (inr (!{{tt}}))
    OSet.compare OSetℕ (suc x) (suc y) with OSet.compare OSetℕ x y
    ... | le = le
    ... | eq = eq
    ... | ge = ge
    OSet.inreflex OSetℕ {zero} {.zero} () refl
    OSet.inreflex OSetℕ {suc x} {.(suc x)} p refl = OSet.inreflex OSetℕ {x} {x} p refl
    {-OSet.inreflex OSetℕ zero refl () refl
    OSet.inreflex OSetℕ {suc x} {.(suc x)} prf refl = OSet.inreflex OSetℕ {x} {x} prf refl
    -}
