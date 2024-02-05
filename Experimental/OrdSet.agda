open import Prelude hiding (Rel; _≡_) 
open import Level renaming (suc to s)
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding (trans)

module OrdSet where
  pattern le = inl !
  pattern ge = inr (inr !)
  pattern eq = inr (inl refl)
  
  private
    variable
      ℓ : Level

  record OSet (Carrier : Set ℓ) : Set (s (s ℓ)) where
    infix 4 _≤_
    field
      --Carrier : Set

      -- relation for ordering in the tree
      _≺_    : Rel Carrier ℓ
      -- relation for comparison
      _≤_     : Rel Carrier ℓ

      -- invariants for ≺
      --inreflex : ∀ {x y : Carrier} → x ≺ y → ¬ (x ≡ y) 

      -- invariants of ≤
      trans : ∀ {x y z : Carrier} → x ≤ y → y ≤ z → x ≤ z
      compare : ∀ x y → ⌜ (x ≺ y)⌝ ⊎ ((x ≡ y) ⊎ ⌜ (y ≺ x)⌝ )

  module _ {A : Set ℓ} {R : OSet A} where
    open OSet R

    ext : OSet (Ext A)
    (ext OSet.≤ _) ⊤         = True
    (ext OSet.≤ (# x)) (# y) = x ≤ y
    (ext OSet.≤ ⊥) _         = True
    (ext OSet.≤ _) _         = Lift ℓ False 
    (ext OSet.≺ ⊤) y = Lift ℓ False
    (ext OSet.≺ # x) ⊤ = True
    (ext OSet.≺ # x) (# y) = x ≺ y
    (ext OSet.≺ # x) ⊥ = Lift ℓ False
    (ext OSet.≺ ⊥) ⊤ = True
    (ext OSet.≺ ⊥) (# x) = True
    (ext OSet.≺ ⊥) ⊥ = Lift ℓ False
    OSet.trans (ext) {x} {y} {⊤} e1 e2       = record {}
    OSet.trans (ext) {# x} {# y} {# z} e1 e2 = trans e1 e2
    OSet.trans (ext) {⊥} {# y} {# z} e1 e2   = record {}
    OSet.trans (ext) {⊥} {⊥} {# z} e1 e2     = record {}
    OSet.trans (ext) {⊥} {⊥} {⊥} e1 e2       = record {}
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

  module _ where
    OSetℕ : OSet Nat 
    OSet._≤_ OSetℕ = LEℕ
    OSet._≺_ OSetℕ = ≺ℕ
    OSet.trans OSetℕ {x} {zero} {zero} e e' = e
    OSet.trans OSetℕ {zero} {zero} {suc z} e e' = e
    OSet.trans OSetℕ {zero} {suc y} {suc z} e e' = e
    OSet.trans OSetℕ {suc x} {suc y} {suc z} e e' = OSet.trans OSetℕ {x} {y} {z} e e'
    OSet.compare OSetℕ Nat.zero Nat.zero = eq
    OSet.compare OSetℕ Nat.zero (suc y) = inl (!{{tt}})
    OSet.compare OSetℕ (suc x) Nat.zero = inr (inr (!{{tt}}))
    OSet.compare OSetℕ (suc x) (suc y) with OSet.compare OSetℕ x y
    ... | le = le
    ... | eq = eq
    ... | ge = ge
