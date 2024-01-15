open import Prelude 

module OrdSet where
  pattern le = inl !
  pattern ge = inr (inr !)
  pattern eq = inr (inl refl)
  
  record OSet (Carrier : Set) : Set₁ where
    infix 4 _≤_
    field
      --Carrier : Set

      -- relation
      _≤_     : Rel Carrier

      -- invariants of ≤
      trans : ∀ {x y z : Carrier} → x ≤ y → y ≤ z → x ≤ z
      compare : ∀ x y → ⌜ (x ≤ y)⌝ ⊎ ((x ≡ y) ⊎ ⌜ (y ≤ x)⌝ )

  module _ {A : Set} {R : OSet A} where
    open OSet R

    ext : OSet (Ext A)
    (ext OSet.≤ _) ⊤         = True
    (ext OSet.≤ (# x)) (# y) = x ≤ y
    (ext OSet.≤ ⊥) _         = True
    (ext OSet.≤ _) _         = False
    OSet.trans (ext) {x} {y} {⊤} e1 e2       = record {}
    OSet.trans (ext) {# x} {# y} {# z} e1 e2 = trans e1 e2
    OSet.trans (ext) {⊥} {# y} {# z} e1 e2   = record {}
    OSet.trans (ext) {⊥} {⊥} {# z} e1 e2     = record {}
    OSet.trans (ext) {⊥} {⊥} {⊥} e1 e2       = record {}
    OSet.compare (ext) ⊤ ⊤ = inr (inl refl)
    OSet.compare (ext) ⊤ _ = inr (inr (!{{record {}}})) 
    OSet.compare (ext) (# x) ⊤ = inl (!{{record {}}})
    OSet.compare (ext) (# x) (# y) with compare x y
    ... | le = le
    ... | eq = eq
    ... | ge = ge
    OSet.compare (ext) (# x) ⊥ = inr (inr (!{{record {}}}))
    OSet.compare (ext) ⊥ ⊤ = inl (!{{record {}}})
    OSet.compare (ext) ⊥ (# x) = inl (!{{record {}}})
    OSet.compare (ext) ⊥ ⊥ = inr (inl refl)

  module _ where
    OSetℕ : OSet Nat 
    OSet._≤_ OSetℕ = LEℕ
    OSet.trans OSetℕ {x} {zero} {zero} e e' = e
    OSet.trans OSetℕ {zero} {zero} {suc z} e e' = e
    OSet.trans OSetℕ {zero} {suc y} {suc z} e e' = e
    OSet.trans OSetℕ {suc x} {suc y} {suc z} e e' = OSet.trans OSetℕ {x} {y} {z} e e'
    OSet.compare OSetℕ zero zero = eq
    OSet.compare OSetℕ (suc x) zero = inr (inr (!{{record {}}}))
    OSet.compare OSetℕ zero (suc y) = inl (!{{record {}}})
    OSet.compare OSetℕ (suc x) (suc y) with OSet.compare OSetℕ x y
    ... | le = le
    ... | eq = eq
    ... | ge = ge
