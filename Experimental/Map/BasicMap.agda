module Map.BasicMap where

open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Product
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary using (¬_)
open import Prelude renaming (⊥ to bot; ⊤ to top)
open import Relation.Binary.PropositionalEquality
open import Data.Sum

private
  variable
    ℓ ℓ' : Level

module _ {K : Set ℓ} {V : Set ℓ'} where

  record BMap : Set (lsuc (ℓ ⊔ ℓ')) where
    constructor mkMap
    field
      Map    : Set (ℓ ⊔ ℓ')
      ∅      : Map                 -- Empty
      _↦_∈_ : K → V → Map → Set (ℓ ⊔ ℓ') -- Domain
      unionWith : (K × V → K × V → K × V) → Map → Map → Map
      -- TODO: Translate all union laws to use unionWith
      _∪_    : Map → Map → Map
      lookup : Map → K → Maybe V   -- Apply
      insertWith : (K × V → K × V → K × V) → K × V → Map → Map
      -- TODO: Translate all insert laws to use insertWith
      insert : (K × V) → Map → Map -- Update

    syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

    infix  7 lookup
    infixr 6 _∪_
    infix  5 _↦_∈_

    [_↦_]_ : K → V → Map → Set ℓ'
    [ k ↦ v ] m = lookup m k ≡ just v

    _↦_∉_ : K → V → Map → Set (ℓ ⊔ ℓ')
    k ↦ v ∉ m = ¬ (k ↦ v ∈ m)

    _⊆_ : Map → Map → Set (ℓ ⊔ ℓ')
    n ⊆ m = ∀ k v → k ↦ v ∈ n → k ↦ v ∈ m

    _≐_ : Map → Map → Set (ℓ ⊔ ℓ')
    n ≐ m = (n ⊆ m) × (m ⊆ n)

    field
      -- induction principle (weak)
      {-
      ⊢ ∀ P . P ∅ ∧ (∀ f . P f ⊃ (∀ x y . P (insert f (x , y))))
          ⊃
        ∀ f . P f
      -}
      ip : {P : Map → Set}
           → P ∅ × (∀ m → P m → ∀ k v → P (insert (k , v) m))
           → (∀ m → P m)

      -- induction principle (stronger)
      {-
      ⊢ ∀ P .
          P ∅ ∧
          (∀ f . P f ⊃ (∀ x . ¬(x ∈ f) ⊃ ∀ y . P (insert f (x , y))))
            ⊃
          ∀ f . P f
      -}
      ips : {P : Map → Set (ℓ ⊔ ℓ')}
            → P ∅ × (∀ m → P m → ∀ k v → k ↦ v ∉ m → ∀ v → P (insert (k , v) m))
            → (∀ m → P m)

      lookup-∅ : ∀ {k} → lookup ∅ k ≡ nothing
      ∈-∅ : ∀ {k v} → ¬ (k ↦ v ∈ ∅)

      ∈⇒lookup : ∀ {m k v} → [ k ↦ v ] m → k ↦ v ∈ m
      lookup⇒∈ : ∀ {m k v} → k ↦ v ∈ m → [ k ↦ v ] m

      {-
      ⊢ ∀ f a b . lookup (insert f (a , b)) a = b
      -}
      lookup-insert : (m : Map) → (k : K) → (v : V) → [ k ↦ v ] (insert (k , v) m)

      {-
      ⊢ ∀ a c . (a ≠ c) ⊃
          ∀ f b d .
            insert (insert f (a , b)) (c , d)
              = insert (insert f (c , d)) (a , b)
      -}
      ins-comm : {k k' : K} → {v v' : V} → {m : Map}
                  → ¬ (k ≡ k')
                  → insert (k' , v') (insert (k , v) m)
                    ≐ insert (k , v) (insert (k' , v') m)

      {-
      ⊢ ∀ f a b c . insert (insert f (a , b)) (a , c) = insert f (a , c)
      -}
      ins-same : ∀ {m k v v'}
                 → insert (k , v) (insert (k , v') m) ≐ insert (k , v) m

      {-
      ⊢ ∀ f a b x . x ∈ (insert f (a , b)) → (x = a) ∨ x ∈ f
      -}
      ∈-ins : ∀ {m k x v} → x ↦ v ∈ (insert (k , v) m) → (x ≡ k) ⊎ x ↦ v ∈ m

      ↦-∪ᴸ : ∀ {m1 m2 k v}
               → k ↦ v ∈ m1
               → k ↦ v ∈ (m1 ∪ m2)
      ↦-∪ᴿ : ∀ {m1 m2 k v }
               → k ↦ v ∉ m1
               → lookup m2 k ≡ lookup (m1 ∪ m2) k
      ∪-∅ : ∀ {m} → (m ∪ ∅ ≡ m) × (∅ ∪ m ≡ m)

      ↦∈∪ : ∀ {k v} → ∀ {n m}
            → k ↦ v ∈ (n ∪ m)
            → k ↦ v ∈ n ⊎ k ↦ v ∈ m

      -- equality (bad)
      {-
      ⊢ ∀ f g . (∀ x . lookup f x = lookup g x) → (f = g)
      -}
      equality : ∀ {n m} → (∀ k → lookup n k ≡ lookup m k) → n ≡ m


      -- eq
      {-
      ⊢ ∀ f g x . (x ∈ f ∧ x ∈ g) ∧ (lookup x f ≡ lookup x g) → f ≡ g
      -}
      -- our ∈ includes values, so we can ignore the lookup part.
      eq∈ : (f g : Map) → ∀ k v → k ↦ v ∈ f × k ↦ v ∈ g → f ≡ g

      {-
      ⊢ ∀ f g x . (x ∈ f ∧ x ∈ g) ∧ (x ∈ f → lookup x f ≡ lookup x g) → f ≡ g
      -}
      -- pointless given that our ∈ includes values.
    ip' : {P : Map → Set (ℓ ⊔ ℓ')}
          → P ∅ × (∀ m → P m → ∀ k v → P (insert (k , v) m))
          → (∀ m → P m)
    ip' {P} (b , s) mp = ips (b , λ m x k _ _ v → s m x k v ) mp
