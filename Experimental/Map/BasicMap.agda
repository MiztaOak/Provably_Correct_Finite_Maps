module Map.BasicMap where

open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Product
--open import Data.Sum
open import Level renaming (suc to lsuc; zero to lzero)
--open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Prelude renaming (⊥ to bot; ⊤ to top) hiding (_×_; _,_)

private
  variable
    ℓ ℓ' : Level

module _ {K : Set ℓ} {V : Set ℓ'} where

  record BMap : Set (lsuc (ℓ ⊔ ℓ')) where
    constructor mkMap
    field
      Map    : Set (ℓ ⊔ ℓ')
      ∅      : Map                 -- Empty
      _∈_    : K → Map → Set (ℓ ⊔ ℓ') -- Domain
      --[_↦_]_ : K → V → Map → Set (ℓ ⊔ ℓ')
      _∪_    : Map → Map → Map
      lookup : Map → K → Maybe V   -- Apply
      insert : Map → (K × V) → Map -- Update

    syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

    infix  7 lookup
    infixr 6 _∪_
    infix  5 _∈_
    --infix  5 [_↦_]_

    [_↦_]_ : K → V → Map → Set ℓ'
    [ k ↦ v ] m = lookup m k ≡ just v

    _∉_ : K → Map → Set (ℓ ⊔ ℓ')
    k ∉ m = ¬ (k ∈ m)

    _⊆_ : Map → Map → Set (ℓ ⊔ ℓ')
    n ⊆ m = ∀ k → k ∈ n → k ∈ m

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
           → P ∅ × (∀ m → (P m → (∀ k v → P (insert m (k , v)))))
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
            → P ∅ × (∀ m → P m → (∀ k → (k ∉ m → (∀ v → P (insert m (k , v))))))
            → (∀ m → P m)

      lookup-∅ : ∀ {k} → lookup ∅ k ≡ nothing
      ∈-∅ : ∀ {k} → ¬ (k ∈ ∅)

      ∈⇒lookup : ∀ {m k v} → [ k ↦ v ] m → k ∈ m
      lookup⇒∈ : ∀ {m k v} → k ∈ m → [ k ↦ v ] m

      {-
      ⊢ ∀ f a b . lookup (insert f (a , b)) a = b
      -}
      insert-∉ : ∀ {m k v} → k ∉ m
                 → [ k ↦ v ] (insert m (k , v))
      insert-∈ : ∀ {m k v} → k ∈ m
                 → ¬ ([ k ↦ v ] m) -- is this necessary?
                 → [ k ↦ v ] (insert m (k , v))

      {-
      ⊢ ∀ a c . (a ≠ c) ⊃
          ∀ f b d .
            insert (insert f (a , b)) (c , d)
              = insert (insert f (c , d)) (a , b)
      -}
      ins-assoc : {k k' : K} → {v v' : V} → {m : Map}
                  → ¬ (k ≡ k')
                  → insert (insert m (k , v)) (k' , v')
                    ≐ insert (insert m (k' , v')) (k , v)

      {-
      ⊢ ∀ f a b c . insert (insert f (a , b)) (a , c) = insert f (a , c)
      -}
      ins-same : ∀ {m k v v'}
                 → insert (insert m (k , v')) (k , v) ≐ insert m (k , v)

      {-
      ⊢ ∀ f a b x . x ∈ (insert f (a , b)) → (x = a) ∨ x ∈ f
      -}
      ∈-ins : ∀ {m k x v} → x ∈ (insert m (k , v)) → (x ≡ k) ⊎ x ∈ m

      ↦-∪ᴸ : ∀ {m1 m2 k v}
               → [ k ↦ v ] m1
               → [ k ↦ v ] (m1 ∪ m2)
      ↦-∪ᴿ : ∀ {m1 m2 k}
               → k ∉ m1
               → lookup m2 k ≡ lookup (m1 ∪ m2) k
      ∪-∅ : ∀ {m} → (m ∪ ∅ ≡ m) × (∅ ∪ m ≡ m)

      ↦∈∪ : ∀ {k v} → ∀ {n m}
            → [ k ↦ v ] (n ∪ m)
            → [ k ↦ v ] n ⊎ [ k ↦ v ] m

      -- equality
      {-
      ⊢ ∀ f g . (∀ x . lookup f x = lookup g x) → (f = g)
      -}
      equality : ∀ {n m} → (∀ k → lookup n k ≡ lookup m k) → n ≡ m
