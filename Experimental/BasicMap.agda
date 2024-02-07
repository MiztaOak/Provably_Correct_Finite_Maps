module BasicMap where

-- TODO: find out which are necessary
open import Agda.Builtin.Unit using (⊤)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Product
open import Data.Sum
open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation.Core using (¬_)

private
  variable
    𝓁 l : Level

module _ {K : Set} {V : Set} {l : Level} where

  record BMap : Set (lsuc l) where
    constructor mkMap
    field
      Map    : Set l
      ∅      : Map                 -- Empty
      _∈_    : K → Map → Set       -- Domain
      _∪_    : Map → Map → Map
      lookup : Map → K → Maybe V   -- Apply
      insert : Map → (K × V) → Map -- Update

    syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

    infix  7 lookup
    infixr 6 _∪_
    infix  5 _∈_

    _[_↦_] : Map → K → V → Set
    m [ k ↦ v ] = lookup m k ≡ just v

    _∉_ : K → Map → Set
    k ∉ m = ¬ (k ∈ m)

    _⊆_ : Map → Map → Set
    n ⊆ m = ∀ k → k ∈ n → k ∈ m

    _≐_ : Map → Map → Set
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
      ips : {P : Map → Set}
            → P ∅ × (∀ m → P m → (∀ k → (k ∉ m → (∀ v → P (insert m (k , v))))))
            → (∀ m → P m)

      lookup-∅ : ∀ {k} → lookup ∅ k ≡ nothing
      ∈-∅ : ∀ {k} → k ∈ ∅ ≡ ⊥

      ∈⇒lookup : ∀ {m k v} → m [ k ↦ v ] → k ∈ m
      lookup⇒∈ : ∀ {m k v} → k ∈ m → m [ k ↦ v ]

      {-
      ⊢ ∀ f a b . lookup (insert f (a , b)) a = b
      -}
      insert-∉ : ∀ {m k v} → k ∉ m
                 → (insert m (k , v)) [ k ↦ v ]
      insert-∈ : ∀ {m k v} → k ∈ m
                 → ¬ (m [ k ↦ v ]) -- is this necessary?
                 → (insert m (k , v)) [ k ↦ v ]

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

      ∪-assoc : ∀ {m1 m2 m3}
                    → m1 ∪ (m2 ∪ m3)
                      ≡ (m1 ∪ m2) ∪ m3
      ∪-∅ : ∀ {m} → (m ∪ ∅ ≡ m) × (∅ ∪ m ≡ m)

      ↦∈∪ : ∀ {k v} → ∀ {n m}
            → (n ∪ m) [ k ↦ v ]
            → n [ k ↦ v ] ⊎ m [ k ↦ v ]

      -- equality
      {-
      ⊢ ∀ f g . (∀ x . lookup f x = lookup g x) → (f = g)
      -}
      equality : ∀ {n m} → (∀ k → lookup n k ≡ lookup m k) → n ≡ m
