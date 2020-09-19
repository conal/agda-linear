{-# OPTIONS --type-in-type --rewriting #-}

module Category where

open import Algebra using (Op₂)
open import Data.Product renaming
      (swap to swap×; _×_ to _×→_; curry to curry→; uncurry to uncurry→)
open import Data.Sum renaming (swap to swap⊎; _⊎_ to _⊎→_)
open import Data.Unit
open import Function renaming (_∘_ to _∘→_; id to id→)
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties
open import Algebra.Definitions using (_DistributesOverˡ_; _DistributesOverʳ_)

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open PE.≡-Reasoning
open import Agda.Builtin.Equality.Rewrite

-- TODO: add levels, and remove --type-in-type.

-- Probably defined somewhere in the standard library. Maybe Rel (with level)
Arr : Set → Set
Arr u = u → u → Set

private
  variable
   u : Set
   A B C D U V Z : u
   _↝_ : u → u → Set
   _◇_ _×_ _⊎_ _⇒_ : Op₂ u

record Category (_↝_ : Arr u) : Set where
  infixr 5 _∘_
  field
    id   : A ↝ A
    _∘_  : (B ↝ C) → (A ↝ B) → (A ↝ C)
    .idˡ  : ∀ {f : A ↝ B} → id ∘ f ≡ f
    .idʳ  : ∀ {f : A ↝ B} → f ∘ id ≡ f
    .assoc : ∀ {h : C ↝ D} {g : B ↝ C} {f : A ↝ B} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
open Category ⦃ … ⦄ public

Fun : Set → Set → Set
Fun = λ (A B : Set) → A → B

instance
  →-Category : Category Fun
  →-Category = record {
    id = id→ ;
    _∘_ = _∘′_ ;
    idˡ = refl ;
    idʳ = refl ;
    assoc = refl }

record Monoidal _↝_ (_◇_ : Op₂ u) : Set where
  field
    ⦃ cat ⦄ : Category _↝_
    _⊙_ : (A ↝ C) → (B ↝ D) → ((A ◇ B) ↝ (C ◇ D))
open Monoidal ⦃ … ⦄ public

-- Is there a way to declare fixity of locally defined operators like × and ⊙?

first : ⦃ _ : Monoidal _↝_ _◇_ ⦄ -> (A ↝ C) -> ((A ◇ B) ↝ (C ◇ B))
first f = f ⊙ id

second : ⦃ _ : Monoidal _↝_ _◇_ ⦄ -> (B ↝ D) -> ((A ◇ B) ↝ (A ◇ D))
second f = id ⊙ f

instance
  →-Monoidal× : Monoidal Fun (_×→_)
  →-Monoidal× = record {
    _⊙_ = λ { f g (a , b) → (f a , g b) } }

instance
  →-Monoidal⊎ : Monoidal Fun (_⊎→_)
  →-Monoidal⊎ = record {
    _⊙_ = λ { f g → (λ { (inj₁ a) → inj₁ (f a) ; (inj₂ b) → inj₂ (g b) }) } }

record Cartesian _↝_ (_×_ : Op₂ u) : Set where
  field
    ⦃ _↝_Monoidal ⦄ : Monoidal _↝_ _×_
    exl : (A × B) ↝ A
    exr : (A × B) ↝ B
    dup : A ↝ (A × A)
open Cartesian ⦃ … ⦄ public

-- TODO: Cartesian laws

infixr 3 _△_
_△_ : ⦃ _ : Cartesian _↝_ _×_ ⦄ → (A ↝ C) → (A ↝ D) → (A ↝ (C × D))
f △ g = (f ⊙ g) ∘ dup

instance
  →-Cartesian : Cartesian Fun _×→_
  →-Cartesian = record {
    exl = proj₁ ;
    exr = proj₂ ;
    dup = λ a → (a , a) }

record Cocartesian _↝_ (_⊎_ : Op₂ u) : Set where
  field
    ⦃ _↝_ComonoidalP ⦄ : Monoidal _↝_ _⊎_
    inl : A ↝ (A ⊎ B)
    inr : B ↝ (A ⊎ B)
    jam : (A ⊎ A) ↝ A
open Cocartesian ⦃ … ⦄ public

infixr 2 _▽_
_▽_ : ⦃ _ : Cocartesian _↝_ _⊎_ ⦄ → (A ↝ C) → (B ↝ C) → ((A ⊎ B) ↝ C)
f ▽ g = jam ∘ (f ⊙ g)

instance
  →-Cocartesian : Cocartesian Fun _⊎→_
  →-Cocartesian = record {
    inl = inj₁ ;
    inr = inj₂ ;
    jam = λ { (inj₁ a) → a ; (inj₂ a) → a }
   }

record Associative (_↝_ : Arr u) _◇_ : Set where
  field
    ⦃ _↝_Monoidal ⦄ : Monoidal _↝_ _◇_
    rassoc : ((A ◇ B) ◇ C) ↝ (A ◇ (B ◇ C))
    lassoc : (A ◇ (B ◇ C)) ↝ ((A ◇ B) ◇ C)
open Associative ⦃ … ⦄ public

AssocViaCart : ⦃ _ : Cartesian _↝_ _×_ ⦄ → Associative _↝_ _×_
AssocViaCart = record {
  lassoc = second exl △ exr ∘ exr ;
  rassoc = exl ∘ exl △ first exr }

instance
  →-Associative× : Associative Fun _×→_
  →-Associative× = AssocViaCart

AssocViaCocart : ⦃ _ : Cocartesian _↝_ _⊎_ ⦄ → Associative _↝_ _⊎_
AssocViaCocart = record {
  lassoc = inl ∘ inl ▽ (inl ∘ inr ▽ inr) ;
  rassoc = (inl ▽ inr ∘ inl) ▽ inr ∘ inr }

instance
  →-Associative⊎ : Associative Fun _⊎→_
  →-Associative⊎ = AssocViaCocart

record Braided (_↝_ : Arr u) _◇_ : Set where
  field
    ⦃ _↝_Monoidal ⦄ : Monoidal _↝_ _◇_
    swap : {A B : u} → (A ◇ B) ↝ (B ◇ A)
open Braided ⦃ … ⦄ public

BraidedViaCart : ⦃ _ : Cartesian _↝_ _×_ ⦄ → Braided _↝_ _×_
BraidedViaCart = record { swap = exr △ exl }

BraidedViaCocart : ⦃ _ : Cocartesian _↝_ _⊎_ ⦄ → Braided _↝_ _⊎_
BraidedViaCocart = record { swap = inr ▽ inl }

instance
  →-Braided× : Braided Fun _×→_
  →-Braided× = BraidedViaCart

instance
  →-Braided⊎ : Braided Fun _⊎→_
  →-Braided⊎ = BraidedViaCocart

record Symmetric (_↝_ : Arr u) (_◇_ : Op₂ u) : Set where
  field
    ⦃ _↝_Braided ⦄ : Braided _↝_ _◇_
    swap∘swap : {A B : u} → swap {A = B} {B = A} ∘ swap {A = A} {B = B} ≡ id
open Symmetric ⦃ … ⦄ public

instance
  →-Symmetric× : Symmetric Fun _×→_
  →-Symmetric× = record { swap∘swap = refl }

-- TODO:
-- 
-- instance
--   →-Symmetric⊎ : Symmetric Fun _⊎→_
--   →-Symmetric⊎ = {!!}

-- Use swap-involutive from the standard library from Data.Sum.Properties

record Biproduct (_↝_ : Arr u) (_◇_ : Op₂ u) : Set where
  field
    ⦃ _↝_Cartesian ⦄ : Cartesian _↝_ _◇_
    ⦃ _↝_Cocartesian ⦄ : Cocartesian _↝_ _◇_
open Biproduct ⦃ … ⦄ public

record Closed _↝_ (_⇒_ : Op₂ u) : Set where
  field
    ⦃ cat ⦄ : Category _↝_
    _⇓_ : (A ↝ B) → (C ↝ D) → ((B ⇒ C) ↝ (A ⇒ D))
open Closed ⦃ … ⦄ public

instance
  →-Closed : Closed Fun Fun
  →-Closed = record { _⇓_ = λ { f h g → h ∘ g ∘ f } }

record CartesianClosed _↝_ _×_ (_⇒_ : Op₂ u) : Set where
  field
    ⦃ closed ⦄ : Closed _↝_ _⇒_
    ⦃ cart ⦄ : Cartesian _↝_ _×_
    curry : ((A × B) ↝ C) → (A ↝ (B ⇒ C))
    uncurry : (A ↝ (B ⇒ C)) → ((A × B) ↝ C)
    apply : ((A ⇒ B) × A) ↝ B
open CartesianClosed ⦃ … ⦄ public

-- applyViaUncurry : ⦃ CartesianClosed _↝_ _×_ _⇒_ ⦄ → ((A ⇒ B) × A) ↝ B
-- applyViaUncurry = uncurry id

-- Fails to resolve id, because there are paths via Closed.cat and Monoidal.cat.
-- How can I ensure that they're the same?

-- TODO: decide whether to keep apply.

instance
  →-CartesianClosed : CartesianClosed Fun _×→_ Fun
  →-CartesianClosed = record {
      curry = curry→ ;
      uncurry = uncurry→ ;
      apply = λ { (f , x) → f x }
      -- apply = applyViaUncurry
      }
     
record Monoid { A : Set } (∅ : A) (_∪_ : A → A → A) : Set where
  field
    .idˡ  : ∀ (a : A) → ∅ ∪ a ≡ a
    .idʳ  : ∀ (a : A) → a ∪ ∅ ≡ a
    .assoc : ∀ (a b c : A) → (a ∪ b) ∪ c ≡ a ∪ (b ∪ c)
open Monoid ⦃ … ⦄ public

-- I'm using explicit parameters here to make Data.Nat.Properties convenient.

instance
  Monoid+ℕ : Monoid 0 _+ℕ_
  Monoid+ℕ = record {
    idˡ = +-identityˡ ;
    idʳ = +-identityʳ ;
    assoc = +-assoc
    }

instance
  Monoid*ℕ : Monoid 1 _*ℕ_
  Monoid*ℕ = record {
    idˡ = *-identityˡ ;
    idʳ = *-identityʳ ;
    assoc = *-assoc
    }
         
record CommutativeMonoid { A : Set } (∅ : A) (_∪_ : A → A → A) : Set where
  field
    ⦃ _Monoid ⦄ : Monoid ∅ _∪_
    .comm : ∀ (a b : A) → (a ∪ b) ≡ (b ∪ a)
open CommutativeMonoid ⦃ … ⦄ public

instance
  CommutativeMonoid+ℕ : CommutativeMonoid 0 _+ℕ_
  CommutativeMonoid+ℕ = record { comm = +-comm }

record Semiring (A : Set) : Set where
  field
    𝟎 𝟏 : A
    _+_ _*_ : A → A → A
    ⦃ _add ⦄ : CommutativeMonoid 𝟎 _+_
    ⦃ _mul ⦄ : Monoid 𝟏 _*_
    .distribˡ : (a b c : A) → a * (b + c) ≡ (a * b) + (a * c)
    .distribʳ : (a b c : A) → (b + c) * a ≡ (b * a) + (c * a)
    .annihilateˡ : (a : A) → 𝟎 * a ≡ 𝟎
    .annihilateʳ : (a : A) → a * 𝟎 ≡ 𝟎
open Semiring ⦃ … ⦄ public

instance
  Semiringℕ : Semiring ℕ
  Semiringℕ = record
    { 𝟎 = 0
    ; 𝟏 = 1
    ; _+_ = _+ℕ_
    ; _*_ = _*ℕ_
    ; distribˡ = *-distribˡ-+
    ; distribʳ = *-distribʳ-+
    ; annihilateˡ = {!!}
    ; annihilateʳ = {!!}
    }

-- TODO: Use Monoid and Semiring from Algebra.Structures in Agda's standard library.
