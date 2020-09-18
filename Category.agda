{-# OPTIONS --type-in-type --rewriting #-}

module Category where

open import Data.Product renaming
      (swap to swap×; _×_ to _×→_; curry to curry→; uncurry to uncurry→)
open import Data.Sum renaming (swap to swap⊎; _⊎_ to _⊎→_)
open import Data.Unit
open import Function renaming (_∘_ to _∘→_; id to id→)
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open PE.≡-Reasoning
open import Agda.Builtin.Equality.Rewrite

Arr : Set → Set
Arr u = u → u → Set

Bop : Set → Set
Bop u = u → u → u

private
  variable
   u : Set
   A B C D U V Z : u
   _↝_ : u → u → Set
   _◇_ _×_ _⊎_ _⇒_ : Bop u

record Category (_↝_ : Arr u) : Set where
  infixr 5 _∘_
  field
    id   : A ↝ A
    _∘_  : (B ↝ C) → (A ↝ B) → (A ↝ C)
    .id-l  : ∀ {f : A ↝ B} → id ∘ f ≡ f
    .id-r  : ∀ {f : A ↝ B} → f ∘ id ≡ f
    .assoc : ∀ {h : C ↝ D} {g : B ↝ C} {f : A ↝ B} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
open Category ⦃ … ⦄ public

Fun : Set → Set → Set
Fun = λ (A B : Set) → A → B

instance
  →-Category : Category Fun
  →-Category = record {
    id = id→ ;
    _∘_ = _∘′_ ;
    id-l = refl ;
    id-r = refl ;
    assoc = refl }

record Monoidal _↝_ (_◇_ : Bop u) : Set where
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

record Cartesian _↝_ (_×_ : Bop u) : Set where
  field
    ⦃ _↝_Monoidal ⦄ : Monoidal _↝_ _×_
    exl : (A × B) ↝ A
    exr : (A × B) ↝ B
    dup : A ↝ (A × A)
open Cartesian ⦃ … ⦄ public

infixr 3 _△_
_△_ : ⦃ _ : Cartesian _↝_ _×_ ⦄ → (A ↝ C) → (A ↝ D) → (A ↝ (C × D))
f △ g = (f ⊙ g) ∘ dup

instance
  →-Cartesian : Cartesian Fun _×→_
  →-Cartesian = record {
    exl = proj₁ ;
    exr = proj₂ ;
    dup = λ a → (a , a) }

record Cocartesian _↝_ (_⊎_ : Bop u) : Set where
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

record AssociativeCat (_↝_ : Arr u) _◇_ : Set where
  field
    ⦃ _↝_Monoidal ⦄ : Monoidal _↝_ _◇_
    rassoc : ((A ◇ B) ◇ C) ↝ (A ◇ (B ◇ C))
    lassoc : (A ◇ (B ◇ C)) ↝ ((A ◇ B) ◇ C)
open AssociativeCat ⦃ … ⦄ public

AssocViaCart : ⦃ _ : Cartesian _↝_ _×_ ⦄ → AssociativeCat _↝_ _×_
AssocViaCart = record {
  lassoc = second exl △ exr ∘ exr ;
  rassoc = exl ∘ exl △ first exr }

instance
  →-AssociativeCat× : AssociativeCat Fun _×→_
  →-AssociativeCat× = AssocViaCart

AssocViaCocart : ⦃ _ : Cocartesian _↝_ _⊎_ ⦄ → AssociativeCat _↝_ _⊎_
AssocViaCocart = record {
  lassoc = inl ∘ inl ▽ (inl ∘ inr ▽ inr) ;
  rassoc = (inl ▽ inr ∘ inl) ▽ inr ∘ inr }

instance
  →-AssociativeCat⊎ : AssociativeCat Fun _⊎→_
  →-AssociativeCat⊎ = AssocViaCocart

record BraidedCat (_↝_ : Arr u) _◇_ : Set where
  field
    ⦃ _↝_Monoidal ⦄ : Monoidal _↝_ _◇_
    swap : (A ◇ B) ↝ (B ◇ A)
open BraidedCat ⦃ … ⦄ public

BraidedViaCart : ⦃ _ : Cartesian _↝_ _×_ ⦄ → BraidedCat _↝_ _×_
BraidedViaCart = record { swap = exr △ exl }

BraidedViaCocart : ⦃ _ : Cocartesian _↝_ _⊎_ ⦄ → BraidedCat _↝_ _⊎_
BraidedViaCocart = record { swap = inr ▽ inl }

instance
  →-BraidedCat× : BraidedCat Fun _×→_
  →-BraidedCat× = BraidedViaCart

instance
  →-BraidedCat⊎ : BraidedCat Fun _⊎→_
  →-BraidedCat⊎ = BraidedViaCocart

record Closed _↝_ (_⇒_ : Bop u) : Set where
  field
    ⦃ cat ⦄ : Category _↝_
    _⇓_ : (A ↝ B) → (C ↝ D) → ((B ⇒ C) ↝ (A ⇒ D))
open Closed ⦃ … ⦄ public

instance
  →-Closed : Closed Fun Fun
  →-Closed = record { _⇓_ = λ { f h g → h ∘ g ∘ f } }

record CartesianClosed _↝_ _×_ (_⇒_ : Bop u) : Set where
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

record NumCat (_↝_ : Arr u) _×_ (A : u) : Set where
  field
    ⦃ cart ⦄ : Cartesian _↝_ _×_
    _+c_ _*c_ _-c_ : (A × A) ↝ A
    negate-c : A ↝ A
open NumCat ⦃ … ⦄ public

record Num (A : Set) : Set where
  field
    _+_ _*_ _-_ : A → A → A
    negate : A → A
    fromℕ : ℕ → A
open Num ⦃ … ⦄ public

instance
  →-NumCat : ⦃ _ : Num A ⦄ → NumCat Fun _×→_ A
  →-NumCat = record {
      _+c_ = uncurry _+_
    ; _*c_ = uncurry _*_
    ; _-c_ = uncurry _-_
    ; negate-c = negate
    }
