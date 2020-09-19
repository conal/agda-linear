open import Level

module Category where

open import Relation.Binary using (Rel)
open import Algebra using (Op₂)

-- TODO: add levels, and remove --type-in-type.

Arr : Set → Set₁
Arr A = Rel A 0ℓ

private
  variable
   u : Set
   A B C D U V Z : u
   _↝_ : u → u → Set
   _◇_ _×_ _⊎_ _⇨_ : Op₂ u

record Category (_↝_ : Arr u) : Set₁ where
  infix 4 _≈_
  infixr 9 _∘_
  field
    _≈_  : Arr (A ↝ B)
           -- Rel (A ↝ B) 0ℓ
    id   : A ↝ A
    _∘_  : (B ↝ C) → (A ↝ B) → (A ↝ C)
    .idˡ  : ∀ {f : A ↝ B} → id ∘ f ≈ f
    .idʳ  : ∀ {f : A ↝ B} → f ∘ id ≈ f
    .assoc : ∀ {h : C ↝ D} {g : B ↝ C} {f : A ↝ B} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
open Category ⦃ … ⦄ public

record Monoidal _↝_ (_◇_ : Op₂ u) : Set₁ where
  infixr 2 _⊙_
  field
    ⦃ cat ⦄ : Category _↝_
    _⊙_ : (A ↝ C) → (B ↝ D) → ((A ◇ B) ↝ (C ◇ D))
open Monoidal ⦃ … ⦄ public

-- Is there a way to declare fixity of parameters like × and ⊙?

first : ⦃ _ : Monoidal _↝_ _◇_ ⦄ -> (A ↝ C) -> ((A ◇ B) ↝ (C ◇ B))
first f = f ⊙ id

second : ⦃ _ : Monoidal _↝_ _◇_ ⦄ -> (B ↝ D) -> ((A ◇ B) ↝ (A ◇ D))
second f = id ⊙ f

record Cartesian _↝_ (_×_ : Op₂ u) : Set₁ where
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

record Cocartesian _↝_ (_⊎_ : Op₂ u) : Set₁ where
  field
    ⦃ _↝_ComonoidalP ⦄ : Monoidal _↝_ _⊎_
    inl : A ↝ (A ⊎ B)
    inr : B ↝ (A ⊎ B)
    jam : (A ⊎ A) ↝ A
open Cocartesian ⦃ … ⦄ public

infixr 2 _▽_
_▽_ : ⦃ _ : Cocartesian _↝_ _⊎_ ⦄ → (A ↝ C) → (B ↝ C) → ((A ⊎ B) ↝ C)
f ▽ g = jam ∘ (f ⊙ g)

record Associative (_↝_ : Arr u) _◇_ : Set₁ where
  field
    ⦃ _↝_Monoidal ⦄ : Monoidal _↝_ _◇_
    rassoc : ((A ◇ B) ◇ C) ↝ (A ◇ (B ◇ C))
    lassoc : (A ◇ (B ◇ C)) ↝ ((A ◇ B) ◇ C)
open Associative ⦃ … ⦄ public

AssocViaCart : ⦃ _ : Cartesian _↝_ _×_ ⦄ → Associative _↝_ _×_
AssocViaCart = record {
  lassoc = second exl △ exr ∘ exr ;
  rassoc = exl ∘ exl △ first exr }

AssocViaCocart : ⦃ _ : Cocartesian _↝_ _⊎_ ⦄ → Associative _↝_ _⊎_
AssocViaCocart = record {
  lassoc = inl ∘ inl ▽ (inl ∘ inr ▽ inr) ;
  rassoc = (inl ▽ inr ∘ inl) ▽ inr ∘ inr }

record Braided (_↝_ : Arr u) _◇_ : Set₁ where
  field
    ⦃ _↝_Monoidal ⦄ : Monoidal _↝_ _◇_
    swap : {A B : u} → (A ◇ B) ↝ (B ◇ A)
open Braided ⦃ … ⦄ public

BraidedViaCart : ⦃ _ : Cartesian _↝_ _×_ ⦄ → Braided _↝_ _×_
BraidedViaCart = record { swap = exr △ exl }

BraidedViaCocart : ⦃ _ : Cocartesian _↝_ _⊎_ ⦄ → Braided _↝_ _⊎_
BraidedViaCocart = record { swap = inr ▽ inl }

record Symmetric (_↝_ : Arr u) (_◇_ : Op₂ u) : Set₁ where
  field
    ⦃ _↝_Braided ⦄ : Braided _↝_ _◇_
    swap∘swap : {A B : u} → swap {A = B} {B = A} ∘ swap {A = A} {B = B} ≈ id
open Symmetric ⦃ … ⦄ public

record Biproduct (_↝_ : Arr u) (_◇_ : Op₂ u) : Set₁ where
  field
    ⦃ _↝_Cartesian ⦄ : Cartesian _↝_ _◇_
    ⦃ _↝_Cocartesian ⦄ : Cocartesian _↝_ _◇_
open Biproduct ⦃ … ⦄ public

record Closed _↝_ (_⇨_ : Op₂ u) : Set₁ where
  field
    ⦃ cat ⦄ : Category _↝_
    _⇓_ : (A ↝ B) → (C ↝ D) → ((B ⇨ C) ↝ (A ⇨ D))
open Closed ⦃ … ⦄ public

record CartesianClosed _↝_ _×_ (_⇨_ : Op₂ u) : Set₁ where
  field
    ⦃ closed ⦄ : Closed _↝_ _⇨_
    ⦃ cart ⦄ : Cartesian _↝_ _×_
    curry : ((A × B) ↝ C) → (A ↝ (B ⇨ C))
    uncurry : (A ↝ (B ⇨ C)) → ((A × B) ↝ C)
    apply : ((A ⇨ B) × A) ↝ B
open CartesianClosed ⦃ … ⦄ public

-- applyViaUncurry : ⦃ CartesianClosed _↝_ _×_ _⇨_ ⦄ → ((A ⇨ B) × A) ↝ B
-- applyViaUncurry = uncurry id

-- Fails to resolve id, because there are paths via Closed.cat and Monoidal.cat.
-- How can I ensure that they're the same?

-- TODO: decide whether to keep apply.
