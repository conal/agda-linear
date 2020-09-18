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

record Symmetric (_↝_ : Arr u) (_◇_ : Bop u) : Set where
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

record Biproduct (_↝_ : Arr u) (_◇_ : Bop u) : Set where
  field
    ⦃ _↝_Cartesian ⦄ : Cartesian _↝_ _◇_
    ⦃ _↝_Cocartesian ⦄ : Cocartesian _↝_ _◇_
open Biproduct ⦃ … ⦄ public

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
     
record Additive (A : Set) : Set where
  infixl 6 _+_
  field
    𝟎 : A
    _+_ : A → A → A
    .id-l  : ∀ {a : A} → 𝟎 + a ≡ a
    .id-r  : ∀ {a : A} → a + 𝟎 ≡ a
    .assoc : ∀ {a b c : A} → (a + b) + c ≡ a + (b + c)
open Additive ⦃ … ⦄ public

+zero : ∀ {m : ℕ} → m +ℕ 0 ≡ m
+zero {zero} = refl
+zero {suc m} rewrite (+zero {m}) = refl
{-# REWRITE +zero #-}

+-assoc : ∀ { m n p : ℕ } → (m +ℕ n) +ℕ p ≡ m +ℕ (n +ℕ p)

+-assoc {zero } {n} {p} = refl
+-assoc {suc m} {n} {p} rewrite +-assoc {m} {n} {p} = refl

instance
  Additiveℕ : Additive ℕ
  Additiveℕ = record {
    𝟎 = zero ;
    _+_ = _+ℕ_ ;
    id-l = refl ;
    id-r = refl ;
    assoc = λ { {a} {b} {c} → +-assoc {a} {b} {c} }
    }
         
