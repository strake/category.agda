module Algebra.Monoid.Category where

open import Algebra
open import Data.Product
open import Data.Unit

open import Category

fromMonoid : {ℓ : _} → (monoid : Monoid ℓ ℓ) → Category _ _ _
fromMonoid {ℓ} monoid = record
    { Dot = ⊤;
      _⇨_ = λ tt tt → Carrier;
      id  = ε;
      _∘_ = _∙_;
      _≈_ = _≈_;
      isCategory = record
          { isEquivalence = isEquivalence;
            ∘-cong = ∙-cong;
            ident = λ {tt tt} {u} → uncurry <_,_> identity u;
            assoc = λ {tt tt tt tt} {u v w} → assoc u v w } }
  where open Monoid monoid
