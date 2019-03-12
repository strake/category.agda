module Category.Examples where

open import Agda.Primitive
open import Data.Product
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Category

set : {ℓ : _} → Category (lsuc ℓ) ℓ ℓ
set {ℓ} = record
    { Dot = Set ℓ;
      _⇨_ = λ A B → A → B;
      id  = λ x → x;
      _∘_ = _∘_;
      _≈_ = _≡_;
      isCategory = record
          { isEquivalence = ≡.isEquivalence;
            ∘-cong = c;
            ident = refl , refl;
            assoc = refl } }

  where _∘_ : {A B C : Set ℓ} → (B → C) → (A → B) → A → C
        (f ∘ g) x = f (g x)

        c : {A B C : Set ℓ} {f u : B → C} {g v : A → B} → f ≡ u → g ≡ v → (f ∘ g) ≡ (u ∘ v)
        c refl refl = refl
