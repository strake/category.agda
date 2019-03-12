module Category.Examples where

open import Agda.Primitive
open import Data.Product
open import Function
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Category

set : {ℓ : _} → Category (lsuc ℓ) ℓ ℓ
set {ℓ} = record
    { _⇨_ = λ A B → A → B;
      isCategory = record
          { isEquivalence = ≡.isEquivalence;
            ∘-cong = ≡.cong₂ _∘′_;
            ident = refl , refl;
            assoc = refl } }
