module Category.Product where

open import Agda.Primitive
open import Data.Product
open import Relation.Binary.Core

open import Category

map₂ : {ℓa ℓb ℓc ℓp ℓq ℓr : _} {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} {P : A → Set ℓp} {Q : B → Set ℓq} {R : C → Set ℓr} →
       (f : A → B → C) → ({x : _} {y : _} → P x → Q y → R (f x y)) →
       Σ A P → Σ B Q → Σ C R
map₂ f g (u , v) (x , y) = (f u x , g v y)

_×c_ : {aa ba ab bb ℓa ℓb : _} → Category aa ba ℓa → Category ab bb ℓb → Category (aa ⊔ ab) (ba ⊔ bb) (ℓa ⊔ ℓb)
A ×c B = record
    { Dot = Dot A × Dot B;
      _⇨_ = λ { (a , b) (a' , b') → a ⇨a a' × b ⇨b b' };
      id  = id A , id B;
      _∘_ = λ { (f , u) (g , v) → (f ∘a g , u ∘b v) };
      _≈_ = λ { (f , u) (g , v) → (f ≈a g × u ≈b v) };
      isCategory = record
          { isEquivalence = record { refl  = (refl' isEqvA , refl' isEqvB);
                                     sym   = map (sym isEqvA) (sym isEqvB);
                                     trans = map₂ (trans isEqvA) (trans isEqvB) };
            ∘-cong = λ { (pa , pb) (qa , qb) → (∘-cong A pa qa , ∘-cong B pb qb) };
            ident = (proj₁ (ident A) , proj₁ (ident B)) , (proj₂ (ident A) , proj₂ (ident B));
            assoc = assoc A , assoc B } }
  where open Category.Category
        open Category.Category A using () renaming (_⇨_ to _⇨a_; _∘_ to _∘a_; _≈_ to _≈a_; isEquivalence to isEqvA)
        open Category.Category B using () renaming (_⇨_ to _⇨b_; _∘_ to _∘b_; _≈_ to _≈b_; isEquivalence to isEqvB)
        open IsEquivalence renaming (refl to refl')
