module Category where

open import Agda.Primitive
open import Algebra
open import Data.Product
open import Data.Unit
open import Function using (flip)
open import Relation.Binary
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality.Core as ≡

record IsCategory {a b ℓ}
    (Dot : Set a)
    (_⇨_ : Dot → Dot → Set b)
    (id : {A : Dot} → A ⇨ A)
    (_∘_ : {A B C : Dot} → B ⇨ C → A ⇨ B → A ⇨ C)
    (_≈_ : {A B : Dot} → Rel (A ⇨ B) ℓ) : Set (lsuc (a ⊔ b ⊔ ℓ)) where
    field isEquivalence : {A B : Dot} → IsEquivalence {_} {_} {A ⇨ B} _≈_
          ∘-cong : {A B C : Dot} {f u : B ⇨ C} {g v : A ⇨ B} → f ≈ u → g ≈ v → (f ∘ g) ≈ (u ∘ v)
          ident : {A B : Dot} → {u : A ⇨ B} → (id ∘ u) ≈ u × (u ∘ id) ≈ u
          assoc : {A B C D : Dot} {u : C ⇨ D} {v : B ⇨ C} {w : A ⇨ B} → ((u ∘ v) ∘ w) ≈ (u ∘ (v ∘ w))

record Category a b ℓ : Set (lsuc (a ⊔ b ⊔ ℓ)) where
    infixr 9 _∘_
    infix  4 _≈_
    field Dot : Set a
          _⇨_ : Dot → Dot → Set b
          id  : {A : Dot} → A ⇨ A
          _∘_ : {A B C : Dot} → B ⇨ C → A ⇨ B → A ⇨ C
          _≈_ : {A B : Dot} → Rel (A ⇨ B) ℓ
          isCategory : IsCategory Dot _⇨_ id _∘_ _≈_

    open IsCategory isCategory public

    dual : Category a b ℓ
    dual = record { Dot = Dot;
                    _⇨_ = flip _⇨_;
                    id  = id;
                    _≈_ = _≈_;
                    isCategory = record { isEquivalence = isEquivalence;
                                          ∘-cong = flip ∘-cong;
                                          ident  = swap ident;
                                          assoc  = IsEquivalence.sym isEquivalence assoc } }

    doms : {A B : Dot} → A ⇨ B → Dot × Dot
    doms {A} {B} _ = A , B

    homSetoid : {A B : Dot} → Setoid b ℓ
    homSetoid {A} {B} = record
        { Carrier = A ⇨ B;
          isEquivalence = isEquivalence }

    module Property where
        IsTerminal IsCoterminal : Dot → Set _
        IsTerminal   ⊤ = {A : Dot} → ∃ λ (f : A ⇨ ⊤) → {g : A ⇨ ⊤} → f ≈ g
        IsCoterminal ⊥ = {A : Dot} → ∃ λ (f : ⊥ ⇨ A) → {g : ⊥ ⇨ A} → f ≈ g

        IsProduct : {c : _} {I : Set c} {A : I → Dot} {P : Dot} → ((i : I) → P ⇨ A i) → Set _
        IsProduct {_} {I} {A} {P} p = {X : Dot} → (x : (i : I) → X ⇨ A i) → ∃ λ (u : X ⇨ P) → (i : I) → x i ≈ p i ∘ u

        IsCoproduct : {c : _} {I : Set c} {A : I → Dot} {Q : Dot} → ((i : I) → A i ⇨ Q) → Set _
        IsCoproduct {_} {I} {A} {Q} q = {X : Dot} → (x : (i : I) → A i ⇨ X) → ∃ λ (v : Q ⇨ X) → (i : I) → v ∘ q i ≈ x i

        IsMonic IsEpic : {B C : Dot} → (B ⇨ C) → Set (a ⊔ b ⊔ ℓ)
        IsMonic {B} {_} f = {A : Dot} {g h : A ⇨ B} → f ∘ g ≈ f ∘ h → g ≈ h
        IsEpic  {_} {C} h = {D : Dot} {f g : C ⇨ D} → g ∘ h ≈ f ∘ h → f ≈ g

        IsIsic : {A B : Dot} → (A ⇨ B) → Set (b ⊔ ℓ)
        IsIsic f = ∃ λ f⁻¹ → f⁻¹ ∘ f ≈ id × f ∘ f⁻¹ ≈ id
    open Property

record IsFunctor {a b ℓ a' b' ℓ'}
       (K : Category a b ℓ) (K' : Category a' b' ℓ')
       (F : Category.Dot K → Category.Dot K') (f : {A B : Category.Dot K} → Category._⇨_ K A B → Category._⇨_ K' (F A) (F B)) : Set (lsuc (lsuc (a ⊔ b ⊔ ℓ ⊔ a' ⊔ b' ⊔ ℓ'))) where
    open Category K using (Dot; _⇨_; id; _∘_; _≈_)
    open Category K' using () renaming (Dot to Dot'; _⇨_ to _⇨'_; id to id'; _∘_ to _∘'_; _≈_ to _≈'_)

    field cong : {A B : Dot} {u v : A ⇨ B} → u ≈ v → f u ≈' f v
          ident : {A : Dot} → f (id {A}) ≈' id' {F A}
          distrib : {A B C : Dot} → {u : B ⇨ C} → {v : A ⇨ B} → f (u ∘ v) ≈' f u ∘' f v

record Functor {a b ℓ a' b' ℓ'} (K : Category a b ℓ) (K' : Category a' b' ℓ') : Set (lsuc (lsuc (a ⊔ b ⊔ ℓ ⊔ a' ⊔ b' ⊔ ℓ'))) where
    open Category K using (Dot; _⇨_; id; _∘_)
    open Category K' using () renaming (Dot to Dot'; _⇨_ to _⇨'_; id to id'; _∘_ to _∘'_)

    field F : Dot → Dot'
          f : {A B : Dot} → A ⇨ B → F A ⇨' F B
          isFunctor : IsFunctor K K' F f

    open IsFunctor isFunctor public
