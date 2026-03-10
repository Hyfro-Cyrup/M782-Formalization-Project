module Limits where

open import Category as Cat using (Category)
open import Functor as Fun using (Functor)
open import Subtype using (ProofIrrelevantSubtype; _,_; PISubtype≡)

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Product.Properties renaming (Σ-≡,≡→≡ to Σ≡)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)

open Category
open Functor

-- The category of cones over a diagram
-- An object in Cone(D) is a pair (X, {f_i}) where X ∈ 𝒞 and f_i : X → F(i) for each i∈ I. 
-- That is, Objects Cone(D) = Σ (X : 𝒞) ( Π (i : I) Hom(X, F(i))) modulo notation
-- Similarly, Hom_{Cone(D)}((x, {f_i}), (y, {g_i})) = Σ (φ : Hom x y) Π (i : I) φ∘g_i = f_i
-- -- correction: Hom would be that if we didn't want proof irrelevance, and we do
Cone : {I 𝒞 : Category} (D : Functor I 𝒞) → Category
Cone {I} {𝒞} D = 
  let 
  _∘𝒞_ : {A B C : Objects 𝒞} → (f : Hom 𝒞 B C) → (g : Hom 𝒞 A B) → Hom 𝒞 A C
  _∘𝒞_ = λ f g → _∘_ 𝒞 f g in
  record
  { Objects = Σ (Objects 𝒞) (λ X → (i : Objects I) → Hom 𝒞 X (obj-map D i))
  ; Hom = λ X Y → (ProofIrrelevantSubtype (Hom 𝒞 (proj₁ X) (proj₁ Y)) λ φ → (i : Objects I) →  ((proj₂ Y) i) ∘𝒞 φ ≡ (proj₂ X i) )
  ; _∘_ = λ {X Y Z} (φ , proof-φ) (ψ , proof-ψ) → (φ ∘𝒞 ψ) , λ i → trans 
    (assoc 𝒞 (proj₂ Z i) φ ψ) 
    (trans 
      ((cong (λ (x : Hom 𝒞 (proj₁ Y) (obj-map D i)) → x ∘𝒞 ψ) (proof-φ i))) 
      (proof-ψ i))
  ; id = λ A → id 𝒞 (proj₁ A) , λ i → id-law-right 𝒞 (proj₂ A i)
  ; id-law-left = λ (φ , proof-φ) → PISubtype≡ (id-law-left 𝒞 φ)
  ; id-law-right = λ (φ , proof-φ) → PISubtype≡ (id-law-right 𝒞 φ)
  ; assoc = λ (h , _) (g , _) (f , _ ) → PISubtype≡ (assoc 𝒞 h g f)
  }

Cocone : {I 𝒞 : Category} (D : Functor I 𝒞) → Category
Cocone {I} {𝒞} D = 
  let 
  _∘𝒞_ : {A B C : Objects 𝒞} → (f : Hom 𝒞 B C) → (g : Hom 𝒞 A B) → Hom 𝒞 A C
  _∘𝒞_ = λ f g → _∘_ 𝒞 f g in
  record
  { Objects = Σ (Objects 𝒞) (λ X → (i : Objects I) → Hom 𝒞 (obj-map D i) X)
  ; Hom = λ X Y → (ProofIrrelevantSubtype (Hom 𝒞 (proj₁ X) (proj₁ Y)) λ φ → (i : Objects I) →  φ ∘𝒞 (proj₂ X i) ≡ (proj₂ Y i) )
  ; _∘_ = λ {X Y Z} (φ , proof-φ) (ψ , proof-ψ) → (φ ∘𝒞 ψ) , λ i → trans 
      (sym (assoc 𝒞 φ ψ (proj₂ X i))) 
      (trans (cong (λ x → φ ∘𝒞 x) (proof-ψ i)) (proof-φ i))
  ; id = λ A → id 𝒞 (proj₁ A) , λ i → id-law-left 𝒞 (proj₂ A i)
  ; id-law-left = λ (φ , proof-φ) → PISubtype≡ (id-law-left 𝒞 φ)
  ; id-law-right = λ (φ , proof-φ) → PISubtype≡ (id-law-right 𝒞 φ)
  ; assoc = λ (h , _) (g , _) (f , _ ) → PISubtype≡ (assoc 𝒞 h g f)
  }

has-unique-term : Set → Set
has-unique-term T = ProofIrrelevantSubtype T (λ t → (t' : T) → t ≡ t')

is-initial : {𝒞 : Category} (X : Objects 𝒞) → Set
is-initial {𝒞} X = (Y : Objects 𝒞) → has-unique-term (Hom 𝒞 X Y)

Initial : (𝒞 : Category) → Set -- Specifially, to the type of all subtypes of Objects 𝒞 but Set is fine
Initial 𝒞 = ProofIrrelevantSubtype (Objects 𝒞) (λ X → is-initial {𝒞} X)

is-terminal : {𝒞 : Category} (X : Objects 𝒞) → Set
is-terminal {𝒞} X = (Y : Objects 𝒞) → has-unique-term (Hom 𝒞 Y X)

Terminal : (𝒞 : Category) → Set -- Specifially, to the type of all subtypes of Objects 𝒞 but Set is fine
Terminal 𝒞 = ProofIrrelevantSubtype (Objects 𝒞) (λ X → is-terminal {𝒞} X)

Limit : {I 𝒞 : Category} (D : Functor I 𝒞) → Set -- Specifically, the type of all subtypes of Objects Cone D
Limit D = Terminal (Cone D)

Colimit : {I 𝒞 : Category} (D : Functor I 𝒞) → Set -- Specifically, the type of all subtypes of Objects Cone D
Colimit D = Initial (Cocone D)
