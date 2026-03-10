{-
    Define a subtype of a given type using a dependent type (property) P : X → Set
    Found this helpful when defining the category of cones over a diagram. 
    Essentially just adds proof irrelevance to a sigma type
-}
module Subtype where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- represents all terms of X satisfying property P
record ProofIrrelevantSubtype (X : Set) (P : X → Set) : Set where
  constructor _,_
  field
    term : X
    . proof : P term -- the dot makes it irrelevant


open ProofIrrelevantSubtype

-- I'm not actually sure why this works. This function definition feels incomplete unless refl is guaranteed to be the only  
-- term in the propositional equality type. And if that's the case, then why did I have so much trouble proving two 
-- proofs of equality were equal without this helper record and lemma
PISubtype≡ : {X : Set} {P : X → Set} {x y : ProofIrrelevantSubtype X P} → (term x ≡ term y) → x ≡ y
PISubtype≡ refl = refl