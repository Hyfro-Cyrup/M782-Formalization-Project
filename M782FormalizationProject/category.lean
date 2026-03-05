/-
  Let's expand on what we learned in `class_practice.lean`.
  This time, we'll define a category.
-/

class MyCategory where
  objects : Type
  Hom : objects → objects → Type
  comp : (A : objects) → (B : objects) → (C : objects)
          → (Hom A B) → (Hom B C) → Hom A C
  id : (A : objects) → Hom A A

  id_law_left : ∀ A B : objects, ∀ f : Hom A B, comp A B B f (id B) = f
  id_law_right : ∀ A B : objects, ∀ f : Hom A B, comp A A B (id A) f = f
  assoc {A B C D} : ∀ f : Hom A B, ∀ g : Hom B C, ∀ h : Hom C D,
    comp A B D f (comp B C D g h) =  comp A C D (comp A B C f g) h

notation f "∘" g => MyCategory.comp _ _ _ g f


inductive single where
  | el : single

instance BN : MyCategory := {
  objects := single
  Hom := fun A B => Nat
  comp A B C f g := f + g
  id A := 0

  id_law_left := by
    intro A B f
    rfl

  id_law_right := fun A B f => Nat.add_eq_right.mpr rfl

  assoc := by
    intro A B C D f g h
    exact Eq.symm (Nat.add_assoc f g h)
}

#check  (Nat.zero : BN.Hom single.el single.el)

def asHom : Nat → BN.Hom single.el single.el := fun x => x

#check (asHom 1 : BN.Hom single.el single.el)
