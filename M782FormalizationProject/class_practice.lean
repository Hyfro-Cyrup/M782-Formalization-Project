/-
  If I want to formalize categories, I should get comfortable with the
  "set/class with operations and axioms" pattern.
  Let's try writing some simple algebraic structures.
-/

/-
  After writing all this, here are my takeaways
  - I experimented with a few different ways of writing proofs down.
    I got some good experience with calc and rw, which are useful

  - I'm wondering what can be done for readability of my work?
    I should define new notation, of course. And coercions for my homomorphism.
    Are there other best practices that I should keep in mind?

  - Is it possible or advisable to skip some of the steps in these proofs?
    For example, is it possible to do multiple rewrites in one line?
    The syntax I imagine is something like
    `formula` = `formula` := by rw[step_1, step_2, step_3]

  - I need to better learn the difference between structure and class.

  - How do I interact with a class as a type? How do I define the opposite magma?
    `def f : Magma -> Magma` fails
-/

class Magma (M : Type) where
  μ : M → M → M

class Semigroup (S : Type) extends Magma S where
  assoc : (fun a b c : S => μ a (μ b c) )= fun a b c => μ (μ a b) c
  assoc_alt : ∀ a b c : S, μ a (μ b c) = μ (μ a b) c
  -- Question: which of these forms is preferable?
  -- Which is easier to use when proving something is a semigroup?
  -- Answer: See theorem inverses_unique for example why assoc_alt is better

class Monoid (M : Type) extends Semigroup M where
  unit : M
  unit_law_left : ∀ m : M, μ unit m = m
  unit_law_right : ∀ m : M, μ m unit = m

class Group (G : Type) extends Monoid G where
  inverse : G → G
  inverse_law_left : ∀ g : G, μ (inverse g) g = unit
  inverse_law_right : ∀ g : G, μ g (inverse g) = unit

structure MagmaHom (M N : Type) [Magma M] [Magma N] where
  toFun : M → N
  multiplicative : ∀ a b : M, toFun (Magma.μ a b) = Magma.μ (toFun a) (toFun b)

/-- The unit of a monoid is the unique element satisfying the left unit law
-/
theorem unit_unique_left {M} [Monoid M] (u : M)
  (u_left : ∀ m : M, Magma.μ u m = m) : u = Monoid.unit := by
  let x := Magma.μ u Monoid.unit
  let y : x = u := Monoid.unit_law_right u
  let z : x = Monoid.unit := u_left Monoid.unit
  let w := Eq.symm y
  exact Eq.trans w z

/-- The unit of a monoid is the unique element satisfying the right unit law
-/
theorem unit_unique_right {M} [Monoid M] (u : M)
  (u_right : ∀ m : M, Magma.μ m u = m) : u = Monoid.unit :=
  Eq.trans (Eq.symm (Monoid.unit_law_left u)) (u_right Monoid.unit)

/-- The inverse of a group element is the unique element satisfying the left inverse law
-/
theorem inverses_unique_left {G} [Group G] (g g' : G)
  (inv_left : Magma.μ g' g = Monoid.unit) : g' = Group.inverse g := by
  calc
    g' = Magma.μ g' Monoid.unit := by rw [Monoid.unit_law_right]
    _ = Magma.μ g' (Magma.μ g (Group.inverse g)) := by rw [Group.inverse_law_right]
    _ = Magma.μ (Magma.μ g' g) (Group.inverse g) := by rw [Semigroup.assoc_alt]
    _ = Magma.μ Monoid.unit (Group.inverse g) := by rw [inv_left]
    _ = Group.inverse g := by rw [Monoid.unit_law_left]
-- Note: Learn how to use notation/infixes

/-- Homomorphism into a group (not a monoid) automatically preserve unit
-/
theorem homs_preserve_unit {G H} [Monoid G] [Group H] (f : MagmaHom G H) :
  f.toFun Monoid.unit = Monoid.unit := by
  let x : G := Monoid.unit -- it doesn't matter what element, but
                           -- this is the only one we can guarantee is there
  calc
    f.toFun Monoid.unit = Magma.μ Monoid.unit (f.toFun Monoid.unit) := by rw [Monoid.unit_law_left]
    _ = Magma.μ (Magma.μ (Group.inverse (f.toFun x)) (f.toFun x)) (f.toFun Monoid.unit) := by rw [@Group.inverse_law_left]
    _ = Magma.μ (Group.inverse (f.toFun x)) (Magma.μ (f.toFun x) (f.toFun (Monoid.unit))) := by rw [@Semigroup.assoc_alt]
    _ = Magma.μ (Group.inverse (f.toFun x)) (f.toFun (Magma.μ x Monoid.unit)) := by rw [@MagmaHom.multiplicative]
    _ = Magma.μ (Group.inverse (f.toFun x)) (f.toFun x) := by rw [@Monoid.unit_law_right]
    _ = Monoid.unit := by rw [@Group.inverse_law_left]

/-- group homomorphisms preserve inverses
-/
theorem homs_preserve_inverses {G H} [Group G] [Group H] (f : MagmaHom G H) :
  f.toFun ∘ Group.inverse = Group.inverse ∘ f.toFun := by
  refine funext ?_
  intro x
  -- want to show that f.toFun (Group.inverse x) has left inverse property
  let g' := f.toFun (Group.inverse x)
  let g := f.toFun x
  let left_inv : Magma.μ g' g = Monoid.unit := by
    calc
      Magma.μ g' g = f.toFun (Magma.μ (Group.inverse x) x) := by rw [f.multiplicative]
      _ = f.toFun Monoid.unit := by rw [Group.inverse_law_left]
      _ = Monoid.unit := by rw [homs_preserve_unit]
  exact inverses_unique_left g g' left_inv
