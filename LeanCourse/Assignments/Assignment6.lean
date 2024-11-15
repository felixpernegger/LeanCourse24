import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8.1.
  Chapter 7 explains some of the design decisions for classes in Mathlib.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 19.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


/- Prove the following exercises about functions where the domain/codomain are
subtypes. -/

abbrev PosReal : Type := {x : ℝ // x > 0}

/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by {
    intro x y xy
    simp
    refine (log_le_log_iff ?h ?h₁).mpr (hf xy)
    exact (f x).2
    exact (f y).2
  }

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : range f ⊆ {x | x > 0}) (h2f : Monotone f) :
  Monotone (log ∘ f) := by {
    intro x y xy
    simp
    refine (log_le_log_iff ?h ?h₁).mpr (h2f xy)
    apply hf
    exact mem_range_self x
    apply hf
    exact mem_range_self y
  }

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by {
      intro x y xy
      simp
      apply hf
      simp
      assumption
  }

/- Only specify that a function is well-behaved on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by {
      intro x y xy
      simp
      apply hf
      simp
      exact exp_pos x
      simp
      exact exp_pos y
      exact exp_le_exp.mpr xy
  }



variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup


/- State and prove that the preimage of `U` under the composition of `φ` and `ψ` is a preimage
of a preimage of `U`. This should be an equality of subgroups! -/
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : Subgroup.comap (ψ.comp φ) U = Subgroup.comap φ (Subgroup.comap ψ U):=
  rfl


/- State and prove that the image of `S` under the composition of `φ` and `ψ`
is a image of an image of `S`. -/
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : Subgroup.map (ψ.comp φ) S = Subgroup.map ψ (Subgroup.map φ S) := by
  ext
  simp at *



/- Define the conjugate of a subgroup, as the elements of the form `xhx⁻¹` for `h ∈ H`. -/
def conjugate (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {g : G | ∃h ∈ H, g=x*h*x⁻¹}
  mul_mem' := by
    intro a b ah bh
    simp
    obtain ⟨u,⟨uh1,uh2⟩⟩ := ah
    obtain ⟨v,⟨vh1,vh2⟩⟩ := bh
    use u*v
    constructor
    exact (Subgroup.mul_mem_cancel_right H vh1).mpr uh1
    rw[uh2,vh2]
    group
  one_mem' := by
    use 1
    constructor
    exact Subgroup.one_mem H
    group
  inv_mem' := by
    intro a ah
    simp at *
    obtain ⟨u,⟨uh1,uh2⟩⟩ := ah
    use u⁻¹
    constructor
    exact (Subgroup.inv_mem_iff H).mpr uh1
    rw[uh2]
    group

/- Now let's prove that a group acts on its own subgroups by conjugation. -/

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by {
  ext g
  constructor
  intro gh
  obtain ⟨a,⟨ah1,ah2⟩⟩ := gh
  simp at ah2
  rw[ah2]
  assumption

  intro gh
  use g
  constructor
  · exact gh
  group
  }

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by {
  ext g
  constructor
  intro gh
  unfold conjugate
  simp
  obtain ⟨a,⟨ah1,ah2⟩⟩ := gh
  use y*a*y⁻¹
  constructor
  use a
  rw[ah2]
  group

  intro gh
  obtain ⟨a,⟨ah1,ah2⟩⟩ := gh
  unfold conjugate
  obtain ⟨b,⟨bh1,bh2⟩⟩ := ah1
  simp
  use b
  constructor
  assumption
  rw[ah2,bh2]
  group
  }


/- Saying that a group `G` acts on a set `X` can be done with `MulAction`.
The two examples below show the two properties that a group action must satisfy. -/
#print MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
example (g g' : G) (x : X) : (g * g') • x = g • (g' • x) := by exact mul_smul g g' x
example (x : X) : (1 : G) • x = x := by exact MulAction.one_smul x

/- Now show that `conjugate` specifies a group action from `G` onto its subgroups. -/
instance : MulAction G (Subgroup G) where
  smul := fun x H ↦ conjugate x H
  one_smul := conjugate_one
  mul_smul := conjugate_mul



/-! # Exercises to hand-in. -/


/- A `Setoid` is the name for an equivalence relation in Lean.
Let's define the smallest equivalence relation on a type `X`. -/
def myEquivalenceRelation (X : Type*) : Setoid X where
  r x y := x = y
  iseqv := {
    refl := by intro x; rfl
    symm := by
      intro x y xy
      exact id (Eq.symm xy)
    trans := by
      intro x y z xy yz
      rw[xy,yz]
  } -- Here you have to show that this is an equivalence.
                 -- If you click on the `sorry`, a lightbulb will appear to give the fields

/- This simp-lemma will simplify `x ≈ y` to `x = y` in the lemma below. -/
@[simp] lemma equiv_iff_eq (X : Type*) (x y : X) :
  letI := myEquivalenceRelation X; x ≈ y ↔ x = y := by rfl

/-
Now let's prove that taking the quotient w.r.t. this equivalence relation is
equivalent to the original type.

Use `Quotient.mk` to define a map into a quotient (or its notation `⟦_⟧`)
Use `Quotient.lift` to define a map out of a quotient.
Use `Quotient.sound` to prove that two elements of the quotient are equal.
Use `Quotient.ind` to prove something for all elements of a quotient.
You can use this using the induction tactic: `induction x using Quotient.ind; rename_i x`.
-/
def quotient_equiv_subtype (X : Type*) : Quotient (myEquivalenceRelation X) ≃ X where
      toFun := by
        apply Quotient.lift (fun (x:X)↦ (x:X))
        intro a b ab
        simp at ab
        assumption
      invFun := Quotient.mk (myEquivalenceRelation X)
      left_inv := by
        intro x
        induction x using Quotient.ind
        rfl
      right_inv := by
        intro x
        rfl


section GroupActions

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/- Below mulis the orbit of an element `x ∈ X` w.r.t. a group action by `G`.
Prove that the orbits of two elements are equal
precisely when one element is in the orbit of the other. -/
def orbitOf (x : X) : Set X := range (fun g : G ↦ g • x)

lemma orbitOf_eq_iff (x y : X) : orbitOf G x = orbitOf G y ↔ y ∈ orbitOf G x := by {
  constructor
  intro h
  have : y ∈ orbitOf G y := by
    use 1
    simp
  rw[← h] at this
  assumption

  intro h
  ext z
  constructor
  intro zh
  unfold orbitOf at *
  simp at *
  obtain ⟨t,ht⟩ := h
  obtain ⟨f,fh⟩ := zh
  use f * t⁻¹
  rw[← fh]
  rw[← ht]
  rw[mul_smul]
  simp

  intro zh
  unfold orbitOf at *
  simp at *
  obtain ⟨t,ht⟩ := h
  obtain ⟨f,fh⟩ := zh
  use f * t
  rw[mul_smul]
  rw[ht,fh]


  }

/- Define the stabilizer of an element `x` as the subgroup of elements
`g ∈ G` that satisfy `g • x = x`. -/
def stabilizerOf (x : X) : Subgroup G where
  carrier := {g : G | g • x = x}
  one_mem' := by
    dsimp
    exact MulAction.one_smul x
  inv_mem' := by
    dsimp
    intro a ah
    rw[← ah]
    rw[←mul_smul]
    simp
    rw[ah]
  mul_mem' := by
    dsimp
    intro a b ah bh
    rw[mul_smul]
    rw[bh,ah]

-- This is a lemma that allows `simp` to simplify `x ≈ y` in the proof below.
@[simp] theorem leftRel_iff {x y : G} {s : Subgroup G} :
    letI := QuotientGroup.leftRel s; x ≈ y ↔ x⁻¹ * y ∈ s :=
  QuotientGroup.leftRel_apply

/- Let's probe the orbit-stabilizer theorem.

Hint: Only define the forward map (as a separate definition),
and use `Equiv.ofBijective` to get an equivalence.
(Note that we are coercing `orbitOf G x` to a (sub)type in the right-hand side) -/

def orbit_stabilizer_theorem (x : X) : G ⧸ stabilizerOf G x ≃ orbitOf G x := by {
  --let f := fun (g : G) ↦ (g • x : X)
  --have h : range f ⊆ orbitOf G x := by
    --intro a ha
    --simp [orbitOf] at ha
    --exact ha

  let f : G → orbitOf G x := λ g => ⟨g • x, by {
  simp [orbitOf]
}⟩
  let g : G ⧸ stabilizerOf G x → orbitOf G x := Quotient.lift f




  --letI := myEquivalenceRelation X; x ≈ y ↔ x = y := by rfl
  --let m := by
    --apply Quotient.lift (fun (g : G) ↦ ((g • x): X))
    --intro a b ab
    --refine eq_inv_smul_iff.mp ?_
    --rw[← mul_smul]
    --??

  --have : range m ⊆ ↑(orbitOf G x)

  }


end GroupActions
