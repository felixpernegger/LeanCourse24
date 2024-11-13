import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Set Nat
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 4, sections 2, 3.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 5.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- Do the exercises about sets from last exercise set, if you haven't done them because
we didn't cover the material in class yet. -/


variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by {
  constructor
  intro h t
  rw[h]
  trivial

  intro h
  ext x
  constructor
  intro xh
  trivial
  intro _
  apply h x
  }


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  by_contra o
  push_neg at o
  obtain ⟨o1,o2⟩ := o
  contradiction
  }

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (123 + 32 * 3, (x + y) ^ 2) = (219, x ^ 2 + 2 * x * y + y ^ 2) := by {
    ext
    norm_num
    ring
  }

/- `A ≃ B` means that there is a bijection from `A` to `B`.
So in this exercise you are asked to prove that there is a bijective correspondence between
  functions from `ℤ × ℕ` to `ℤ × ℤ`
and
  functions from `ℕ` to `ℕ`
This is an exercise about finding lemmas from the library.
Your proof is supposed to only combine results from the library,
you are not supposed to define the bijection yourself.
If you want, you can use `calc` blocks with `≃`. -/
example : (ℤ × ℕ → ℤ × ℤ) ≃ (ℕ → ℕ) := by {
  calc
    (ℤ × ℕ → ℤ × ℤ) ≃ (ℤ × ℤ → ℤ × ℤ) := by apply Equiv.arrowCongr; apply Equiv.prodCongr; rfl; exact Equiv.intEquivNat.symm; rfl
      _ ≃ (ℤ → ℤ × ℤ) := by apply Equiv.arrowCongr; exact Denumerable.pair; rfl
      _≃ (ℤ → ℤ) := by apply Equiv.arrowCongr; rfl; exact Denumerable.pair
      _≃ (ℕ → ℤ) := by apply Equiv.arrowCongr; exact Equiv.intEquivNat; rfl
      _≃ (ℕ → ℕ) := by apply Equiv.arrowCongr; rfl; exact Equiv.intEquivNat
  }

/- Prove a version of the axiom of choice Lean's `Classical.choose`. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by {
  let f : ι → α := fun (i : ι) ↦ if h : ∃ y, y ∈ C i then Classical.choose h else x
  use f
  intro i
  unfold f
  specialize hC i
  rw[dif_pos hC]
  apply Classical.choose_spec hC
  }
#check Classical.choose

/-! # Exercises to hand-in. -/


/- ## Converging sequences

Prove two more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma sequentialLimit_reindex {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
  unfold SequentialLimit
  intro ε εh
  simp
  obtain ⟨m,hm⟩ := hs ε εh
  obtain ⟨p,hp⟩ := hr m
  use p
  intro n hn
  apply hm
  apply hp
  exact hn
  }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma sequentialLimit_squeeze {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
  intro ε εh
  obtain ⟨n, hn⟩ := hs₁ ε εh
  obtain ⟨m, hm⟩ := hs₃ ε εh
  let M := max n m
  use M
  intro k hk
  apply abs_lt.2
  have t₁ : abs (s₁ k - a) < ε := by
    apply hn
    calc
      k ≥ M := by exact hk
      _= max n m := rfl
      _≥ n := by exact Nat.le_max_left n m
  have t₃ : abs (s₃ k - a) < ε := by
    apply hm
    calc
      k ≥ M := by exact hk
      _= max n m := rfl
      _≥ m := by exact Nat.le_max_right n m
  constructor
  calc
    s₂ k - a ≥ s₁ k -a := by exact tsub_le_tsub_right (hs₁s₂ k) a
      _> -ε := by exact neg_lt_of_abs_lt t₁
  calc
    s₂ k - a ≤  s₃ k - a := by exact tsub_le_tsub_right (hs₂s₃ k) a
      _< ε := by exact lt_of_abs_lt t₃

  }

/- ## Sets -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
  ext x
  constructor
  intro h
  apply (mem_image f (s ∩ f ⁻¹' t) x).2 --you could also do simp (or before) but I want to do it without
  obtain ⟨hs,ht⟩ := h
  apply (mem_image f s x).1 at hs
  obtain ⟨y,⟨ys,yx⟩⟩ := hs
  use y
  constructor
  constructor
  exact ys
  apply mem_preimage.2
  rw[yx]; exact ht
  exact yx

  intro h
  apply (mem_image f (s ∩ f ⁻¹' t) x).1 at h
  obtain ⟨y,⟨⟨ys,yt⟩,yx⟩⟩ := h
  constructor
  use y
  rw[← yx]
  exact yt

  }

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {
  ext x
  have t: (16:ℝ) = 4^2 := by norm_num
  rw[t]
  simp
  constructor
  intro h
  apply sq_le_sq.1 at h
  apply le_abs.1 at h
  simp at h
  obtain h|h :=h
  right; exact h
  left; linarith

  intro h
  apply sq_le_sq.2
  simp
  apply le_abs.2
  obtain h|h:=h
  · right;linarith
  · left;exact h
  }


/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {
  let g : (β → α) := fun (b : β) ↦ if h : ∃ a ∈ s, f a = b then Classical.choose h else default
  use g
  unfold LeftInvOn
  intro x xs
  have an: ∃ a, a ∈ s ∧ f a = f x := by
    use x
  apply hf
  unfold g
  rw[dif_pos an]
  exact (Classical.choose_spec an).1
  exact xs
  simp [g]
  rw[dif_pos an]
  exact (Classical.choose_spec an).2
  }
--let f : ι → α := fun (i : ι) ↦ if h : ∃ y, y ∈ C i then Classical.choose h else default

/- Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

To help you along the way, some potentially useful ways to reformulate the hypothesis are given. -/

-- This lemma might be useful.
#check Injective.eq_iff

lemma set_bijection_of_partition {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by {
  -- h1' and h1'' might be useful later as arguments of `simp` to simplify your goal.
  have h1' : ∀ x y, f x ≠ g y := by
    by_contra h0
    push_neg at h0
    obtain ⟨x,y,yx⟩ := h0
    have : f x ∈ range f ∩ range g := by
      simp
      use y
      rw[yx]
    rw[h1] at this
    contradiction

  have h1'' : ∀ y x, g y ≠ f x := by
    by_contra h0
    simp at h0
    obtain ⟨y,x,yx⟩ := h0
    have : f x ∈ range f ∩ range g := by
      simp
      use y
    rw[h1] at this
    contradiction
  have h2' : ∀ x, x ∈ range f ∪ range g := by
    rw[h2]
    intro x
    trivial
  let L : Set α × Set β → Set γ := fun ((s,t) : (Set α × Set β)) ↦ f '' (s) ∪ g '' (t)
  /- Sorry for what is coming next-/
  let R : Set γ → Set α × Set β := fun u ↦ (f⁻¹'(range f ∩ u), g⁻¹'(range g ∩ u))
  use L, R
  constructor
  ext t mt
  constructor
  simp
  intro mh
  unfold L at mh
  unfold R at mh
  simp at mh
  obtain ⟨x,h⟩|⟨x,h⟩ := mh
  rw[← h.2]
  exact h.1
  rw[← h.2]
  exact h.1

  intro h
  simp at h
  simp
  unfold L; unfold R; simp
  by_cases r: mt ∈ range f
  left
  obtain ⟨x,xh⟩ := r
  use x
  repeat rw[xh]
  exact ⟨h,rfl⟩

  right
  have : mt ∈ range f ∪ range g := by
    rw[h2]
    trivial
  obtain p|p := this
  contradiction
  obtain ⟨x,xh⟩ := p
  use x
  rw[xh]
  exact ⟨h,rfl⟩

  ext s sm
  unfold L; unfold R; simp
  constructor
  intro h
  obtain ⟨x,⟨xh1,xh2⟩⟩|⟨x,⟨xh1,xh2⟩⟩ := h
  apply hf at xh2
  rw[← xh2]
  exact xh1

  have : g x ∈ range f ∩ range g := by
    constructor
    rw[xh2]
    unfold range
    use sm
    unfold range
    use x
  rw[h1] at this
  contradiction

  intro h
  left
  use sm

  unfold L; unfold R; simp
  constructor
  intro h
  obtain ⟨x,⟨xh1,xh2⟩⟩|⟨x,⟨xh1,xh2⟩⟩ := h
  have : f x ∈ range f ∩ range g := by
    constructor
    use x
    rw[xh2]
    use sm
  rw[h1] at this
  contradiction

  apply hg at xh2
  rw[xh2] at xh1
  exact xh1

  intro h
  right
  use sm
  }