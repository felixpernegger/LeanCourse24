import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real Function Set Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 2, 3, 5, 6.
  Read chapter 4, section 1.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 29.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example {p : ℝ → Prop} (h : ∀ x, p x) : ∃ x, p x := by {
  specialize h 1
  use 1
  }


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by {
  intro h0
  obtain ⟨a,ha⟩ := h0
  use a
  exact h a ha
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by {
  constructor
  intro h a pa
  have : ∃ x, p x := by use a
  exact h this

  intro h h'
  obtain ⟨a,ah⟩ := h'
  exact h a ah
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by {
  constructor
  intro h
  obtain ⟨a,ah⟩ := h
  constructor
  use a
  exact ah.1
  exact ah.2

  intro h
  obtain ⟨a,ah⟩ := h.1
  use a
  constructor
  exact ah
  exact h.2
  }

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
  constructor
  intro h
  obtain ⟨b,bh⟩ := h
  by_contra a
  specialize a b
  contradiction

  intro h
  contrapose h
  simp
  intro a ah
  contrapose h
  simp
  use a


  }

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by {
  intro ε εh
  use 1
  intro n n1;
  simp
  exact εh
  }

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m k : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by {
  calc
    (n)! ∣ (m)! := by exact factorial_dvd_factorial h
      _∣ (m+1) * (m)! := by exact Nat.dvd_mul_left m ! (m + 1)
      _= (m+1)! := rfl
  }

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by {
  intro x xh
  obtain ⟨y,yh⟩ := xh
  have h': f (y) ∈ s := by
    exact yh.1
  rw[yh.2] at h'
  exact h'
  }

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by {
  intro x xh
  obtain ⟨a,ah⟩ := h x
  have: a∈ f⁻¹' s := by
    simp
    rw[ah]
    exact xh
  rw[← ah]
  exact mem_image_of_mem f this
  }

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
  intro x xh
  obtain ⟨a,ah⟩ := xh.1
  obtain ⟨b,bh⟩ := xh.2
  have : a=b := by
    apply h
    rw[ah.2,← bh.2]
  rw[← this] at bh
  have : a∈ s∩t := by
    constructor
    exact ah.1
    exact bh.1
  rw[← ah.2]
  exact mem_image_of_mem f this
  }

example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  apply subset_antisymm
  intro x xh
  obtain ⟨y,yh⟩ := xh
  have ⟨yh1, yh2⟩ := yh
  obtain ⟨j,jh,jh'⟩ := yh1
  simp at jh
  have h: f y ∈ f '' (j) := by
    exact mem_image_of_mem f jh'
  rw[yh2] at h
  obtain ⟨z,zh⟩ := jh
  rw[← zh] at h
  exact mem_iUnion_of_mem z h

  intro x xh
  obtain ⟨a,ah⟩ := xh
  simp at ah
  have ⟨ah1,ah2⟩ := ah
  obtain ⟨z, zh⟩ := ah1
  rw[← zh] at ah2
  have h'': A z ⊆ ⋃ i, A i := by exact subset_iUnion_of_subset z fun ⦃a⦄ a ↦ a
  have: f '' A z ⊆ f '' ⋃ i, A i := by exact image_mono h''
  exact this ah2





example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by {
  apply subset_antisymm
  intro y yh
  obtain ⟨x, xh⟩ := yh
  simp at xh
  rw[← xh]
  simp
  exact sq_nonneg x

  intro y yh
  simp at *
  use sqrt y
  exact sq_sqrt yh
  }

end Set

/-! # Exercises to hand-in. -/


/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
  constructor
  intro h
  obtain ⟨a,ah⟩ := h
  obtain h'|h' := ah
  left
  use a
  right
  use a

  intro h
  obtain h'|h' := h
  obtain ⟨a,ah⟩ := h'
  use a
  left
  assumption

  obtain ⟨a,ah⟩ := h'
  use a
  right
  assumption

  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by {
  constructor
  intro h
  intro z
  obtain ⟨u, uh⟩ := h z
  simp at uh
  use f u

  intro h
  intro z
  obtain ⟨y,yh⟩ := h z
  obtain ⟨x,xh⟩ := hf y
  use x
  simp
  rw[xh,yh]
  }

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {
  intro y
  simp
  ring
  obtain ⟨a,ah⟩ := hf ((y - (1:ℝ) ) / (2:ℝ))
  use ((a-(12:ℝ)) / (3:ℝ))
  ring
  rw[ah]
  ring

  }

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  by_contra h0
  let R := {x | x ∉ f x}
  obtain ⟨r, hr⟩ := h0 R

  by_cases p: r ∈ R
  have : r ∉ f r := by
      exact p
  rw[hr] at this
  contradiction

  have : r ∈ R := by rw[← hr] at p; exact p
  contradiction
  }

end Surjectivity

/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {
  intro ε  εh
  have : ε /2 > 0 := by linarith
  obtain ⟨N₁,hN₁⟩ := hs (ε / 2) this
  obtain ⟨N₂,hN₂⟩ := ht (ε / 2) this
  let M := max N₁ N₂
  use M
  intro n hn
  simp
  calc
    |s n + t n - (a + b)| = abs ((s n - a) + (t n - b)) := by ring
    _≤ abs (s n -a) + abs (t n -b) := by exact abs_add_le (s n - a) (t n - b)
    _< ε / 2 + ε /2 := by
      gcongr
      apply hN₁
      exact le_of_max_le_left hn
      apply hN₂
      exact le_of_max_le_right hn
    _=ε := by ring
  }

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by {
  by_cases p : c = 0;
  rw[p]
  ring
  intro ε hε
  use 1
  intro n hn
  ring
  rw[abs_zero]
  exact hε

  intro ε hε
  have : ε/(abs (c)) > 0 := by
    apply div_pos
    exact hε
    apply abs_pos.2
    exact p
  obtain ⟨M, hM⟩ := hs (ε/(abs (c))) this
  use M
  simp
  intro n hn
  calc
    abs (c * s n - c * a) = abs (c * (s n - a)) := by ring
      _=abs (c) * abs (s n - a) := by apply abs_mul
      _< abs (c) * (ε / (abs c)) := by gcongr; apply hM n hn
      _=ε := by field_simp
  }





section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by {
  intro k
  simp
  use k
  intro n hn
  gcongr
  }

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by {
  intro k
  obtain ⟨N₁,hN₁⟩ := h₁ k
  obtain ⟨N₂,hN₂⟩ := h₂ k
  let M := max N₁ N₂
  use M
  intro n hn
  calc
    k * (t₁ + t₂) n = k * ((t₁ n) + (t₂ n)) := by rfl
      _= k * t₁ n + k* t₂ n := by ring
      _≤ (s₁ n) + (s₂ n) := by
        refine Nat.add_le_add ?h₁ ?h₂
        apply hN₁
        exact le_of_max_le_left hn
        apply hN₂
        exact le_of_max_le_right hn
      _= (s₁ + s₂) n := by rfl
  }

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  use (fun n ↦ n^n)
  simp
  intro k
  use k;
  intro n hn
  simp
  calc
    (n+1)^(n+1) ≥ n^(n+1) := by gcongr; linarith
      _=n^n*n := by congr
      _=n*n^n := by rw[mul_comm]
      _≥ k*n^n := by exact Nat.mul_le_mul_right (n ^ n) hn
    }

end Growth
