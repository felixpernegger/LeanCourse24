import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 5 (mostly section 2) and 6 (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 12.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- A note on definitions -/

lemma my_lemma : 3 + 1 = 4 := rfl
def myThree : ℕ := 3

/-
Tactics like `simp` and `rw` will not unfold definitions unless instructed to.
Tactics like `exact` and `apply` will unfold definitions if needed.
Uncomment the following lines one-by-one to see the difference. -/

example : myThree + 1 = 4 := by
  -- rw [my_lemma] -- fails
  -- simp [my_lemma] -- fails to use `my_lemma`
  -- exact my_lemma -- works
  -- apply my_lemma -- works
  -- rw [myThree, my_lemma] -- works after instructing `rw` to unfold the definition
  -- simp [myThree] -- works after instructing `simp` to unfold the definition
                    -- (it doesn't need `my_lemma` to then prove the goal)
  rw[myThree]


/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by {
  norm_cast at h
  rw[h]
  }

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by {
  norm_cast at *
  linarith
  }

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by {
  have :((↑m : ℝ) - 1) ^ 2 = (↑m^2:ℝ) -2*↑m + 1 := by ring;
  rw[this]
  have : ↑(n : ℝ) = (↑m : ℝ)^ 2 - 2 * (↑m : ℝ) := by
    norm_cast at h
    norm_cast
  linarith
  }

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by {
  norm_cast
  }

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by {
  norm_cast
  }

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by {
  gcongr
  norm_cast
  }

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by {
  apply Real.sqrt_pos.2
  norm_cast
  }

/- Working with `Finset` is very similar to working with `Set`.
However, some notation, such as `f '' s` or `𝒫 s` doesn't exist for `Finset`. -/
example (s t : Finset ℕ) : (s ∪ t) ∩ t = (s ∩ t) ∪ t := by {
  ext x
  constructor
  intro h
  apply Finset.mem_union_right
  exact Finset.mem_of_mem_inter_right h
  intro h
  apply Finset.mem_inter.2
  constructor
  apply Finset.mem_union.1 at h
  obtain c|c := h
  apply Finset.mem_union_right
  exact Finset.mem_of_mem_inter_right c
  apply Finset.mem_union_right
  exact c
  apply Finset.mem_union.1 at h
  obtain h|h := h
  exact Finset.mem_of_mem_inter_right h
  exact h
 }

example {α β : Type*} (f : α → β) (s : Finset α) (y : β) : y ∈ s.image f ↔ ∃ x ∈ s, f x = y := by {
  simp
  }

/- `Disjoint` can be used to state that two (fin)sets are disjoint.
Use `Finset.disjoint_left` (or `Set.disjoint_left`) to unfold its definition.
If you have `x ∈ t \ s` apply `simp` first to get a conjunction of two conditions.
-/
example {α : Type*} (s t : Finset α) : Disjoint s (t \ s) := by {
  intro x xh xhh
  intro e ex
  have rr: e ∈ s := by exact xh ex
  have r: e ∈ t \ s := by exact xhh ex
  apply Finset.mem_sdiff.1 at r
  obtain ⟨_,h⟩ := r
  contradiction
}


/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i in range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by {
  induction n with
  | zero =>
    simp
    rw[fibonacci]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have : fibonacci (2 * (n + 1))= fibonacci (2*n+1+1) := by ring
    rw[this,fibonacci]
    ring
  }

example (n : ℕ) : ∑ i in range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by {
  induction n with
  | zero =>
    simp
    rw[fibonacci]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rw[fibonacci]
    push_cast
    ring
  }

example (n : ℕ) : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw[mul_add, ih]
    ring
  }

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  induction n with
  | zero =>
    simp
    rw[fac,fac]
    linarith
  | succ n ih =>
    calc
      2 ^ (n+1) = 2 * (2 ^ n) := by ring
                _≤ 2 * (fac (n+1)) := by apply Nat.mul_le_mul; rfl; exact ih
                _≤ fac (n+1+1) := by nth_rw 2 [fac]; apply Nat.mul_le_mul; linarith; rfl
  }

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  induction n with
  | zero =>
    simp
    rw[fac]
  | succ n ih =>
    rw[Finset.prod_range_succ, ← ih]
    rw[fac]
    ring
  }

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw[Finset.prod_range_succ]
    calc
      fac (2 * (n+1)) = fac (2*n +1 +1) := by ring
        _=(2*n+1)*(2*n+2)* (fac (2*n)) := by rw[fac,fac];ring
        _=(2 * n + 1) * (2 * n + 2) * (fac n * 2 ^ n * ∏ i ∈ Finset.range n, (2 * i + 1)) := by rw[ih]
        _=(2 * n + 1) * 2* (n + 1) * (fac n) * 2 ^ n * ∏ i ∈ Finset.range n, (2 * i + 1) := by ring
        _=(2 * n + 1) * 2* (fac (n + 1)) * 2 ^ n * ∏ i ∈ Finset.range n, (2 * i + 1) := by rw[fac];ring
        _=(2 * n + 1) * (fac (n + 1)) * 2 ^ (n+1) * ∏ i ∈ Finset.range n, (2 * i + 1) := by ring
    ring
  }





/- **Exercise**.
Define scalar multiplication of a real number and a `Point`. -/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

-- give definition here

def scalar : Point → ℝ → Point
  | Point.mk x y z, (r : ℝ) => ⟨r*x, r*y, r*z⟩

def dotprod : Point → Point → ℝ
  | Point.mk x y z, Point.mk x' y' z' => (x * x' + y * y' + z * z')


/- **Exercise**.Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/
structure PythTriple where
  x : ℕ
  y : ℕ
  z : ℕ
  trip : x^2+y^2=z^2

lemma ktrip (G : PythTriple) (k : ℕ) : (k*G.x)^2+(k*G.y)^2=(k*G.z)^2 := by
  obtain ⟨x,y,z, h⟩ := G
  simp
  calc
    (k*x)^2+(k*y)^2=k^2*(x^2+y^2) := by ring
      _= k^2*(z^2) := by rw[h]
      _=(k*z)^2 := by ring

example (G: PythTriple) (k: ℕ): ∃G' : PythTriple, G'.x=k*G.x ∧ G'.y=k*G.y ∧ G'.z=k*G.z := by
  have h': (k*G.x)^2+(k*G.y)^2 = (k*G.z)^2 := by exact ktrip G k
  use PythTriple.mk (k*G.x) (k*G.y) (k*G.z) h'



-- give definition here

/- Prove that triples of equivalent types are equivalent. -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β := by
  obtain ⟨a,b,hb,ha⟩ := e
  use fun u ↦ Triple.mk (a u.x) (a u.y) (a u.z)
  use fun v ↦ Triple.mk (b v.x) (b v.y) (b v.z)
  intro p
  ext
  simp
  exact hb p.x
  exact hb p.y
  exact hb p.z
  intro p
  ext
  simp
  exact ha p.x
  exact ha p.y
  exact ha p.z



/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

example (G : Type*) [h: AbelianGroup' G] : AbelianGroup' (Triple G) := by
  obtain ⟨m,c,a,z,az,n,an⟩ := h
  use fun (Triple.mk x y z) (Triple.mk v r t) ↦ (Triple.mk (m x v) (m y r) (m z t))
  intro x y
  simp
  obtain ⟨x1,x2,x3⟩ := x
  obtain ⟨y1,y2,y3⟩ := y
  simp
  constructor
  exact c x1 y1
  constructor
  exact c x2 y2
  exact c x3 y3

  intro x y z
  obtain ⟨x1,x2,x3⟩ := x
  obtain ⟨y1,y2,y3⟩ := y
  obtain ⟨z1,z2,z3⟩ := z
  simp
  constructor
  exact a x1 y1 z1
  constructor
  exact a x2 y2 z2
  exact a x3 y3 z3

  use z
  use z
  use z
  simp
  intro x
  obtain ⟨x1,x2,x3⟩ := x
  simp
  constructor
  exact az x1
  constructor
  exact az x2
  exact az x3

  use fun (Triple.mk x y z) ↦ (Triple.mk (n x) (n y) (n z))
  intro x
  obtain ⟨x1,x2,x3⟩ := x
  simp
  constructor
  exact an x1
  constructor
  exact an x2
  exact an x3




/-! # Exercises to hand-in. -/

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

-- give the definition here
structure strict_bipointed_type where
  α : Type
  x : α
  y : α
  neq : x ≠ y

-- state and prove the lemma here
example (s : strict_bipointed_type) : ∀(z : s.α), (z ≠ s.x) ∨ (z ≠ s.y) := by
  intro z
  by_cases p: z = s.x
  right
  rw[p]
  exact s.neq
  left
  assumption

/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
--I use the proof from the lecture here as a lemma

open Finset in

lemma sum_ints (m : ℕ) :
   ∑ i ∈ Finset.range (m + 1), i = (↑m : ℚ) * ((↑m : ℚ) + 1) / 2 := by {
  induction m with
  | zero => simp
  | succ n ihh =>
    rw [Finset.sum_range_succ]
    push_cast at ihh
    push_cast; rw[ihh]
    field_simp
    ring
  }

lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i in range (n + 1), (i : ℚ) ^ 3) = (∑ i in range (n + 1), (i : ℚ)) ^ 2 := by {
  --I use the proof from the lecture here as a lemma
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    nth_rw 2 [Finset.sum_range_succ]
    simp
    symm
    have h (m:ℕ): ∑ i ∈ Finset.range (m + 1), ↑i = (↑m:ℚ)*((↑m : ℚ)+1)/2 := by
      induction m with
        | zero =>
          simp
        | succ m ih =>
          rw[Finset.sum_range_succ]
          rw[ih]
          field_simp
          ring
    rw[h]
    field_simp
    ring
  }

/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma disjoint_unions {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have h := wf.wf.has_min -- this hypothesis allows you to use well-orderedness
  constructor
  unfold Pairwise
  unfold Disjoint
  intro i j ij s si sj
  simp
  by_contra p
  push_neg at p
  obtain ⟨r,rs⟩ := p
  have ri: r ∈ C i := by exact si rs
  have rj: r ∈ C j := by exact sj rs
  rw[hC i] at ri
  rw[hC j] at rj
  obtain ⟨a1,a2⟩ := ri
  obtain ⟨b1,b2⟩ := rj
  by_cases o: i<j
  contrapose b2
  push_neg
  exact Set.mem_biUnion o a1

  simp at o
  have : j < i := by exact lt_of_le_of_ne o (id (Ne.symm ij))
  contrapose a2
  push_neg
  exact Set.mem_biUnion this b1

  ext x
  simp
  constructor
  intro hx
  obtain ⟨i,ih⟩ := hx
  use i
  rw[hC i] at ih
  obtain ⟨h,h'⟩ := ih
  assumption

  intro hx
  let W := {i : ι | x ∈ A i}
  have : W.Nonempty := by
    obtain ⟨i,ih⟩ := hx
    use i
    exact ih
  specialize h W this
  obtain ⟨q,qh⟩ := h
  use q
  rw[hC q]
  constructor
  exact qh.1
  by_contra h0
  obtain ⟨s,⟨l,sh2⟩,xh⟩ := h0
  simp at sh2
  obtain ⟨j,jh⟩ := sh2
  obtain ⟨o,⟨oh1,oh2⟩,oh3⟩ := xh
  simp at oh2
  obtain ⟨qh1,qh2⟩ := qh
  rw[← oh2] at oh3
  have : l ∈ W := by exact oh3
  specialize qh2 l this
  contradiction

  }



/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

lemma not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
  constructor
  intro np
  by_contra wrong
  push_neg at wrong
  have : Nat.Prime n := by
    rw[Nat.prime_def_lt]
    constructor
    by_contra t
    simp at t
    have : n = 0 ∨ n=1 := by
      refine le_one_iff_eq_zero_or_eq_one.mp ?_
      exact le_of_lt_succ t
    obtain ⟨a,b,_⟩ := wrong
    obtain h|h := this
    contradiction
    contradiction

    intro m mh mn
    obtain ⟨k,kh⟩ := mn
    obtain ⟨_,_,w⟩ := wrong
    by_contra m0
    by_cases p : m=0
    rw[p] at kh
    rw[zero_mul] at kh
    contradiction
    have g1: 2 ≤ m := by refine (two_le_iff m).mpr ?_; constructor; assumption;assumption

    have g2: 2 ≤ k := by
      by_contra u
      have : k=0 ∨ k=1 := by
        refine le_one_iff_eq_zero_or_eq_one.mp ?_
        exact Nat.le_of_not_lt u
      obtain h|h := this
      rw[h,mul_zero] at kh
      contradiction
      rw[h,mul_one] at kh
      rw[kh] at mh
      exact (lt_self_iff_false m).mp mh

    specialize w m k g1 g2
    contradiction
  contradiction
  intro h
  obtain h|h := h

  rw[Nat.prime_def_lt]
  simp
  intro h
  linarith
  obtain h|h := h
  rw[Nat.prime_def_lt]
  simp
  intro h0
  linarith
  rw[Nat.prime_def_lt]
  simp
  intro h0
  obtain ⟨a,b,ah,bh,h'⟩ := h
  use a
  constructor
  rw[h']
  refine (Nat.lt_mul_iff_one_lt_right ?h.left.ha).mpr bh
  linarith
  constructor
  rw[h']
  exact Nat.dvd_mul_right a b
  linarith


  }

lemma prime_of_prime_two_pow_sub_one (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by {
  by_contra h2n
  rw [not_prime_iff] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · simp at hn
    rw[Nat.prime_def_lt] at hn
    contradiction
  · simp at hn
    rw[Nat.prime_def_lt] at hn
    contradiction
  have h0: (2^a - 1) ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by
    refine Dvd.dvd.modEq_zero_int ?h
    rfl
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by
          gcongr
          rw [@npow_mul]
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by
        calc
          (2^a)^b - 1 ≡ ((2^a-1)+ 1)^b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by ring;rfl
            _≡ (0+1)^b -1 [ZMOD (2 : ℤ) ^ a - 1] := by
              apply Int.ModEq.sub_right 1
              refine Int.ModEq.pow b ?h
              exact Int.ModEq.add h0 rfl
            _≡ 1^b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by ring; rfl
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by rw[one_pow]; rfl
  have h2 : 2 ^ 2 ≤ 2 ^ a := by apply Nat.pow_le_pow_of_le; linarith; exact ha
  have h3 : 1 ≤ 2 ^ a := by exact Nat.one_le_two_pow
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    apply Nat.pow_lt_pow_of_lt
    linarith
    refine (Nat.lt_mul_iff_one_lt_right ?w.ha).mpr hb
    exact zero_lt_of_lt ha
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by
    apply Nat.pow_le_pow_of_le
    linarith
    exact Nat.zero_le (a * b)
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1 := by norm_cast at h
  rw [Nat.prime_def_lt] at hn
  obtain ⟨hn1,hn2⟩ := hn
  specialize hn2 (2 ^ a - 1) h5 h'
  contradiction
  }

/- Prove that for positive `a` and `b`, `a^2 + b` and `b^2 + a` cannot both be squares.
Prove it on paper first! -/
lemma not_isSquare_sq_add_or (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
  by_cases h: IsSquare (a ^ 2 +b)
  swap
  left
  assumption

  obtain ⟨k,hk⟩ := h
  by_contra t
  push_neg at t
  obtain ⟨_,⟨k',hk'⟩⟩ := t
  have kb : a < k := by
    by_contra h0
    simp at h0
    have : k*k < k*k := by
      calc
        k*k ≤ a*a := by exact Nat.mul_le_mul h0 h0
          _< a*a + b := by exact Nat.lt_add_of_pos_right hb
          _=a^2+b := by ring;
          _=k*k := by rw[hk]
    linarith
  have ka1 : a+1≤ k := by exact kb
  have bbig: a^2+2*a+1≤ a^2+b := by
    calc
      a ^2 + 2*a +1 = (a+1)*(a+1) := by ring
      _≤ k*k := by exact Nat.mul_le_mul kb kb
      _= a^2+b := by rw[hk]
  have b1 : 2*a+1≤ b := by exact Nat.le_of_add_le_add_left bbig
  clear bbig kb ka1

  have k'a : b < k' := by
    by_contra h0
    simp at h0
    have : k'*k' < k'*k' := by
      calc
        k'*k' ≤ b*b := by exact Nat.mul_le_mul h0 h0
          _< b*b + a := by exact Nat.lt_add_of_pos_right ha
          _=b^2+a := by ring;
          _=k'*k' := by rw[hk']
    linarith
  have k'b1 : b+1≤ k' := by exact k'a
  have abig: b^2+2*b+1≤ b^2+a := by
    calc
      b ^2 + 2*b +1 = (b+1)*(b+1) := by ring
      _≤ k'*k' := by exact Nat.mul_le_mul k'a k'a
      _= b^2+a := by rw[hk']
  have a1 : 2*b+1≤ a := by exact Nat.le_of_add_le_add_left abig
  clear abig k'a k'b1
  linarith
  }


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosReal : Type := {x : ℝ // 0 < x}

#check Group

def groupPosReal : Group PosReal :=
{
  mul := fun x y ↦ x * y
  mul_assoc := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  inv := fun a ↦ ⟨1 / a, div_pos zero_lt_one a.2⟩
  inv_mul_cancel := by
    intro a
    simp only [← one_div]
    have : (1 / (↑a:ℝ))*(↑a:ℝ)=1 := by
      refine one_div_mul_cancel ?h
      refine Ne.symm (_root_.ne_of_lt ?h.h)
      exact a.2
    show ⟨1 / a, div_pos zero_lt_one a.2⟩ * a = 1
    exact Eq.symm (Subtype.eq (id (Eq.symm this))) --wtf is this lol. I love exact? so much
}
/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] card_powerset
#check Finset.induction

lemma fintype_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (powerset s) = 2 ^ Finset.card s := by {
  induction s using Finset.induction with
  | empty => rfl
  | @insert x s hxs ih =>
    rw[Finset.powerset_insert]
    rw[Finset.card_union]
    rw[ih]
    have : s.powerset ∩ Finset.image (insert x) s.powerset = ∅ := by
      ext y
      constructor
      swap
      intro hy
      contradiction

      intro hy
      simp at hy
      obtain ⟨y1,y2⟩ := hy
      obtain ⟨a,⟨ah1,ah2⟩⟩ := y2
      have : x ∈ y ∧ x ∉ y := by
        constructor
        rw[← ah2]
        exact mem_insert_self x a
        exact fun a ↦ hxs (y1 a)
      obtain ⟨_, _⟩ := this
      contradiction
    rw[this]
    rw[Finset.card_empty]
    simp
    rw[Finset.card_insert_of_not_mem]
    have : 2 ^ (s.card + 1) = 2^ s.card + 2^ s.card := by ring
    rw[this]
    simp
    rw[Finset.card_image_of_injOn]
    exact ih
    swap
    exact hxs
    unfold InjOn
    intro a ah b bh h
    have xnota: x ∉ a := by
     exact not_mem_of_mem_powerset_of_not_mem ah hxs
    have xnotb: x ∉ b := by
     exact not_mem_of_mem_powerset_of_not_mem bh hxs
    ext t
    constructor
    intro ta
    have : t ∈ insert x a := by exact Finset.mem_insert_of_mem ta
    rw[h] at this
    simp at this
    obtain h0|h0 := this
    rw[h0] at ta
    contradiction
    exact h0
    intro tb
    have : t ∈ insert x b := by exact Finset.mem_insert_of_mem tb
    rw[← h] at this
    simp at this
    obtain h0|h0 := this
    rw[h0] at tb
    contradiction
    exact h0
    --that was an adventure
 }
