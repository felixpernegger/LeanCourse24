import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import LeanCourse.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x xh
  obtain xh1|xh2 := xh
  obtain ⟨xs,xt⟩ := xh1
  constructor
  exact xs
  left
  exact xt

  obtain ⟨xs,xu⟩ := xh2
  constructor
  exact xs
  right
  exact xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x xh
  have xs: x∈ s := xh.1
  have xntu: x ∉ t ∪ u := xh.2
  constructor
  constructor
  exact xs
  intro xt
  have : x∈ t ∪ u := by exact mem_union_left u xt
  contradiction
  intro xu
  have : x∈ t∪ u := by exact mem_union_right t xu
  contradiction

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun x ⟨xs,xt⟩ ↦ ⟨xt,xs⟩) (fun x ⟨xt,xs⟩ ↦ ⟨xs,xt⟩)
example : s ∩ (s ∪ t) = s := by
  apply subset_antisymm
  exact inter_subset_left

  apply subset_inter_iff.2
  constructor
  apply subset_refl
  exact subset_union_left

example : s ∪ s ∩ t = s := by
  apply subset_antisymm
  apply union_subset_iff.2
  constructor
  rfl
  apply inter_subset_left

  apply subset_union_left

example : s \ t ∪ t = s ∪ t := by
  ext x
  simp only [mem_union]
  constructor
  intro h
  obtain h1|h2 := h
  left
  exact h1.1
  right
  exact h2

  intro h
  obtain h1|h2 := h
  by_cases p: x∈ t
  right
  exact p
  left
  exact ⟨h1,p⟩

  right
  exact h2



example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  simp only [mem_diff, mem_union, mem_inter]
  constructor
  intro h
  obtain h1|h2 := h
  constructor
  left
  exact h1.1
  intro h0
  have : x∈ t := by exact mem_of_mem_inter_right h0
  obtain ⟨a1,a2⟩ := h1
  contradiction

  constructor
  right
  exact h2.1
  intro h0
  have : x∈s := by exact mem_of_mem_inter_left h0
  obtain ⟨a1,a2⟩ := h2
  contradiction

  intro h
  by_cases p: x ∈ s
  left
  constructor
  exact p
  obtain ⟨h1,h2⟩ := h
  intro h0
  have : x∈ s ∩ t := by exact mem_inter p h0
  contradiction

  right
  constructor
  obtain ⟨h1,h2⟩ := h
  obtain a1|a2 := h1
  contradiction
  exact a2
  exact p

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro np
  intro n2
  apply Nat.Prime.eq_two_or_odd at np
  obtain h1|h2 := np
  · exfalso
    linarith
  · apply Nat.odd_iff.2
    exact h2


#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  have: x ∈ t := by exact ssubt xs
  constructor
  exact h₀ x this
  exact h₁ x this

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  obtain ⟨x,xs,_,xp⟩ := h
  have: x ∈ t := by exact ssubt xs
  use x

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  intro h
  obtain h|h := h
  · intro i
    right
    exact h
  intro i
  left
  exact h i

  intro h
  by_cases p: x ∈ s
  left
  exact p
  right
  intro i
  specialize h i
  obtain h|h := h
  · exact h
  contradiction




def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨p,hp⟩ := Nat.exists_infinite_primes x
  simp
  use p
  exact And.symm hp

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
