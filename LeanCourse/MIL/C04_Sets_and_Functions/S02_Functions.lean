import LeanCourse.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro sv x xs
  show f x ∈ v
  have : f x ∈ f '' s := by exact mem_image_of_mem f xs
  exact mem_of_subset_of_mem sv this

  intro sv x xs
  obtain ⟨y,ys,yx⟩ := xs
  have : f y ∈ v := by
    show y ∈ f⁻¹' v
    exact sv ys
  rw[yx] at this
  assumption

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x xs
  obtain ⟨y,yis,yx⟩ := xs
  apply h at yx
  rw[← yx]
  assumption

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x xu
  obtain ⟨y,yu,yx⟩ := xu
  have : f y ∈ u := yu
  rw[yx] at this
  assumption

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x xu
  obtain ⟨y, yx⟩ := h x
  rw[← yx]
  apply mem_image_of_mem
  rw[← yx] at xu
  exact xu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x xs
  obtain ⟨y, ys, yx⟩ := xs
  rw[← yx]
  apply mem_image_of_mem
  exact h ys

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x xu
  have : f x ∈ u := xu
  show f x ∈ v
  exact h this

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  intro h
  have : f x ∈ u ∪ v := h
  obtain t|t := h
  left
  assumption
  right
  assumption

  intro h
  show f x ∈ u ∪ v
  obtain p|p := h
  left
  exact p
  right
  exact p



example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x xst
  obtain ⟨y, yst, yx⟩ := xst
  rw[← yx]
  have ys: y ∈ s := by exact mem_of_mem_inter_left yst
  have yt: y ∈ t := by exact mem_of_mem_inter_right yst
  apply mem_image_of_mem at ys
  apply mem_image_of_mem at yt
  exact mem_inter ys yt




example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x xw
  obtain ⟨xfs, xft⟩ := xw
  obtain ⟨y,ys,yx⟩ := xfs
  obtain ⟨z,zt,zx⟩ := xft
  have : z= y:= by
    rw[← yx] at zx
    apply h zx
  rw[this] at zt
  rw[← yx]
  apply mem_image_of_mem
  apply mem_inter ys zt

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x ⟨x1,x2⟩
  obtain ⟨y,ys,yx⟩ := x1
  rw[← yx]; rw[← yx] at x2
  have h1: y ∉ t := by
    by_contra o
    have : f y ∈ f '' t := by apply mem_image_of_mem _ o
    contradiction
  apply mem_image_of_mem
  exact mem_diff_of_mem ys h1

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x ⟨xh1,xh2⟩
  show f x ∈ u \ v
  have h1: f x ∈ u := xh1
  have h2: f x ∉ v := xh2
  exact mem_diff_of_mem xh1 xh2


example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  intro h
  obtain ⟨y, ysv, yx⟩ := h.1
  have : x∈ v := h.2
  rw[← yx]
  rw[← yx] at this
  apply mem_image_of_mem
  constructor
  exact ysv
  exact this

  intro h
  obtain ⟨z,zw,zx⟩ := h
  rw[← zx]
  constructor
  apply mem_image_of_mem
  exact zw.1
  exact zw.2

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x xh
  obtain ⟨y,yw,yx⟩ := xh
  rw[← yx]
  constructor
  apply mem_image_of_mem
  exact yw.1
  exact yw.2

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨xs,xpu⟩
  show f x ∈ f '' s ∩ u
  have h1: f x ∈ u := by exact xpu
  have h2: f x ∈ f '' s := by exact mem_image_of_mem f xs
  exact mem_inter h2 h1

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x h
  obtain h|h := h
  · show f x ∈ f '' s ∪ u
    left
    apply mem_image_of_mem f h
  · right
    exact h

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  constructor
  intro h
  obtain ⟨y,yw,yx⟩ := h
  obtain ⟨a,⟨b,d⟩,c⟩ := yw
  simp at d
  rw[← d] at c
  simp only [mem_iUnion]
  use b
  rw[← yx]
  apply mem_image_of_mem
  exact c

  intro xh
  simp only [mem_iUnion] at xh
  obtain ⟨j,jh⟩ := xh
  show ∃ z ∈ ⋃ i, A i, f z = x
  obtain ⟨r, hr1,hr2⟩ := jh
  use r
  constructor
  exact mem_iUnion_of_mem j hr1
  exact hr2

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro x xh
  obtain ⟨y,yw,yx⟩ := xh
  simp only [mem_iInter] at *
  intro j
  specialize yw j
  rw[← yx]
  apply mem_image_of_mem
  exact yw


example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x xh
  simp only [mem_iInter] at xh
  show ∃ z ∈ ⋂ i, A i, f z = x
  have h1: x ∈ f '' A i := by
      exact xh i
  obtain ⟨z,zh⟩ := h1
  use z
  constructor
  simp only [mem_iInter]
  by_contra u
  push_neg at u
  obtain ⟨j, jh⟩ := u
  specialize xh j
  obtain ⟨a,aj,ax⟩ := xh
  obtain ⟨z1,z2⟩ := zh
  have : a = z := by
    have o: f a = f z := by
      calc
        f a = x := by exact ax
          _= f z := by rw[z2]
    exact injf o
  rw[this] at aj
  contradiction
  exact zh.2






example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  intro hx
  have : f x ∈ ⋃ i, B i := by exact hx
  apply mem_iUnion.1 at this
  obtain ⟨j,jh⟩ := this
  apply mem_iUnion.2
  use j
  exact jh

  intro h
  simp at h
  obtain ⟨j,hj⟩ := h
  show f x ∈  ⋃ i, B i
  apply mem_iUnion.2
  use j

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor
  intro xh
  simp only [mem_preimage] at xh
  apply mem_iInter.2
  intro j
  simp only [mem_preimage]
  simp only [mem_iInter] at xh
  specialize xh j
  assumption

  intro xh
  simp only [mem_iInter, mem_preimage] at xh
  simp only [mem_preimage, mem_iInter]
  assumption

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos
  intro e
  calc
    x = (√ (x) )^2 := by exact Eq.symm (sq_sqrt xpos)
    _= (√ y)^2 := by rw[e]
    _= y := by exact sq_sqrt ypos

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xh y yh
  intro e
  simp at e
  calc
    x = √ (x ^ 2) := by exact Eq.symm (sqrt_sq xh)
      _= √ (y ^ 2) := by  rw[e]
      _= y := by exact sqrt_sq yh

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext z; constructor
  intro ⟨x,⟨xh1,xh2⟩⟩
  rw[← xh2]
  apply sqrt_nonneg

  intro zpos
  use z^2
  constructor
  exact sq_nonneg z
  rw[sqrt_sq zpos]


example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x; constructor
  intro ⟨y,yh⟩
  rw[← yh]
  exact sq_nonneg y

  intro xpos
  use √ (x)
  apply sq_sqrt xpos

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  intro h
  intro x
  let y := inverse f (f x)
  have : f y = f x := by
    calc
      f y = f (inverse f (f x)) := rfl
      _= f x := by apply inverse_spec; use x
  apply h this

  intro h
  intro x y xy
  calc
    x = (inverse f) (f x) := by exact id (Eq.symm (h x))
      _= (inverse f) (f y) := by rw[xy]
      _= y := by exact h y

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  intro h
  intro x
  obtain ⟨y, yh⟩ := h x
  apply inverse_spec
  use y

  intro h
  intro x
  use inverse f x
  exact h x

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  exact h₁
  have h₃ : j ∉ S
  rw[h] at h₁
  exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
