import LeanCourse.Project.Auxiliary
import Mathlib

open Function Set Classical

noncomputable section


/- In this rather short section, we introduce reflections along points and lines.
Nothing too spectacular, but never the less good to have.-/

/-Notation: reflection_object1_object2 mean we reflect object2 along object1.
We do all cases except object1 being a circle:
The respective reflection would be inversion, but that would be too much and hard too define for now-/

def reflection_point_point: Point → Point → Point :=
  fun a b ↦ padd (p_scal_mul 2 b) (pneg a)
--so just 2*b-a

/-This does nothing too surprising:-/
@[simp] lemma reflection_point_point_self (a : Point): reflection_point_point a a = a := by{
  unfold reflection_point_point padd p_scal_mul pneg
  ext
  simp
  ring
}

lemma reflection_point_point_same_imp_same {a b : Point}(h : a = reflection_point_point a b): a = b := by{
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  unfold reflection_point_point padd pneg p_scal_mul at h
  simp at *
  have s1:  ({ re := a1, im := a2 }:ℂ).re = (2 * { re := b1, im := b2 } + -({ re := a1, im := a2 } : ℂ)).re := by{
    nth_rw 1[h]
  }
  simp at s1
  have s2:  ({ re := a1, im := a2 }:ℂ).im = (2 * { re := b1, im := b2 } + -({ re := a1, im := a2 } : ℂ)).im := by{
    nth_rw 1[h]
  }
  simp at s2
  constructor
  linarith
  linarith
}

@[simp] lemma reflection_point_point_twice (a b : Point) : reflection_point_point (reflection_point_point a b) b  = a := by{
  ext
  unfold reflection_point_point padd pneg p_scal_mul
  simp
}

/-Reflecting a point along a line is the same as reflection along the foot-/

def reflection_point_line: Point → Line → Point :=
  fun a L ↦ reflection_point_point (foot a L)
