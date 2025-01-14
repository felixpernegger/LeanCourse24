import LeanCourse.Project.Ceva
import Mathlib

open Function Set Classical

noncomputable section

set_option linter.unusedTactic false

/-In this file, we first introduce rotations (really not that much) and then
angle_bisectors (more that "not that much")-/

/-Defining rotations with lines is, like with angles, problematic, because
there are basically always 2 directions you can go. We therefore do it with points:-/
/-Rotate Point a along b with Angle α:-/
#check Angle
def rot_point : Point → Point → ℝ → Point :=
  fun a b α ↦ Point.mk (b.x + (a.x-b.x)*(Complex.exp (α * Complex.I)))

/-This really has the Angle we want:-/

lemma rot_point_angle{a b : Point}(α : ℝ)(ab: a ≠ b): Angle (rot_point a b α) b a = α := by{
  unfold rot_point Angle
  field_simp [sub_neq_zero ab]
  rw [Complex.arg_exp_mul_I]
  simp
}

lemma rot_point_self(a : Point)(α : ℝ): rot_point a a α = a := by{
  unfold rot_point
  simp
}

/-If a ≠ b, the rot_point isn't b:-/
lemma center_neq_rot_point{a b : Point}(α : ℝ)(ab : a ≠ b): b ≠ rot_point a b α := by{
  contrapose ab
  unfold rot_point at ab
  simp at *
  have : b.x = ({ x := b.x + (a.x - b.x) * Complex.exp (↑α * Complex.I) } : Point).x := by{
    rw[← ab]
  }
  simp at this
  ext
  calc
    a.x = a.x - (a.x - b.x) := by{rw[this, sub_zero]}
      _= b.x := by{ring}
}

/-With this we get roation of lines:-/

def rot_line : Point → Point → ℝ → Line :=
  fun a b α ↦ qLine_through b (rot_point a b α)

lemma rot_line_self(a : Point)(α : ℝ): rot_line a a α = qLine_through a a := by{
  unfold rot_line
  rw[rot_point_self]
}

/-b lies on the rotated line:-/

lemma center_lies_on_rot_line(a b : Point)(α : ℝ): Lies_on b (rot_line a b α) := by{
  unfold rot_line
  exact qline_through_mem_left b (rot_point a b α)
}

/-With that, we now define the Angle bisector:-/

def Angle_bisector : Point → Point → Point → Line :=
  fun a b c ↦ rot_line a b ((Angle a b c)/2)
