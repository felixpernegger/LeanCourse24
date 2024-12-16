import LeanCourse.Project.Powpoint
import Mathlib

open Function Set Classical

noncomputable section


--Angles

#check Complex.arg

/-We now FINALLY deifne angles (I pretty much did everything you can reasonably do without angles lol)-/

/-We will use angles only as directed angles, furthermore, for the time being,
we only define angles between three points. Definining angles between lines is a bit tricky.

We will also make two versions of angles, seen as followed:
-/
#check Complex.arg_mul_coe_angle
#check Real.Angle
def Angle{a b c : Point}(ha : a ≠ b)(hc : c ≠ b): Real.Angle :=
  Complex.arg ((a.x-b.x)/(c.x-b.x))

def qAngle(a b c : Point): Real.Angle :=
  if ha : a ≠ b then (if hc : c ≠ b then (Angle ha hc) else 0) else 0

@[simp] lemma qangle_simp{a b c : Point}(ha : a ≠ b)(hc : c ≠ b): qAngle a b c = Angle ha hc := by{
  unfold qAngle
  simp [*]
}

@[simp] lemma qangle_simp_left(a b c : Point)(ha : a = b): qAngle a b c = 0 := by{
  unfold qAngle
  simp [*]
}

@[simp] lemma qangle_simp_left'(a b c : Point)(ha : b = a): qAngle a b c = 0 := by{
  unfold qAngle
  simp [*]
}

@[simp] lemma qangle_simp_right(a b c : Point)(ha : c = b): qAngle a b c = 0 := by{
  unfold qAngle
  simp [*]
}

@[simp] lemma qangle_simp_right'(a b c : Point)(ha : b = c): qAngle a b c = 0 := by{
  unfold qAngle
  simp [*]
}

/-We prove several elementary but very important properties:-/

lemma angle_self{a b : Point}(ha : a ≠ b): Angle ha ha = 0 := by{
  have asub : a.x-b.x ≠ 0 := by{exact sub_neq_zero ha}
  unfold Angle
  field_simp
}

lemma qangle_self(a b : Point): qAngle a b a = 0 := by{
  by_cases ha: a ≠ b
  · simp [*]
    exact angle_self ha
  simp at ha
  simp [*]
}

lemma angle_add{a b c d : Point}(ha : a ≠ b)(hc : c ≠ b)(hd : d ≠ b): Angle ha hd = Angle ha hc + Angle hc hd := by{
  unfold Angle
  have asub: a.x - b.x ≠ 0 := by{exact sub_neq_zero ha}
  have csub: c.x - b.x ≠ 0 := by{exact sub_neq_zero hc}
  have dsub: d.x - b.x ≠ 0 := by{exact sub_neq_zero hd}
  have rr: (a.x - b.x)/(d.x-b.x) = ((a.x-b.x)/(c.x-b.x))*((c.x-b.x)/(d.x-b.x)) := by{field_simp}
  rw[rr]
  refine Complex.arg_mul_coe_angle ?hx ?hy
  repeat
    by_contra p0
    simp at p0
    tauto
}

lemma angle_symm{a b c : Point}(ha : a ≠ b)(hc : c ≠ b): Angle hc ha = -(Angle ha hc) := by{
  have g: Angle ha ha = Angle ha hc + Angle hc ha := by{exact angle_add ha hc ha}
  rw[angle_self ha] at g
  have : Angle hc ha = Angle hc ha - 0 := by{simp}
  rw[this, g]
  simp
}

lemma qangle_symm(a b c : Point): qAngle a b c = -qAngle c b a := by{
  by_cases ha : a ≠ b
  by_cases hc : c ≠ b
  simp [*]
  rw[angle_symm ha hc]
  simp

  simp at hc
  simp [*]
  simp at ha
  simp [*]
}

/-With this we can already prove the sum of angles in a triangle!-/

theorem angle_tri_points{a b c : Point}(h : noncolinear a b c): qAngle a b c + qAngle b c a + qAngle c a b = 0 := by{
  #check noncolinear
}
