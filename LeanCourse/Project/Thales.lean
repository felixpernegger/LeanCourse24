import LeanCourse.Project.Angles
import Mathlib

open Function Set Classical

noncomputable section


--thales

/-In this section we prove thales theorem, first though, some notation:-/

def Thales_circle: Point → Point → CCircle :=
  fun a b ↦ Circle_through (pmidpoint a b) (⟨1/2 * point_abs a b, by{
    have : 0 ≤ point_abs a b := by{exact point_abs_pos a b}
    linarith
  }⟩)

lemma thales_center(a b : Point): Center (Thales_circle a b) = pmidpoint a b := by{
  unfold Thales_circle
  nth_rw 1[center_unique (pmidpoint a b) ⟨1 / 2 * point_abs a b, Thales_circle.proof_2 a b⟩]
}

lemma thales_radius(a b : Point): Radius (Thales_circle a b) = 1/2 * point_abs a b := by{
  unfold Thales_circle
  rw[radius_unique (pmidpoint a b) ⟨1 / 2 * point_abs a b, Thales_circle.proof_2 a b⟩]
}

lemma thales_radius'(a b : Point): Radius (Thales_circle a b) = ⟨1/2 * point_abs a b,by{have : 0 ≤ point_abs a b := by{exact point_abs_pos a b};linarith}⟩ := by{
  unfold Thales_circle
  exact radius_unique (pmidpoint a b) ⟨1 / 2 * point_abs a b, Thales_circle.proof_2 a b⟩
}

lemma thales_posrad{a b : Point}(ab : a ≠ b): PosRad (Thales_circle a b) := by{
  unfold PosRad
  rw[thales_radius' a b]
  have : 0 < point_abs a b := by{exact point_abs_neq ab}
  have : 0 < 1 / 2 * point_abs a b := by{linarith}
  exact this
}

lemma thales_symm(a b : Point): Thales_circle b a = Thales_circle a b := by{
  unfold Thales_circle
  rw[pmidpoint_symm a b]
  have : (⟨1/2 * point_abs a b,by{have : 0 ≤ point_abs a b := by{exact point_abs_pos a b};linarith}⟩: PosReal) = ⟨1/2 * point_abs b a,by{have : 0 ≤ point_abs b a := by{exact point_abs_pos b a};linarith}⟩ := by{
    ext
    simp
    rw[point_abs_symm]
  }
  rw[this]
}

lemma thales_mem_left(a b : Point): Lies_on_circle a (Thales_circle a b) := by{
  unfold Thales_circle
  refine
    (lies_on_circle_through a (pmidpoint a b)
          ⟨1 / 2 * point_abs a b, Thales_circle.proof_2 a b⟩).mpr
      ?_
  rw[point_abs_symm,point_abs_pmidpoint]
}

lemma thales_mem_right(a b : Point): Lies_on_circle b (Thales_circle a b) := by{
  rw[thales_symm]
  exact thales_mem_left b a
}

lemma thales_mem(a b p : Point): Lies_on_circle p (Thales_circle a b) ↔ point_abs (pmidpoint a b) p = 1/2 * point_abs a b := by{
  unfold Thales_circle Lies_on_circle Circle_through at *
  simp
}

/-Now we feel brave enough to have a go at the theorem:-/
#check posrad_not_center

lemma thales_abs_left{a b p : Point}(hp : Lies_on_circle p (Thales_circle a b)): point_abs (pmidpoint a b) p = point_abs (pmidpoint a b) a := by{
  rw[(thales_mem a b p).1 hp, ← point_abs_pmidpoint, point_abs_symm]
}

lemma thales_abs_right{a b p : Point}(hp : Lies_on_circle p (Thales_circle a b)): point_abs (pmidpoint a b) p = point_abs (pmidpoint a b) b := by{
  rw[(thales_mem a b p).1 hp]
  nth_rw 2[point_abs_symm]
  rw[pmidpoint_symm, point_abs_pmidpoint, point_abs_symm]
}

lemma thales_self(a : Point): ¬PosRad (Thales_circle a a) := by{
  unfold PosRad
  simp
  rw[thales_radius']
  simp
  exact point_abs_self a
}

lemma thales_same_angles_left{a b p : Point}(hp : Lies_on_circle p (Thales_circle a b)): Angle (pmidpoint a b) a p = Angle a p (pmidpoint a b) := by{
  exact same_abs_angle (Eq.symm (thales_abs_left hp))
}

lemma thales_same_angles_right{a b p : Point}(hp : Lies_on_circle p (Thales_circle a b)): Angle (pmidpoint a b) b p = Angle b p (pmidpoint a b) := by{
  exact same_abs_angle (Eq.symm (thales_abs_right hp))
}

theorem thales_theorem{a b p : Point}(hp : Lies_on_circle p (Thales_circle a b)): perp_points p a p b := by{
  by_cases ab: a=b
  rw[ab]
  apply perp_points_self
  simp
  have : ¬PosRad (Thales_circle a b) := by{
    rw[ab]
    exact thales_self b
  }
  #check zero
  sorry
}
