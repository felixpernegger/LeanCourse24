import LeanCourse.Project.Incircle
import Mathlib

open Function Set Classical

noncomputable section

set_option linter.unusedTactic false

/-Here we prove the Hilbert axioms. Unfortunately many of the Hilbert axioms are actually *three dimensional*, so we do not provide those for obvious reasons.-/

/-I. Axioms of Incidence:-/

/-For every two points, there is a line containing both of them:-/

theorem hilbert_i1(a b : Point): ∃(L : Line), Lies_on a L ∧ Lies_on b L := by{
  use qLine_through a b
  constructor
  · exact qline_through_mem_left a b
  exact qline_through_mem_right a b
}

/-If the points arent the same, this line is unique:-/
theorem hilbert_i2(a b : Point) (L : Line) (ab : a ≠ b) (Lh : Lies_on a L ∧ Lies_on b L) : L = Line_through ab := line_through_unique a b L ab Lh

/-There exists at least two points on a line:-/
theorem hilbert_i3(L : Line): 1 < (L.range).encard := by{
  refine one_lt_encard_iff.mpr ?_
  obtain ⟨a,b,ab,ah,bh⟩ := ex_points_on_line L
  unfold Lies_on at *
  use a
  use b
}

/-There exists three points which do not lie on a line:-/
theorem hilbert_i3': ∃(a b c : Point), pairwise_different_point3 a b c ∧ ¬∃(L : Line), (Lies_on a L ∧ Lies_on b L ∧ Lies_on c L) := by{
  use zero
  use one
  use (Point.mk ({re := 0, im := 1} : ℂ))
  constructor
  · unfold zero one pairwise_different_point3
    simp
    constructor
    · by_contra h0
      suffices : (1:ℂ) = (0:ℂ)
      · contrapose this
        exact one_ne_zero
      calc
        (1:ℂ) = ({ re := 0, im := 1 } : ℂ).re := by{rw[← h0]; simp}
          _= (0:ℂ) := by{simp}
    by_contra h0
    suffices: (1 : ℂ) = (0 : ℂ)
    · contrapose this
      exact one_ne_zero
    calc
      (1:ℂ) = (0 : ℂ).im := by{rw[← h0]; simp}
        _= (0:ℂ) := by{simp}
  by_contra h0
  obtain ⟨L, hL⟩ := h0
  obtain col := three_point_line_colinear hL.1 hL.2.1 hL.2.2
  unfold colinear det conj zero one at col
  simp at col
  linarith
}

/-Axioms of Incidence 4-8 are all three dimensional.-/

/-II. Axioms of Order:-/

/-If a point B lies between points A and C, B is also between C and A, and there exists a line containing the distinct points A, B, C.-/
theorem hilbert_ii1{a b c : Point}(h: in_between a c b): ∃(L : Line), Lies_on a L ∧ Lies_on b L ∧ Lies_on c L := by{
  apply colinear_imp_ex_line
  apply colinear_perm23
  exact in_between_imp_colinear h
}

/-If a and c are points, there is a point lying in between them, on the joint line of a and c.-/
theorem hilbert_ii2{a c : Point}(ac: a ≠ c): ∃(b : Point), Lies_on b (Line_through ac) ∧ b ≠ a ∧ b ≠ c ∧ in_between a c b := by{
  use pmidpoint a c
  constructor
  · unfold Lies_on Line_through pmidpoint colinear det conj
    simp
    ring
  constructor
  · exact pmidpoint_diff_left ac
  constructor
  · exact pmidpoint_diff_right ac
  exact pmidpoint_in_between a c
}

/-Of any three points situated on a line, there is no more than one which lies between the other two.-/
/-(I very slightly simplified this, so the statement doesnt get too ugly)-/
theorem hilbert_ii3{a b c : Point}(abc : pairwise_different_point3 a b c)(h : in_between a b c): ¬in_between b c a ∧ ¬in_between c a b := by{
  unfold pairwise_different_point3 at abc
  simp [in_between_imp_not_left, in_between_imp_not_right, *]
}

/-This remains unfinished for now.-/
