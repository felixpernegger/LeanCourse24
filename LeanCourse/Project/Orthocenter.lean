import LeanCourse.Project.Thales
import Mathlib

open Function Set Classical

noncomputable section

/-in this section we prove the existance of the orthocenter!-/
/-First as usual a point version:-/

/-the central lemma is that the foots of the altitudes lie on the thales circles as stated here:-/
lemma thales_foot_lies_on{a b : Point}{L : Line}(h : Lies_on a L): Lies_on_circle (foot b L) (Thales_circle a b) := by{
  apply thales_inverse
  apply perp_points_perm_front
  apply perp_points_perm_back
  exact perp_points_foot a b h
}

/-the altidues of 3 noncolinear points are not parallel:-/

lemma altitudes_not_paralllel_points{a b c : Point}(h : noncolinear a b c): ¬Parallel (perp_through (qLine_through a b) c) (perp_through (qLine_through a c) b) := by{
  by_contra h0
  have g: Parallel (qLine_through a b) (qLine_through a c) := by{
    apply perp_perp (perp_through (qLine_through a b) c)
    · apply perp_symm
      exact perp_through_is_perp (qLine_through a b) c
    apply parallel_perp (perp_through (qLine_through a c) b)
    · apply parallel_symm
      assumption
    apply perp_symm
    exact perp_through_is_perp (qLine_through a c) b
  }
  contrapose g
  clear g h0
  have : pairwise_different_point3 a b c := by{exact noncolinear_imp_pairwise_different h}
  have t: pairwise_different_point3 a b c := by{exact noncolinear_imp_pairwise_different h}
  unfold pairwise_different_point3 at this
  have : a ≠ c := by{tauto}
  simp [*]
  exact noncolinear_not_parallel1 h
}

#check Midtriangle
