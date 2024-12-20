import LeanCourse.Project.Thales
import Mathlib

open Function Set Classical

noncomputable section

/-in this section we prove the existance of the orthocenter!-/
/-First as usual a point version:-/

/-the central lemma is that the foots of the altitudes lie on the thales circles as stated here:-/
lemma thales_foot_lies_on(a b : Point)(L : Line)(h : Lies_on a L): Lies_on_circle (foot b L) (Thales_circle a b) := by{
  apply thales_inverse
  apply perp_points_perm_front
  apply perp_points_perm_back
  exact perp_points_foot a b h
}

/-or in the slightly nicer manner for triangles:-/
lemma thales_foot_lies_on_noncolinear{a b c : Point}(h : noncolinear a b c): Lies_on_circle (foot a (qLine_through b c)) (Thales_circle a b) := by{
  have t: Lies_on b (qLine_through b c) := by{exact qline_through_mem_left b c}
  rw[thales_symm]
  exact thales_foot_lies_on b a (qLine_through b c) t
}

/-The thales circle of a triangle are nonconenctric:-/
lemma thales_not_concentric{a b c : Point}(h : noncolinear a b c): ¬Concentric (Thales_circle a b) (Thales_circle a c) := by{
  unfold Concentric
  rw[thales_center, thales_center]
  contrapose h
  have : b = c := by{
    unfold pmidpoint at h
    field_simp at h
    ext
    assumption
  }
  unfold noncolinear
  simp
  apply colinear_self
  tauto
}

/-And in triangles the foots arent the same as the corners:-/
lemma noncolinear_not_on_line{a b c : Point}(h : noncolinear a b c): ¬Lies_on a (qLine_through b c) := by{
  contrapose h
  unfold noncolinear at *
  simp at *
  by_cases bc: b = c
  · apply colinear_self
    tauto
  simp [*] at h
  unfold Line_through Lies_on at h
  simp at h
  apply colinear_perm12
  apply colinear_perm23
  assumption
}

lemma noncolinear_foot_neq_point{a b c : Point}(h : noncolinear a b c): foot a (qLine_through b c) ≠ a := by{
  apply foot_point_not_on_line
  exact noncolinear_not_on_line h
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
#check PowLine
#check powline_intersection3

/-Because now the altidues are just the powlines of the thales circles:-/
theorem altitude_powline{a b c : Point}(h : noncolinear a b c): perp_through (qLine_through b c) a = PowLine (thales_not_concentric h) := by{
  rw[← foot_line_through (noncolinear_not_on_line h)]
  apply powline_intersection3
  constructor
  · exact thales_foot_lies_on_noncolinear h
  rw[qline_through_symm]
  apply noncolinear_perm23 at h
  exact thales_foot_lies_on_noncolinear h

  constructor
  · exact thales_mem_left a b
  exact thales_mem_left a c
}

/-The respective thales circle are cnoncolinear:-/
#check cnoncolinear
lemma thales_cnoncolinear{a b c : Point}(h : noncolinear a b c): cnoncolinear (Thales_circle b c) (Thales_circle c a) (Thales_circle a b) := by{
  unfold cnoncolinear
  repeat
    rw[thales_center]

  exact midtriangle_noncolinear_point h
}

theorem altitudes_copunctal_point{a b c : Point}(h : noncolinear a b c): Copunctal (perp_through (qLine_through b c) a) (perp_through (qLine_through c a) b) (perp_through (qLine_through b a) c) := by{
  #check powline_copunctal
  rw[altitude_powline]
  apply noncolinear_perm12 at h
  rw[altitude_powline]
  apply noncolinear_perm23 at h
  apply noncolinear_perm12 at h
  rw[altitude_powline]
  apply copunctal_perm23
  #check PowLine
  nth_rw 2[powline_symm]
  #check Copunctal
  --apply powline_copunctal
  sorry

  repeat
    assumption
}

#check midtriangle_noncolinear_point
