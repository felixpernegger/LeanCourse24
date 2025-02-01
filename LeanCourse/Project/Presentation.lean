import LeanCourse.Project.Incircle
import Mathlib

open Function Set Classical

noncomputable section

set_option linter.unusedTactic false

#check Point

#check colinear

#check det

#check colinear_alt2

#check Line


/-The geometry/framework introduced lets us prove statements "naturally".-/
/-For example, a triangle reflection across a line is similar to the original triangle:-/
example(T: Triangle)(L : Line): Similar (reflection_triangle_line T L) T := by{
  unfold Similar
  right
  apply aaa_asimilar
  unfold Angle_A reflection_triangle_line
  simp
  rw[← angle_reflection_line, angle_symm]

  unfold Angle_B reflection_triangle_line
  simp
  rw[← angle_reflection_line, angle_symm]

  unfold Angle_C reflection_triangle_line
  simp
  rw[← angle_reflection_line, angle_symm]
}

#check ceva

/-
example(T: Triangle)(L : Line): Similar (reflection_triangle_line T L) T := by{
  unfold Similar
  right
  apply aaa_asimilar
  unfold Angle_A reflection_triangle_line
  simp
  rw[← angle_reflection_line, angle_symm]

  unfold Angle_B reflection_triangle_line
  simp
  rw[← angle_reflection_line, angle_symm]

  unfold Angle_C reflection_triangle_line
  simp
  rw[← angle_reflection_line, angle_symm]
}
-/
