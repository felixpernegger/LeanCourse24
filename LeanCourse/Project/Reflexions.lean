import LeanCourse.Project.Auxiliary
import Mathlib

open Function Set Classical

noncomputable section

abbrev PosReal : Type := {x : ℝ // 0 ≤ x}
