import LeanCourse.Project.Incircle
import Mathlib

open Function Set Classical

noncomputable section

set_option linter.unusedTactic false

#check Point

#check colinear

#check det

#check Line



/-The geometry/framework introduced lets us prove statements "naturally".-/
/-For example, a triangle reflection across a line is similar to the original triangle:-/
example(T: Triangle)(L : Line):
