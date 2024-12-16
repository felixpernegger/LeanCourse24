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
#check Angle
def Angle
