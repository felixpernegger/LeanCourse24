import LeanCourse.Project.qObject
import Mathlib

open Function Set Classical

noncomputable section

/-Here we prove a few things about tangents (on circles). Unfortunately, we cannot yet prove thales theorem
which is needed for constructing a tangents through a give point to a circle-/

/-As tangent inthe vast majority of cases actually means tangent line to circle, we just use the predicate Tangent-/

def Tangent(L : Line)(C : CCircle) : Prop :=
  Tangential L.range C.range

lemma tangent_nonempty{L : Line}{C : CCircle}(h : )
