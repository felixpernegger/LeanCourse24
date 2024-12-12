import LeanCourse.Project.Parallels
import Mathlib

open Function Set Classical

noncomputable section

/-This file doesnt add anything new however may simplfiy some stuff:
To create geometric object from other objects, the ifrst objects usually have to fulflill some properties:

For example, "Line_through ab" goes through the _proposition_ "a ≠ b" and not actually a b.
This is because laying a line through the same point, is a bit nonsensical and loses all important properties.

The downside of this approach is, we may lose trivial edge cases of theorems becuase points fall together or something.
So therefore in this sections  we introduce quick Line_throuhg's etc., for which we also allow a = b.
-/

/-If a = b, we choose the pparallel_line_to the real line-/

def real_line : Line where
  range := {c : Point | (c.x).im = 0}
  span := by{
    use zero
    use Point.mk 1
    constructor
    unfold zero
    simp

    ext z
    constructor
    intro h
    simp at *
    obtain ⟨z1,z2⟩ := z
    unfold zero colinear det conj
    simp at *
    linarith

    intro h
    obtain ⟨z1,z2⟩ := z
    unfold colinear det conj zero at *
    simp at *
    linarith
  }

lemma zero_on_real_line : Lies_on zero real_line := by{
  unfold Lies_on zero real_line
  simp
}


def qLine_through : Point → Point → Line :=
  fun a b ↦ if ab : a ≠ b then Line_through ab else (if ha : a ≠ zero then Line_through ha else real_line)

@[simp] lemma qline_through_line_through {a b : Point}(ab : a ≠ b): qLine_through a b = Line_through ab := by{
  unfold qLine_through
  simp [*]
}

@[simp] lemma qline_through_ha {a b : Point}(ab : a = b)(ha : a ≠ zero): qLine_through a b = Line_through ha := by{
  unfold qLine_through
  simp [*]
  rw[ab] at ha
  have : ¬ b = zero := by{
    tauto
  }
  simp [*]
}

@[simp] lemma qline_through_zero_zero : qLine_through zero zero = real_line := by{
  unfold qLine_through
  simp
}

@[simp] lemma qline_through_extreme{a b : Point}(ab : a = b)(ha : a = zero): qLine_through a b = real_line := by{
  unfold qLine_through
  simp [*]
  intro c
  exfalso
  rw[← ha] at c
  symm at ab
  contradiction
}

/-with this construction we preserve some important properties:-/

lemma qline_through_symm (a b : Point): qLine_through a b = qLine_through b a := by{
  by_cases ab : a ≠ b
  have ba: b ≠ a := by{tauto}
  simp [*]
  apply line_through_unique
  constructor
  · exact line_through_mem_right ab
  exact line_through_mem_left ab

  simp at ab
  rw[ab]
}

lemma qline_through_mem_left (a b : Point): Lies_on a (qLine_through a b) := by{
  by_cases ab : a ≠ b
  simp [*]
  exact line_through_mem_left ab
  by_cases ha : a ≠ zero
  unfold Lies_on
  simp [*] at ab
  unfold qLine_through
  simp [*]
  by_cases h0: b = zero
  exfalso
  rw[← h0] at ha
  contradiction

  simp [*]
  unfold Line_through
  simp
  apply colinear_self
  tauto

  simp at *
  rw[qline_through_extreme]
  unfold Lies_on real_line
  simp
  rw[ha]
  unfold zero
  simp

  assumption
  assumption
}

lemma qline_through_mem_right (a b : Point): Lies_on b (qLine_through a b) := by{
  by_cases ab : a ≠ b
  simp [*]
  exact line_through_mem_right ab
  by_cases ha : a ≠ zero
  unfold Lies_on
  simp [*] at ab
  unfold qLine_through
  simp [*]
  by_cases h0: b = zero
  exfalso
  rw[← h0] at ha
  contradiction

  simp [*]
  unfold Line_through
  simp
  apply colinear_self
  tauto

  simp at *
  rw[qline_through_extreme]
  unfold Lies_on real_line
  simp
  rw[← ab,ha]
  unfold zero
  simp

  assumption
  assumption
}

/-Now that we've got this out of the way we also make qIntersection for lines.
Here we will actually use *two* versions. If L R are the same, intersection is just some point on L,
if they are disjoint the intersection is zero.-/

def Line_disjoint(L R : Line): Prop
  := L.range ∩ R.range = ∅

lemma disjoint_parallel{L R : Line}(h : Line_disjoint L R): Parallel L R := by{
  apply (parallel_def L R).2
  left
  assumption
}

lemma not_parallel_not_disjoint{L R : Line}(h : ¬Parallel L R): ¬Line_disjoint L R := by{
  contrapose h
  simp at *
  exact disjoint_parallel h
}

lemma line_disjoint_symm{L R : Line}(h : Line_disjoint L R): Line_disjoint R L := by{
  unfold Line_disjoint at *
  rw[Set.inter_comm]
  assumption
}

lemma not_line_disjoint_refl(L : Line): ¬Line_disjoint L L := by{
  obtain ⟨a,ah⟩ := ex_point_on_line L
  unfold Lies_on at ah
  unfold Line_disjoint
  simp
  by_contra p0
  rw[p0] at ah
  contradiction
}

lemma not_line_disjoint_symm{L R : Line}(h : ¬Line_disjoint L R): ¬Line_disjoint R L := by{
  contrapose h
  simp at *
  exact line_disjoint_symm h
}

def qIntersection{L R : Line}(LR : ¬Line_disjoint L R) : Point
  := if h : ¬ Parallel L R then Intersection h else ((ex_point_on_line L).choose)

@[simp] lemma qintersection_intersection{L R : Line}(h : ¬Parallel L R): qIntersection (not_parallel_not_disjoint h) = Intersection h := by{
  unfold qIntersection
  simp [*]
}

lemma qintersection_symm {L R : Line}(LR : ¬Line_disjoint L R): qIntersection LR = qIntersection (not_line_disjoint_symm LR) := by{
  by_cases h: ¬Parallel L R
  simp [*]
  symm
  have h': ¬Parallel R L := by{
    contrapose h
    simp at *
    exact parallel_symm R L h
  }
  simp [*]
  apply intersection_unique
  constructor
  exact intersection_mem_right (of_eq_true (Eq.trans (congrArg Not (eq_false h')) not_false_eq_true))
  exact intersection_mem_left (of_eq_true (Eq.trans (congrArg Not (eq_false h')) not_false_eq_true))

  simp at *
  have : L = R := by{
    apply (parallel_def L R).1 at h
    unfold Line_disjoint at LR
    simp [*] at h
    ext
    rw[h]
  }
  unfold qIntersection
  simp [*]
}

lemma qintersection_mem{L R : Line}(LR: ¬Line_disjoint L R): Lies_on (qIntersection LR) L ∧ Lies_on (qIntersection LR) R := by{
  by_cases h: ¬Parallel L R
  simp [*]
  exact intersection_mem (of_eq_true (Eq.trans (congrArg Not (eq_false h)) not_false_eq_true))

  simp at *
  have h0: L = R := by{
    apply (parallel_def L R).1 at h
    unfold Line_disjoint at LR
    simp [*] at h
    ext
    rw[h]
  }
  simp [*]
  unfold qIntersection
  rw[h0] at h
  simp [*]
  exact (Exists.choose_spec (ex_point_on_line R))
}

lemma qintersection_mem_left{L R : Line}(LR: ¬ Line_disjoint L R): Lies_on (qIntersection LR) L := by{
  exact (qintersection_mem LR).1
}

lemma qintersection_mem_right{L R : Line}(LR: ¬ Line_disjoint L R): Lies_on (qIntersection LR) R := by{
  exact (qintersection_mem LR).2
}

/-And now as promised an even weaker version for which the last property fails (its basically only symmteric)-/

def qqIntersection: Line → Line → Point :=
  fun L R ↦ (if LR : ¬Line_disjoint L R then qIntersection LR else zero)

/-This isnt eniterely useless, as theorems can be stated in a quaicker way using this-/

@[simp] lemma qqintersection_qintersection {L R : Line}(LR: ¬Line_disjoint L R): qqIntersection L R = qIntersection LR := by{
  unfold qqIntersection
  simp [*]
}

@[simp] lemma qqintersection_intersection {L R : Line}(h : ¬Parallel L R): qqIntersection L R = Intersection h := by{
  unfold qqIntersection
  have : ¬Line_disjoint L R := by{
    exact not_parallel_not_disjoint h
  }
  simp [*]
}

lemma qqintersection_symm(L R : Line): qqIntersection L R = qqIntersection R L := by{
  by_cases LR: ¬Line_disjoint L R
  have : ¬Line_disjoint R L := by{
    exact not_line_disjoint_symm LR
  }
  simp [*]
  exact qintersection_symm (of_eq_true (Eq.trans (congrArg Not (eq_false LR)) not_false_eq_true))

  have : Line_disjoint R L := by{
    simp at LR
    exact line_disjoint_symm LR
  }
  unfold qqIntersection
  simp [*]
}

/-For Copunctal we also have simplified version:-/
/-

def qCopunctal(L R S : Line) : Prop :=
  qqIntersection L R = qqIntersection R S ∧ qqIntersection R S = qqIntersection S L

/-With this  we can define perspective triangles and STATE desargue theorem-/

def Perspective(T Q : Triangle): Prop :=
  qCopunctal (qLine_through T.a Q.a) (qLine_through T.b Q.b) (qLine_through T.c Q.c)

example(T Q : Triangle)(h: Perspective T Q): colinear (qqIntersection (tri_ab T) (tri_ab Q)) (qqIntersection (tri_bc T) (tri_bc Q)) (qqIntersection (tri_ca T) (tri_ca Q)) := by{
  sorry
}

--this is still wrong fuck
-/
