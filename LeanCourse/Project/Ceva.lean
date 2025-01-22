import LeanCourse.Project.Similar
import Mathlib

open Function Set Classical

noncomputable section

set_option linter.unusedTactic false
set_option maxHeartbeats 500000

/-In this section we actually prove something interesting for once:
Ceva's theorem. The main lemma behind it will be proven by computation, the main result however
geomtrically!-/

/-First we need signed quotients:-/
def sQuot : Point → Point → Point → ℝ :=
  fun a b c ↦ (if h: in_between a c b then (point_abs a b) /(point_abs b c) else - (point_abs a b) / point_abs b c)

/-Note: We will only ever use this in the case of a b c being colinear, to simplify the definitioon however,
we techincally dont require that.-/

/-The central lemma (bc of its importance called theorem tho haha) is now, that the sQuot corresponds to the quotient of areas:-/
/-We define it very carefully to be as exact and general as possible:-/
theorem squot_areas{a b c : Point}(p : Point)(L : Line)(ah: Lies_on a L)(bh: Lies_on b L)(ch: Lies_on c L)(ph: ¬Lies_on p L): sQuot a b c = (area_points a b p) / (area_points b c p) := by{
  by_cases cb: c = b
  · rw[cb]
    unfold area_points det
    simp
    unfold sQuot in_between
    rw[point_abs_self]
    have u : point_abs a c + 0 = point_abs a c := by{ring}
    simp [u]
  by_cases ab: a = b
  · rw[ab]
    unfold sQuot area_points det
    simp [in_between_self_left, point_abs_self]
  unfold sQuot
  have col: colinear a b c := by{
    have hL: L = Line_through ab := by{
      apply line_through_unique
      tauto
    }
    rw[hL] at ch
    unfold Line_through Lies_on at ch
    simp at ch
    assumption
  }
  have bc_abs: point_abs b c ≠ 0 := by{
    contrapose cb
    simp at *
    symm
    exact abs_zero_imp_same b c cb
  }
  have area_z: area_points b c p ≠ 0 := by{
    contrapose ph
    simp at *
    have hL: L = Line_through cb := by{
      apply line_through_unique
      tauto
    }
    rw[hL]
    unfold Lies_on Line_through
    simp
    apply colinear_perm12
    exact (area_zero_iff b c p).1 ph
  }
  by_cases ac : a = c
  · rw[ac]
    rw[point_abs_symm b c]
    rw[point_abs_symm] at bc_abs
    field_simp
    have : ¬in_between c c b := by{
      contrapose bc_abs
      simp at *
      unfold in_between at bc_abs
      rw[point_abs_symm b c, point_abs_self] at bc_abs
      simp [*] at *
      assumption
    }
    simp [*]
    unfold area_points det
    simp
    ring
  obtain h|h|h := colinear_imp_in_between2 a b c col
  · have nh: ¬in_between a c b := by{
      by_contra h0
      unfold in_between at *
      rw[← h0, point_abs_symm c b] at h
      have : b = c := by{
        apply abs_zero_imp_same b c
        linarith
      }
      tauto
    }
    simp [nh]
    field_simp
    apply colinear_perm23 at col
    obtain ⟨R,hR⟩ := colinear_go_along ac col
    rw[hR]
    rw[hR] at h
    have ca: c ≠ a := by{tauto}
    rw[go_along_symm] at h
    have h1: abs R = R := by{
      suffices: 0 ≤ R
      · exact (abs_of_nonneg this)
      suffices: point_abs c a - R ≤ 0
      · have : 0 ≤ point_abs c a := by{exact point_abs_pos c a}
        linarith
      exact in_between_go_along' ca h
    }
    have h2: abs (point_abs a c - R) = - (point_abs a c - R) := by{
      suffices: point_abs a c - R ≤ 0
      · exact abs_of_nonpos this
      rw[point_abs_symm]
      exact in_between_go_along' ca h
    }
    rw[go_along_abs1, point_abs_symm, go_along_abs2, h1, h2]
    unfold go_along dir
    have ac_abs: (point_abs a c) ≠ 0 := by{
      exact point_abs_neq_zero ac
    }
    unfold area_points det padd p_scal_mul
    field_simp
    obtain ⟨a1,a2⟩ := a
    obtain ⟨c1,c2⟩ := c
    obtain ⟨p1,p2⟩ := p
    unfold point_abs conj
    field_simp at *
    have : Complex.abs { re := a1 - c1, im := a2 - c2 } ≠ 0 := by{
      by_contra h0
      simp at h0
      have s1: a1 - c1 = 0 := by{
        calc
          a1-c1 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).re := by{simp}
            _= (0 : ℂ).re := by{rw[h0]}
            _= 0 := by{simp}
      }
      have s2: a2-c2 = 0 := by{
        calc
          a2-c2 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).im := by{simp}
            _= (0 : ℂ).im := by{rw[h0]}
            _= 0 := by{simp}
      }
      have t1: a1 = c1 := by{linarith}
      have t2: a2 = c2 := by{linarith}
      tauto
    }
    field_simp
    ring
    repeat
      assumption

  have hh: ¬in_between a c b := by{
    by_contra h0
    unfold in_between at *
    rw[← h0] at h
    rw[point_abs_symm b a] at h
    have : a=b := by{
      apply abs_zero_imp_same
      linarith
    }
    tauto
  }
  simp [hh]
  field_simp
  apply colinear_perm23 at col
  obtain ⟨R,hR⟩ := colinear_go_along ac col
  rw[hR] at h
  apply in_between_symm at h
  obtain u := in_between_go_along' ac h
  rw[point_abs_symm b c, hR, go_along_abs1 ac, go_along_abs2 ac]
  have s1: abs R = -R := by{
    simp
    assumption
  }
  have s2: |point_abs a c - R| = point_abs a c - R := by{
    obtain o := point_abs_pos a c
    simp
    linarith
  }
  rw[s1,s2]
  obtain ⟨a1,a2⟩ := a
  obtain ⟨c1,c2⟩ := c
  obtain ⟨p1,p2⟩ := p
  unfold go_along dir padd p_scal_mul area_points det conj point_abs
  field_simp at *
  have : Complex.abs { re := a1 - c1, im := a2 - c2 } ≠ 0 := by{
      by_contra h0
      simp at h0
      have s1: a1 - c1 = 0 := by{
        calc
          a1-c1 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).re := by{simp}
            _= (0 : ℂ).re := by{rw[h0]}
            _= 0 := by{simp}
      }
      have s2: a2-c2 = 0 := by{
        calc
          a2-c2 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).im := by{simp}
            _= (0 : ℂ).im := by{rw[h0]}
            _= 0 := by{simp}
      }
      have t1: a1 = c1 := by{linarith}
      have t2: a2 = c2 := by{linarith}
      tauto
  }
  field_simp
  ring



  apply in_between_symm at h
  simp [h]
  field_simp
  apply colinear_perm23 at col
  obtain ⟨R,hR⟩ := colinear_go_along ac col
  rw[point_abs_symm b c, hR, go_along_abs1, go_along_abs2]
  rw[hR] at h
  obtain ⟨u1,u2⟩ := in_between_go_along ac h
  have s1: abs R = R := by{simp [*]}
  have s2: abs (point_abs a c - R) = point_abs a c - R := by{
    simp
    linarith
  }
  rw[s1,s2]
  obtain ⟨a1,a2⟩ := a
  obtain ⟨c1,c2⟩ := c
  obtain ⟨p1,p2⟩ := p
  unfold go_along dir padd p_scal_mul area_points det conj point_abs
  field_simp at *
  have : Complex.abs { re := a1 - c1, im := a2 - c2 } ≠ 0 := by{
      by_contra h0
      simp at h0
      have s1: a1 - c1 = 0 := by{
        calc
          a1-c1 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).re := by{simp}
            _= (0 : ℂ).re := by{rw[h0]}
            _= 0 := by{simp}
      }
      have s2: a2-c2 = 0 := by{
        calc
          a2-c2 = ({ re := a1 - c1, im := a2 - c2 } : ℂ).im := by{simp}
            _= (0 : ℂ).im := by{rw[h0]}
            _= 0 := by{simp}
      }
      have t1: a1 = c1 := by{linarith}
      have t2: a2 = c2 := by{linarith}
      tauto
  }
  field_simp
  ring
  repeat
    tauto
}

/-With that lemma we can now prove ceva's theorem in a nice way
Unfortunaately our version is a bit ugly, as ceva's theorem is best stated in terms of projective geometry,
which is not possible with the foundation of geometry being used here :(-/

def not_on_perimiter(p : Point)(T : Triangle): Prop :=
  ¬Lies_on p (tri_ab T) ∧ ¬Lies_on p (tri_bc T) ∧ ¬Lies_on p (tri_ca T)

def not_on_perimiter_points(p : Point){a b c : Point}(h : noncolinear a b c) :=
  not_on_perimiter p (Triangle.mk a b c h)

def qnot_on_perimiter_points(p a b c : Point): Prop :=
  if h : noncolinear a b c then not_on_perimiter_points p h else False

lemma not_on_perimiter_points_not_on_perimiter{p : Point}{T : Triangle}(h: not_on_perimiter p T): not_on_perimiter_points p T.noncolinear := by{
  unfold not_on_perimiter_points
  simp [*]
}

lemma qnot_on_perimiter_points_not_on_perimiter_points{p : Point}{a b c : Point}{h : noncolinear a b c}(h': not_on_perimiter_points p h): qnot_on_perimiter_points p a b c := by{
  unfold qnot_on_perimiter_points
  simp [*]
}

lemma qnot_on_perimiter_points_not_on_perimiter{p : Point}{T : Triangle}(h: not_on_perimiter p T): qnot_on_perimiter_points p T.a T.b T.c := by{
  apply qnot_on_perimiter_points_not_on_perimiter_points
  exact not_on_perimiter_points_not_on_perimiter h
}


/-We can permutate the latter:-/

lemma qnot_on_perimiter_points_perm12{p a b c : Point}(h : qnot_on_perimiter_points p a b c): qnot_on_perimiter_points p b a c := by{
  unfold qnot_on_perimiter_points at *
  simp at *
  obtain ⟨h1,h2⟩ := h
  use noncolinear_perm12 h1
  unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at *
  simp at *
  repeat
    rw[← qline_through_line_through]
    rw[← qline_through_line_through] at h2
  rw[qline_through_symm b a, qline_through_symm a c, qline_through_symm c b]
  tauto
}

lemma qnot_on_perimiter_points_perm13{p a b c : Point}(h : qnot_on_perimiter_points p a b c): qnot_on_perimiter_points p c b a := by{
  unfold qnot_on_perimiter_points at *
  simp at *
  obtain ⟨h1,h2⟩ := h
  use noncolinear_perm13 h1
  unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at *
  simp at *
  repeat
    rw[← qline_through_line_through]
    rw[← qline_through_line_through] at h2
  rw[qline_through_symm b a, qline_through_symm a c, qline_through_symm c b]
  tauto
}

lemma qnot_on_perimiter_points_perm23{p a b c : Point}(h : qnot_on_perimiter_points p a b c): qnot_on_perimiter_points p a c b := by{
  unfold qnot_on_perimiter_points at *
  simp at *
  obtain ⟨h1,h2⟩ := h
  use noncolinear_perm23 h1
  unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at *
  simp at *
  repeat
    rw[← qline_through_line_through]
    rw[← qline_through_line_through] at h2
  rw[qline_through_symm b a, qline_through_symm a c, qline_through_symm c b]
  tauto
}

/-TO further generale a tiny bit more, we introduce the following:-/

def sQuotL : Line → Point → Point → ℝ :=
  fun L a b ↦ if h: Parallel L (qLine_through a b) then -1 else sQuot a (Intersection h) b

/-A small numerical lemma:-/

lemma same_quot_diff{a b c d q : ℝ}(bh : b ≠ 0)(dh : d ≠ 0)(ab: a / b = q)(cd: c / d = q)(bd: b ≠ d): (a-c)/(b-d) = q := by{
  field_simp at *
  have : b - d ≠ 0 := by{
    contrapose bd
    simp at *
    calc
      b = b - (b-d) := by{rw[bd, sub_zero]}
        _= d := by{ring}
  }
  field_simp
  ring_nf
  rw[← ab, cd]
}

/-The areas of b p c etc are nonzero:-/

lemma qnot_on_perimiter_points_imp_area_not_zero{p a b c : Point}(h : qnot_on_perimiter_points p a b c): area_points b c p ≠ 0 := by{
  unfold qnot_on_perimiter_points at h
  simp at h
  obtain ⟨h,h'⟩ := h
  unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h'
  obtain ⟨ab,bc,ca⟩ := h'
  unfold Lies_on Line_through at bc
  simp at bc
  contrapose bc
  simp at *
  exact (area_zero_iff b c p).mp bc
}

lemma qnot_on_perimiter_points_imp_area_not_zero'{p a b c : Point}(h: qnot_on_perimiter_points p a b c): area_points a p b ≠ 0 := by{
  apply qnot_on_perimiter_points_perm13 at h
  obtain u := qnot_on_perimiter_points_imp_area_not_zero h
  contrapose u
  simp at *
  rw[area_points_perm12, area_points_perm23]
  simp [*]
}

/-A slightly different version of the lemma above is the following:

If bc isnt parallel to ap, the area a (Intersection ap bc) b isnt zero:-/
/-(We will need this to apply same_quot_diff)-/

lemma qnot_on_perimiter_points_not_parallel_imp_area_not_zero{p a b c : Point}(h : qnot_on_perimiter_points p a b c)(h' : ¬Parallel (qLine_through a p) (qLine_through b c)): area_points a (Intersection h') b ≠ 0 := by{
  unfold qnot_on_perimiter_points at h
  simp at h
  obtain ⟨h,h'⟩ := h
  unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h'
  obtain ⟨ab,bc,ca⟩ := h'
  have bc': b ≠ c := by{
    have : pairwise_different_point3 a b c := by{exact noncolinear_imp_pairwise_different h}
    unfold pairwise_different_point3 at this
    tauto
  }
  have g: ¬Lies_on a (qLine_through b c) := by{
    simp [bc']
    by_contra p0
    suffices : colinear a b c
    · unfold noncolinear at h
      tauto
    unfold Lies_on Line_through at p0
    simp at p0
    apply colinear_perm12
    apply colinear_perm23
    assumption
  }
  have ap : a ≠ p := by{
    contrapose ab
    simp at *
    rw[← ab, ← qline_through_line_through]
    exact qline_through_mem_left a b
  }
  have ib: Intersection h' ≠ b := by{
    by_contra p0
    contrapose ab
    simp at *
    have hb: Lies_on b (Line_through ap) := by{
      rw[← p0, ← qline_through_line_through]
      exact intersection_mem_left h'
    }
    unfold Line_through Lies_on at hb
    simp at hb
    unfold Lies_on Line_through
    simp
    apply colinear_perm23
    assumption
  }
  by_contra p0
  obtain col := (area_zero_iff a (Intersection h') b).mp p0
  have g1: Line_through ib = Line_through bc' := by{
    symm
    apply line_through_unique
    constructor
    · rw[← qline_through_line_through]
      exact intersection_mem_right h'
    exact line_through_mem_left bc'
  }
  have g2: Lies_on a (Line_through ib) := by{
    unfold Lies_on Line_through
    simp
    apply colinear_perm13
    apply colinear_perm23
    assumption
  }
  rw[g1] at g2
  unfold Lies_on Line_through at g2
  simp at g2
  unfold noncolinear at h
  apply colinear_perm23 at g2
  apply colinear_perm12 at g2
  contradiction
}

/-The central lemma is the following (the main theorem will mostly just be special cases, albeit is is very ugly sadly)-/

lemma squotl_not_parallel{p : Point}{a b c : Point}(np: qnot_on_perimiter_points p a b c)(h : ¬Parallel (qLine_through a p) (qLine_through b c)): sQuotL (qLine_through a p) b c = area_points a p b / area_points c p a := by{
  unfold sQuotL
  simp [h]
  have s1: sQuot b (Intersection h) c = area_points b (Intersection h) p / area_points (Intersection h) c p := by{
    rw[squot_areas p (qLine_through b c) (qline_through_mem_left b c) ?_ (qline_through_mem_right b c)]
    · unfold qnot_on_perimiter_points not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at np
      simp [h] at *
      obtain ⟨h1,h2⟩ := np
      repeat
        rw[← qline_through_line_through] at h2
      tauto
    exact intersection_mem_right h
  }
  have s2: sQuot b (Intersection h) c = area_points b (Intersection h) a / area_points (Intersection h) c a := by{
    rw[squot_areas a (qLine_through b c) (qline_through_mem_left b c) ?_ (qline_through_mem_right b c)]
    · contrapose np
      unfold qnot_on_perimiter_points
      simp at *
      intro u
      have bc': b ≠ c := by{
        contrapose u
        unfold noncolinear colinear det
        simp at *
        rw[u]
        ring
      }
      simp [bc'] at np
      unfold Lies_on Line_through at np
      simp at np
      unfold noncolinear at u
      apply colinear_perm13 at np
      apply colinear_perm23 at np
      contradiction
    exact intersection_mem_right h
  }
  symm at s1 s2

  have r1: (area_points b (Intersection h) p - area_points b (Intersection h) a) = area_points a p b := by{
    have bc: b ≠ c := by{
      unfold qnot_on_perimiter_points at np
      simp at np
      obtain ⟨h1,h2⟩ := np
      unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca Lies_on Line_through at h2
      simp at *
      contrapose h1
      unfold noncolinear
      simp at *
      apply colinear_self
      tauto
    }
    have ip: Intersection h ≠ p := by{
      by_contra h0
      have: Lies_on p (qLine_through b c) := by{
        rw[← h0]
        exact intersection_mem_right h
      }
      unfold qnot_on_perimiter_points at np
      simp at np
      obtain ⟨h1,h2⟩ := np
      unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
      simp at h2
      simp [bc] at this
      tauto
    }
    have al: Lies_on a (Line_through ip) := by{
      have ap: a ≠ p := by{
        unfold qnot_on_perimiter_points at np
        simp at np
        obtain ⟨h1,h2⟩ := np
        unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
        contrapose h2
        simp at *
        repeat
          rw[← qline_through_line_through]
        intro h0
        have : Lies_on p (qLine_through a b) := by{
          rw[← h2]
          exact qline_through_mem_left a b
        }
        contradiction
      }
      suffices : Line_through ip = Line_through ap
      · rw[this]
        exact line_through_mem_left ap
      symm
      apply line_through_unique
      constructor
      · rw[← qline_through_line_through]
        exact intersection_mem_left h
      exact line_through_mem_right ap
    }

    rw[area_add_side b (Intersection h) p a ip al]
    ring_nf
    rw[area_points_perm12, area_points_perm23]
    simp
  }
  have r2: (area_points (Intersection h) c p - area_points (Intersection h) c a) = area_points c p a := by{
    have bc: b ≠ c := by{
      unfold qnot_on_perimiter_points at np
      simp at np
      obtain ⟨h1,h2⟩ := np
      unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca Lies_on Line_through at h2
      simp at *
      contrapose h1
      unfold noncolinear
      simp at *
      apply colinear_self
      tauto
    }
    have ip: Intersection h ≠ p := by{
      by_contra h0
      have: Lies_on p (qLine_through b c) := by{
        rw[← h0]
        exact intersection_mem_right h
      }
      unfold qnot_on_perimiter_points at np
      simp at np
      obtain ⟨h1,h2⟩ := np
      unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
      simp at h2
      simp [bc] at this
      tauto
    }
    have al: Lies_on a (Line_through ip) := by{
      have ap: a ≠ p := by{
        unfold qnot_on_perimiter_points at np
        simp at np
        obtain ⟨h1,h2⟩ := np
        unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
        contrapose h2
        simp at *
        repeat
          rw[← qline_through_line_through]
        intro h0
        have : Lies_on p (qLine_through a b) := by{
          rw[← h2]
          exact qline_through_mem_left a b
        }
        contradiction
      }
      suffices : Line_through ip = Line_through ap
      · rw[this]
        exact line_through_mem_left ap
      symm
      apply line_through_unique
      constructor
      · rw[← qline_through_line_through]
        exact intersection_mem_left h
      exact line_through_mem_right ap
    }
    rw[area_points_perm12, area_add_side c (Intersection h) p a ip al, area_points_perm12]
    ring_nf
    rw[area_points_perm23]
    simp
  }
  have n1: area_points (Intersection h) c p ≠ 0 := by{
    by_contra h0
    obtain col := (area_zero_iff (Intersection h) c p).mp h0
    have ic: Intersection h ≠ c := by{
      by_contra p0
      have ap: a ≠ p := by{
        unfold qnot_on_perimiter_points at np
        simp at np
        obtain ⟨h1,h2⟩ := np
        unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
        contrapose h2
        simp at *
        repeat
          rw[← qline_through_line_through]
        intro h0
        have : Lies_on p (qLine_through a b) := by{
          rw[← h2]
          exact qline_through_mem_left a b
        }
        contradiction
      }
      unfold qnot_on_perimiter_points at np
      simp at np
      obtain ⟨h1,h2⟩ := np
      unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
      simp at *
      obtain ⟨ab,bc,ca⟩ := h2
      contrapose ca
      simp at *
      have hc : Lies_on c (Line_through ap) := by{
        rw[← p0, ← qline_through_line_through]
        exact intersection_mem_left h
      }
      unfold Line_through Lies_on at hc
      simp at hc
      unfold Lies_on Line_through
      simp
      apply colinear_perm12
      apply colinear_perm23
      assumption
    }
    have bc : b ≠ c := by{
      unfold qnot_on_perimiter_points at np
      simp at np
      obtain ⟨h1,h2⟩ := np
      unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
      by_contra h0
      have col: colinear a b c := by{
        apply colinear_self
        tauto
      }
      unfold noncolinear at h1
      contradiction
    }
    have g: Line_through bc = Line_through ic := by{
      apply line_through_unique
      constructor
      · rw[← qline_through_line_through]
        exact intersection_mem_right h
      exact line_through_mem_right bc
    }
    suffices : Lies_on p (Line_through bc)
    · unfold qnot_on_perimiter_points at np
      simp at np
      obtain ⟨h1,h2⟩ := np
      unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
      tauto
    rw[g]
    unfold Lies_on Line_through
    simp
    assumption
  }
  have n2: area_points (Intersection h) c a ≠ 0 := by{
    by_contra h0
    obtain col := (area_zero_iff (Intersection h) c a).mp h0
    have ic: Intersection h ≠ c := by{
      by_contra p0
      have ap: a ≠ p := by{
        unfold qnot_on_perimiter_points at np
        simp at np
        obtain ⟨h1,h2⟩ := np
        unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
        contrapose h2
        simp at *
        repeat
          rw[← qline_through_line_through]
        intro h0
        have : Lies_on p (qLine_through a b) := by{
          rw[← h2]
          exact qline_through_mem_left a b
        }
        contradiction
      }
      unfold qnot_on_perimiter_points at np
      simp at np
      obtain ⟨h1,h2⟩ := np
      unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
      simp at *
      obtain ⟨ab,bc,ca⟩ := h2
      contrapose ca
      simp at *
      have hc : Lies_on c (Line_through ap) := by{
        rw[← p0, ← qline_through_line_through]
        exact intersection_mem_left h
      }
      unfold Line_through Lies_on at hc
      simp at hc
      unfold Lies_on Line_through
      simp
      apply colinear_perm12
      apply colinear_perm23
      assumption
    }
    have bc : b ≠ c := by{
      unfold qnot_on_perimiter_points at np
      simp at np
      obtain ⟨h1,h2⟩ := np
      unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
      by_contra h0
      have col: colinear a b c := by{
        apply colinear_self
        tauto
      }
      unfold noncolinear at h1
      contradiction
    }
    have g: Line_through bc = Line_through ic := by{
      apply line_through_unique
      constructor
      · rw[← qline_through_line_through]
        exact intersection_mem_right h
      exact line_through_mem_right bc
    }
    suffices: Lies_on a (Line_through bc)
    · unfold qnot_on_perimiter_points at np
      simp at np
      obtain ⟨h1,h2⟩ := np
      unfold Lies_on Line_through at this
      unfold noncolinear at h1
      simp at *
      apply colinear_perm13 at this
      apply colinear_perm23 at this
      contradiction
    rw[g]
    unfold Lies_on Line_through
    simp
    assumption
  }
  have n3: area_points (Intersection h) c p ≠ area_points (Intersection h) c a := by{
    suffices : area_points c p a ≠ 0
    · contrapose this
      simp at *
      rw[← r2, this, sub_self]
    by_contra h0
    have col: colinear c p a := by{exact (area_zero_iff c p a).mp h0}
    have ca : c ≠ a := by{
      unfold qnot_on_perimiter_points at np
      simp at np
      obtain ⟨h1,h2⟩ := np
      unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
      by_contra p0
      have : colinear a b c := by{
        apply colinear_self
        tauto
      }
      unfold noncolinear at h1
      contradiction
    }
    unfold qnot_on_perimiter_points at np
    simp at np
    obtain ⟨h1,h2⟩ := np
    unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
    have : Lies_on p (Line_through ca) := by{
      unfold Lies_on Line_through
      simp
      apply colinear_perm23
      assumption
    }
    tauto
  }
  rw[← same_quot_diff n1 n2 s1 s2 n3, r1,r2]
}

/-We actually don't need parallelity! (The main case I didnt put this in one theorem all together is that I actually noticed this fact very very late lol)-/

lemma squotl_quot{p : Point}{a b c : Point}(np: qnot_on_perimiter_points p a b c): sQuotL (qLine_through a p) b c = area_points a p b / area_points c p a := by{
  by_cases h0: ¬Parallel (qLine_through a p) (qLine_through b c)
  · exact squotl_not_parallel np h0
  simp at h0
  unfold sQuotL
  simp [h0]
  field_simp [qnot_on_perimiter_points_imp_area_not_zero' (qnot_on_perimiter_points_perm12 (qnot_on_perimiter_points_perm23 np))]
  rw[area_points_perm13]
  simp

  have bc: b ≠ c := by{
    unfold qnot_on_perimiter_points at np
    simp at np
    obtain ⟨h1,h2⟩ := np
    unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
    have : pairwise_different_point3 a b c := by{exact noncolinear_imp_pairwise_different h1}
    unfold pairwise_different_point3 at this
    tauto
  }
  have ap: a ≠ p := by{
    unfold qnot_on_perimiter_points at np
    simp at np
    obtain ⟨h1,h2⟩ := np
    unfold not_on_perimiter_points not_on_perimiter tri_ab tri_bc tri_ca at h2
    contrapose h2
    simp at *
    repeat
      rw[← qline_through_line_through]
      intro h0
      have : Lies_on p (qLine_through a b) := by{
        rw[← h2]
        exact qline_through_mem_left a b
      }
      contradiction
  }
  simp [bc, ap] at h0
  obtain ⟨t,ht⟩ := parallel_line_through ap bc h0
  rw[ht]
  unfold area_points det conj
  simp
  ring
}

/-Using this (techincally one direction of) Ceva theorem can be formulated as followed:-/

theorem ceva_spec(T : Triangle)(p : Point)(hp: not_on_perimiter p T): (sQuotL (qLine_through T.a p) T.b T.c) * (sQuotL (qLine_through T.b p) T.c T.a) * (sQuotL (qLine_through T.c p) T.a T.b) = 1 := by{
  apply qnot_on_perimiter_points_not_on_perimiter at hp
  obtain hp' := (qnot_on_perimiter_points_perm13 (qnot_on_perimiter_points_perm12 hp))
  obtain hp'' := (qnot_on_perimiter_points_perm13 (qnot_on_perimiter_points_perm12 hp'))
  rw[squotl_quot hp, squotl_quot hp', squotl_quot hp'']
  field_simp [qnot_on_perimiter_points_imp_area_not_zero' hp, qnot_on_perimiter_points_imp_area_not_zero' hp', qnot_on_perimiter_points_imp_area_not_zero' hp'']
  ring
}

/-The converse of this - sort of - holds modulo an edge case. Meaning: Given three lines through the vertices, such that the sQuotL's multiply to one,
then the lines are copunctal (minus edge case in non-projective geometry like we have here...)-/

/-For this we first need injectivity of sQuot:-/

/-For this, first note the following, postivity of squot:-/
lemma squot_pos{a b c : Point}: 0 < sQuot a b c ↔ b ≠ a ∧ b ≠ c ∧ in_between a c b := by{
  constructor
  · intro h
    unfold sQuot at h
    constructor
    · by_contra h0
      have : in_between a c b := by{
        rw[h0]
        exact in_between_self_left a c
      }
      simp [this] at h
      rw[h0, point_abs_self] at h
      simp at h
    constructor
    · by_contra h0
      have : in_between a c b := by{
        rw[h0]
        exact in_between_self_right a c
      }
      simp [this] at h
      rw[h0, point_abs_self] at h
      simp at h
    by_contra h0
    simp [h0] at h
    by_cases bc: b = c
    rw[bc, point_abs_self] at h
    simp at h

    have bcpos: 0 < point_abs b c := by{exact point_abs_neq bc}
    field_simp [bcpos] at h
    have : 0 ≤ point_abs a b := by{exact point_abs_pos a b}
    linarith
  intro ⟨ba,bc,h⟩
  unfold sQuot
  simp [h]
  rw[point_abs_symm a b]
  simp [point_abs_neq ba, point_abs_neq bc]
}

/-One lemma which probably should have been stated earlier, but which is needed here, that
- basically- if in_between a b c then ¬in_between b c a and so on:-/
lemma in_between_imp_not_left{a b c : Point}(ab : a ≠ b)(ca: c ≠ a)(h: in_between a b c): ¬in_between b c a := by{
  obtain col := in_between_imp_colinear h
  obtain ⟨R,hR⟩ := colinear_go_along ab col
  rw[hR] at h
  obtain ⟨R1,R2⟩ := in_between_go_along ab h
  by_contra h0
  rw[hR] at h0
  obtain R3 := in_between_go_along' ab h0
  have g : R = 0 := by{
    linarith
  }
  have goal: c = a := by{
    rw[hR, g, go_along_zero]
  }
  contradiction
}

lemma in_between_imp_not_right{a b c : Point}(ab : a ≠ b)(bc: b ≠ c)(h: in_between a b c): ¬in_between c a b := by{
  obtain col := in_between_imp_colinear h
  obtain ⟨R,hR⟩ := colinear_go_along ab col
  rw[hR] at h
  obtain ⟨R1,R2⟩ := in_between_go_along ab h
  by_contra h0
  rw[hR] at h0
  apply in_between_symm at h0
  rw[go_along_symm] at h0
  obtain R3 := in_between_go_along' (Ne.symm ab) h0
  rw[point_abs_symm] at R3
  have g : R = point_abs a b := by{
    linarith
  }
  have goal: c = b := by{
    rw[hR, g, go_along_point_abs]
  }
  tauto
}

/-Similarly, we get a result for negative sQuot, though due to our (rather inprecise) definition, we also need colinearity:-/
lemma squot_neg{a b c : Point}(h: colinear a b c): sQuot a b c < 0 ↔ b ≠ a ∧ b ≠ c ∧ (in_between b c a ∨ in_between a b c) := by{
  constructor
  · intro h'
    have ba: b ≠ a := by{
      by_contra h0
      unfold sQuot at h'
      rw[h0] at h'
      simp [in_between_self_left, point_abs_self] at h'
    }
    have bc: b ≠ c := by{
      by_contra h0
      unfold sQuot at h'
      rw[h0] at h'
      simp [in_between_self_left, point_abs_self] at h'
    }
    simp [*]
    obtain u|u|u := colinear_imp_in_between2 a b c h
    swap
    tauto
    tauto

    exfalso
    suffices: 0 < sQuot a b c
    · linarith
    apply squot_pos.2
    simp [*]
    apply in_between_symm
    assumption
  intro ⟨ba,bc,h'⟩
  unfold sQuot
  suffices: ¬in_between a c b
  · simp [this]
    rw[point_abs_symm a b]
    refine div_neg_of_neg_of_pos ?mpr.ha ?mpr.hb
    · simp [point_abs_neq ba]
    simp [point_abs_neq bc]
  obtain h'|h' := h'
  · exact in_between_imp_not_right (Ne.symm bc) ba (in_between_symm h')
  exact in_between_imp_not_left ba (Ne.symm bc) (in_between_symm h')
}

/-And its zero iff its a or b or a = b:-/
lemma squot_zero{a b p : Point}: sQuot a p b = 0 ↔ p = a ∨ p = b := by{
  unfold sQuot
  by_cases u: in_between a b p
  · simp [u]
    constructor
    · intro v
      obtain v|v := v
      · left
        symm
        exact abs_zero_imp_same a p v
      right
      exact abs_zero_imp_same p b v
    intro h
    obtain h|h|h := h
    · rw[h, point_abs_self]
      tauto
    · rw[point_abs_self]
      tauto
  simp [u]
  constructor
  · intro h
    obtain h|h := h
    · left
      symm
      exact abs_zero_imp_same a p h
    right
    exact abs_zero_imp_same p b h
  intro h
  obtain h|h := h
  · rw[h, point_abs_self]
    tauto
  rw[h, point_abs_self]
  tauto
}

/-sQuotL is -1 iff the lines are parallel. One direction is in the definition, other one simple calculation:-/
lemma squotl_neg_one{a b : Point}{L : Line}(ab : a ≠ b): sQuotL L a b = -1 ↔ Parallel (Line_through ab) L := by{
  constructor
  intro h
  apply parallel_symm
  by_contra h0
  unfold sQuotL at h
  simp [*] at h
  have col: colinear a (Intersection h0) b := by{
    suffices: Lies_on (Intersection h0) (Line_through ab)
    · unfold Lies_on Line_through at this
      simp at this
      apply colinear_perm23
      assumption
    exact intersection_mem_right h0
  }
  have q: sQuot a (Intersection h0) b < 0 := by{linarith}
  obtain ⟨ia,ib,u⟩ := (squot_neg col).1 q
  set I := Intersection h0
  have inb: ¬in_between a b I := by{
    obtain u|u := u
    · exact in_between_imp_not_right (Ne.symm ib) ia (in_between_symm u)
    exact in_between_imp_not_left ia (Ne.symm ib) (in_between_symm u)
  }
  unfold sQuot at h
  simp [*] at h
  obtain t := point_abs_neq ib --for some reason i cant put this in field_simp directly?
  field_simp at h
  obtain u|u := u
  · unfold in_between at u
    suffices : a = b
    · tauto
    rw[← h] at u
    rw[point_abs_symm I a] at u
    simp at u
    exact abs_zero_imp_same a b u
  unfold in_between at u
  rw[h, point_abs_symm I b] at u
  simp at u
  obtain g := (abs_zero_imp_same a b u)
  tauto

  intro h
  unfold sQuotL
  apply parallel_symm at h
  simp [ab, h]
}

/-A purely analytical lemma will help us finishing off:-/
/-This could probably done by just using some fun prop (although we have an annoyance at t = r), but it is simple enough to prove directly:-/
lemma t_div_r_sub_t_inj{t t' r : ℝ}(hr: r ≠ 0)(ht: t ≠ r)(ht': t' ≠ r)(h: t / (r - t) = t' / (r - t')): t = t' := by{
  have rt_sub: r-t ≠ 0 := by{
    contrapose ht
    simp at *
    linarith
  }
  have rt'_sub: r-t' ≠ 0 := by{
    contrapose ht'
    simp at *
    linarith
  }
  field_simp [*] at h
  suffices: t*r = t'*r
  · field_simp at this
    tauto
  calc
    t*r = t'*(r-t) + t*t' := by{rw[← h]; ring}
      _= t'*r := by{ring}
}

/-And similarly:-/
lemma t_ad_r_dis_t_inj{t t' r : ℝ}(hr: r ≠ 0)(ht: t ≠ 0)(ht': t' ≠ 0)(h: (t+r)/t = (t'+r)/t'): t = t' := by{
  field_simp at h
  suffices: r*t' = r*t
  · field_simp at this
    tauto
  calc
    r*t' = (t' + r) * t - t*t' := by{rw[← h];ring}
      _= r*t := by{ring}
}


/-Very importantly, sQuot is (sort of) injective:
(Note: I got lost a bit in this proof, its rather ugly. So best to not look at the details...)-/
theorem squot_inj{a b p q: Point}(ab : a ≠ b)(hp: Lies_on p (Line_through ab))(hq : Lies_on q (Line_through ab))(pa: p ≠ a)(pb: p ≠ b)(qa: q ≠ a)(qb: q ≠ b)(h: sQuot a p b = sQuot a q b): p = q := by{
  unfold Lies_on Line_through at *
  simp at *
  by_cases e0: sQuot a p b = 0
  · apply squot_zero.1 at e0
    tauto
  by_cases l0: sQuot a p b < 0
  · have inp: in_between p b a ∨ in_between a p b := by{
      apply colinear_perm23 at hp
      obtain u := (squot_neg hp).1 l0
      tauto
    }
    have inq: in_between q b a ∨ in_between a q b := by{
      apply colinear_perm23 at hq
      rw[h] at l0
      obtain u := (squot_neg hq).1 l0
      tauto
    }
    have ninp: ¬in_between a b p := by{
      obtain inp|inp := inp
      apply in_between_symm at inp
      apply in_between_imp_not_right
      · tauto
      · assumption
      assumption

      apply in_between_imp_not_left
      · assumption
      · tauto
      apply in_between_symm at inp
      assumption
    }
    have ninq: ¬in_between a b q := by{
      obtain inq|inq := inq
      apply in_between_imp_not_right
      tauto
      tauto
      apply in_between_symm at inq
      assumption

      apply in_between_imp_not_left
      tauto
      tauto
      apply in_between_symm at inq
      assumption
    }
    obtain inp|inp := inp
    obtain inq|inq := inq
    have inp' := inp
    have inq' := inq
    unfold sQuot at h
    simp [*] at h
    unfold in_between at inq inp
    rw[← inp, ← inq] at h
    rw[point_abs_symm p a, point_abs_symm q a] at h
    set t := point_abs a p
    set t' := point_abs a q
    set r' := point_abs a b
    set r := - r'
    have tr: t ≠ r := by{
      suffices: r < t
      · linarith
      suffices : r < 0 ∧ 0 ≤ t
      · linarith
      constructor
      · unfold r r'
        simp
        exact point_abs_neq ab
      unfold t
      exact point_abs_pos a p
    }
    have t'r: t' ≠ r := by{
      suffices: r < t'
      · linarith
      suffices : r < 0 ∧ 0 ≤ t'
      · linarith
      constructor
      · unfold r r'
        simp
        exact point_abs_neq ab
      unfold t'
      exact point_abs_pos a q
    }
    have hr: r ≠ 0 := by{
      unfold r r'
      simp
      contrapose ab
      simp at *
      exact abs_zero_imp_same a b ab
    }
    have tt': t = t' := by{
      apply t_div_r_sub_t_inj hr tr t'r
      unfold r
      calc
        t / (-r' - t) =  -t' / (t' + r') := by{
          rw[← h]
          by_cases h0: r' = -t
          · rw[h0]
            simp
          have s1: -r' - t ≠ 0 := by{
            contrapose h0
            simp at *
            linarith
          }
          have s2: t + r' ≠ 0 := by{
            contrapose h0
            simp at *
            linarith
          }
          field_simp
          ring
        }
          _= t' / (-r' -t') := by{
            by_cases h0: r' = -t'
            · rw[h0]
              simp
            have s1: -r' - t' ≠ 0 := by{
              contrapose h0
              simp at *
              linarith
            }
            have s2: t' + r' ≠ 0 := by{
              contrapose h0
              simp at *
              linarith
            }
            field_simp
            ring
          }
    }
    clear h tr t'r hr
    unfold t t' at tt'
    clear t t'
    unfold r' at inp inq
    clear r r'
    obtain ⟨R, hR⟩ := colinear_go_along ab hp
    obtain ⟨R', hR'⟩ := colinear_go_along ab hq
    suffices : R = R'
    · rw[hR,hR',this]
    rw[hR,hR', go_along_abs1, go_along_abs1] at tt'
    have RR': R = R' ∨ R = -R' := by{
      exact abs_eq_abs.mp tt'
    }
    obtain RR'|RR' := RR'
    · tauto
    rw[hR] at inp'
    apply in_between_symm at inp'
    obtain Rz := in_between_go_along' ab inp'
    rw[hR'] at inq'
    apply in_between_symm at inq'
    obtain R'z := in_between_go_along' ab inq'
    rw[RR'] at Rz
    have : R' = 0 := by{
      linarith
    }
    rw[this]
    rw[this] at RR'
    simp at RR'
    rw[RR']
    repeat
      tauto


    unfold sQuot at h
    simp [*] at h
    unfold in_between at inp inq
    have hbq: point_abs b q = point_abs a q - point_abs a b := by{
      linarith
    }
    rw[point_abs_symm b q] at hbq
    rw[hbq, ← inp, point_abs_symm p a] at h
    set t := point_abs a p
    set t' := point_abs a q
    set r := point_abs a b
    have ht: -1 < -t / (t + r) := by{
      have tr: 0 < t +r := by{
        unfold t r
        have hht: 0 < point_abs a p := by{
          exact point_abs_neq fun a_1 ↦ pa (id (Eq.symm a_1))
        }
        have hhr: 0 ≤ point_abs a b := by{exact point_abs_pos a b}
        linarith
      }
      suffices : -(t+r) < -t
      · set s := t+r
        have this': -1 = -s / s := by{field_simp}
        rw[this']
        exact div_lt_div_of_pos_right this tr
      simp
      unfold r
      exact point_abs_neq ab
    }
    by_cases p0: t'-r = 0
    · rw[p0] at h
      simp at h
      obtain h|h := h
      · unfold t at h
        have : a = p := by{exact abs_zero_imp_same a p h}
        tauto
      have tr: 0 < t +r := by{
        unfold t r
        have hht: 0 < point_abs a p := by{
          exact point_abs_neq fun a_1 ↦ pa (id (Eq.symm a_1))
        }
        have hhr: 0 ≤ point_abs a b := by{exact point_abs_pos a b}
        linarith
      }
      exfalso
      linarith
    by_cases t'r: 0 < t'-r
    · suffices: -t' / (t' - r) < -1
      exfalso
      linarith
      set s := t'-r
      suffices: -t' < -s
      · have this': -1 = -s / s := by{field_simp}
        rw[this']
        simp
        exact div_lt_div_of_pos_right this t'r
      unfold s
      simp
      unfold r
      exact point_abs_neq ab
    have tr: 0 < t +r := by{
        unfold t r
        have hht: 0 < point_abs a p := by{
          exact point_abs_neq fun a_1 ↦ pa (id (Eq.symm a_1))
        }
        have hhr: 0 ≤ point_abs a b := by{exact point_abs_pos a b}
        linarith
    }
    field_simp at h
    have tt': t' = -t := by{
      have r0: r ≠ 0 := by{
        unfold r
        contrapose ab
        simp at *
        exact abs_zero_imp_same a b ab
      }
      suffices : t* -r = t' * r
      · calc
          t' = 1/r * (t'*r) := by{field_simp}
            _= 1/r * (t * -r) := by{rw[← this]}
            _= -t := by{field_simp}
      calc
        t* -r = t' * (t + r) - t*t' := by{rw[← h]; ring}
          _= t'*r := by{ring}
    }
    unfold t t' at tt'
    have t1: 0 < point_abs a q := by{exact point_abs_neq fun a_1 ↦ qa (id (Eq.symm a_1))}
    have t2: 0 ≤ point_abs a p := by{exact point_abs_pos a p}
    exfalso
    linarith

    obtain inq|inq := inq
    unfold sQuot at h
    simp [*] at h
    obtain ⟨R, hR⟩ := colinear_go_along ab hp
    obtain ⟨R', hR'⟩ := colinear_go_along ab hq
    rw[point_abs_symm p b, point_abs_symm q b, hR, hR', go_along_abs1, go_along_abs1, go_along_abs2, go_along_abs2] at h
    rw[hR] at inp
    rw[hR'] at inq
    apply in_between_symm at inq
    obtain u :=  in_between_go_along' ab inq
    rw[go_along_symm] at inp
    obtain o := in_between_go_along' (Ne.symm ab) inp
    rw[point_abs_symm] at o
    have abpos: 0 < point_abs a b := by{
      exact point_abs_neq ab
    }
    have Rpos: 0 < R := by{linarith}
    have diffpos: 0 < point_abs a b - R' := by{linarith}
    have diffneg: point_abs a b - R < 0 := by{
      suffices: point_abs a b - R ≠ 0
      · contrapose o
        simp at *
        contrapose this
        simp at *
        linarith
      contrapose pb
      simp at *
      have : R = point_abs a b := by{linarith}
      rw[hR, this, go_along_point_abs]
    }
    set r := point_abs a b
    have aR: abs R = R := by{exact abs_of_pos Rpos}
    have aR': abs R' = -R' := by{exact abs_of_nonpos u}
    have arR: abs (r - R) = - (r-R) := by{exact abs_of_neg diffneg}
    have arR': abs (r-R') = r-R' := by{exact abs_of_pos diffpos}
    rw[aR, aR', arR, arR'] at h
    field_simp at h
    have Rrsub : R-r ≠ 0 := by{
      contrapose diffneg
      simp at *
      linarith
    }
    field_simp at h
    rw[hR,hR']
    suffices: R = R'
    · rw[this]
    suffices: R*r = R'*r
    · have r0: 0 < r := by{
      unfold r
      exact abpos
      }
      calc
        R = 1/r * (R'*r) := by{rw[← this]; field_simp}
          _= R' := by{field_simp}
    calc
      R*r = (-(R' * (R - r))) + R*R' := by{rw[← h]; ring}
        _= R'*r := by{ring}
    repeat
      tauto


    unfold sQuot at h
    simp [*] at h
    obtain ⟨R, hR⟩ := colinear_go_along ab hp
    obtain ⟨R', hR'⟩ := colinear_go_along ab hq
    suffices : R = R'
    · rw[hR,hR',this]
    rw[point_abs_symm p b, point_abs_symm q b, hR, hR', go_along_abs1, go_along_abs1, go_along_abs2, go_along_abs2] at h
    rw[hR, go_along_symm] at inp
    rw[hR', go_along_symm] at inq
    obtain u :=  in_between_go_along' (Ne.symm ab) inq
    obtain o :=  in_between_go_along' (Ne.symm ab) inp
    rw[point_abs_symm b a] at u o
    set r := point_abs a b
    have : 0 < r := by{
      unfold r
      exact point_abs_neq ab
    }
    have aR: abs R = R := by{
      simp
      linarith
    }
    have aR': abs R' = R' := by{
      simp
      linarith
    }
    have arR: abs (r - R) = -(r - R) := by{exact abs_of_nonpos o}
    have arR': abs (r - R') = -(r - R') := by{exact abs_of_nonpos u}
    have rR: R ≠ r := by{
      contrapose pb
      simp at *
      rw[hR, pb]
      unfold r
      rw[go_along_point_abs]
    }
    have rR': R' ≠ r := by{
      contrapose qb
      simp at *
      rw[hR', qb]
      unfold r
      rw[go_along_point_abs]
    }
    rw[aR,aR', arR, arR'] at h
    have r0: r ≠ 0 := by{
      exact point_abs_neq_zero ab
    }
    apply t_div_r_sub_t_inj r0 rR rR'
    calc
      R / (r - R) = -R' / -(r - R') := by{
        rw[← h]
        set s := r - R
        by_cases s0: s=0
        · rw[s0]
          simp
        field_simp
      }
            _= R' / (r-R') := by{
              set s := r - R'
              by_cases s0: s=0
              · rw[s0]
                simp
              simp
              }
    repeat
      tauto
  have snn: 0 < sQuot a p b := by{
    contrapose l0
    simp at *
    exact lt_of_le_of_ne l0 e0
  }
  have snn': 0 < sQuot a q b := by{rw[← h]; assumption}
  obtain ⟨l, ll, hhp⟩ := squot_pos.1 snn
  obtain ⟨lll, llll, hhq⟩ := squot_pos.1 snn'
  clear l ll lll llll --lol
  unfold sQuot at h
  simp [*] at h
  obtain ⟨R,hR⟩ := colinear_go_along ab hp
  obtain ⟨R',hR'⟩ := colinear_go_along ab hq
  suffices: R = R'
  · rw[hR,hR', this]
  rw[hR] at hhp
  rw[hR'] at hhq
  obtain ⟨hR1,hR2⟩ := in_between_go_along ab hhp
  obtain ⟨hR'1, hR'2⟩ := in_between_go_along ab hhq
  rw[point_abs_symm p b, point_abs_symm q b, hR, hR', go_along_abs1, go_along_abs1, go_along_abs2, go_along_abs2] at h
  have aR: abs R = R := by{simp [*]}
  have aR': abs R' = R' := by{simp [*]}
  set r := point_abs a b
  have arR: abs (r-R) = r - R := by{simp [*]}
  have arR': abs (r-R') = r - R' := by{simp [*]}
  rw[aR, aR', arR, arR'] at h
  have r0: r ≠ 0 := by{
    contrapose ab
    simp at *
    exact abs_zero_imp_same a b ab
  }
  apply t_div_r_sub_t_inj r0
  · contrapose pb
    simp at *
    rw[hR, pb]
    unfold r
    rw[go_along_point_abs]
  · contrapose qb
    simp at *
    rw[hR', qb]
    unfold r
    rw[go_along_point_abs]
  assumption
  repeat
    tauto
}

/-Similarly, we want sQuotL to be injective as well. Compared with squot_inj, there isn't a relatively
obvious formulation for this. However following version will suffice:-/

lemma squotl_inj{a b p : Point}{L R : Line}(ab : a ≠ b)(hp: ¬Lies_on p (Line_through ab))(hL: Lies_on p L)(hR: Lies_on p R)(h: sQuotL L a b = sQuotL R a b)(sL: sQuotL L a b ≠ 0)(sR: sQuotL R a b ≠ 0): L = R := by{
  by_cases par: Parallel L (Line_through ab)
  · apply lines_eq_parallel_point p
    · tauto
    apply parallel_trans par
    apply (squotl_neg_one ab).1
    rw[← h]
    apply parallel_symm at par
    exact (squotl_neg_one ab).2 par
  have npar: ¬Parallel (Line_through ab) R := by{
    contrapose par
    simp at *
    apply parallel_symm
    apply (squotl_neg_one ab).1
    rw[h]
    exact (squotl_neg_one ab).2 par
  }
  unfold sQuotL at h
  apply not_parallel_symm at npar
  simp [*] at h
  suffices: Intersection par = Intersection npar
  · set I := Intersection par
    have Ip : I ≠ p := by{
      contrapose hp
      simp at *
      rw[← hp]
      unfold I
      exact intersection_mem_right par
    }
    calc
      L = Line_through Ip := by{
        apply line_through_unique
        constructor
        · unfold I
          exact intersection_mem_left par
        assumption
      }
        _= R := by{
          symm
          apply line_through_unique
          constructor
          · rw[this]
            exact intersection_mem_left npar
          assumption
        }
  apply squot_inj ab
  · exact intersection_mem_right par
  · exact intersection_mem_right npar
  · contrapose sL
    simp at *
    unfold sQuotL
    simp [ab, par]
    apply squot_zero.2
    tauto
  · contrapose sL
    simp at *
    unfold sQuotL
    simp [ab, par]
    apply squot_zero.2
    tauto
  · contrapose sR
    simp at *
    unfold sQuotL
    simp [ab, npar]
    apply squot_zero.2
    tauto
  · contrapose sR
    simp at *
    unfold sQuotL
    simp [ab, npar]
    apply squot_zero.2
    tauto
  assumption
}
--also they cant intersect on a or b help

/-Next we deal with a very annoying but unfortunately very important edge case. For this let's quickly define
Cevians (= line going through a vertice of a Triangle). We don't allow Cevians to be the same as a triangle side,
else sQuotL breaks (same happens in ordinary definitions, so this is a natural choice I think).-/

/-Furthermore (similar with Angle_A) I use one deifnition per vertice. This could technically be avoided, but I mean come on...-/

def Cevian_A(T : Triangle)(L : Line): Prop :=
  Lies_on T.a L ∧ L ≠ tri_ab T ∧ L ≠ tri_ca T

def Cevian_B(T : Triangle)(L : Line): Prop :=
  Lies_on T.b L ∧ L ≠ tri_bc T ∧ L ≠ tri_ab T

def Cevian_C(T : Triangle)(L : Line): Prop :=
  Lies_on T.c L ∧ L ≠ tri_ca T ∧ L ≠ tri_bc T

/-We will need the following:-/
lemma cevians_not_same_ab{T : Triangle}{L U : Line}(hL: Cevian_A T L)(hU: Cevian_B T U): L ≠ U := by{
  by_contra h0
  rw[← h0] at hU
  unfold Cevian_A Cevian_B at *
  obtain ⟨aL,abL,caL⟩ := hL
  obtain ⟨bL, bcL, abL⟩ := hU
  clear abL
  contrapose abL
  unfold tri_ab
  simp
  apply line_through_unique
  tauto
}

/-Their respective sQuotL's are not zero:-/
@[simp] lemma squotl_cevian_a_neq_zero{T : Triangle}{L : Line}(hL: Cevian_A T L): sQuotL L T.b T.c ≠ 0 := by{
  unfold sQuotL
  by_cases Lbc: Parallel L (qLine_through T.b T.c)
  · simp [*]
  simp [*]
  by_contra h0
  apply squot_zero.1 at h0
  obtain h0|h0 := h0
  · suffices: L = tri_ab T
    · unfold Cevian_A at hL
      tauto
    unfold tri_ab
    apply line_through_unique
    unfold Cevian_A at hL
    constructor
    · tauto
    rw[← h0]
    exact intersection_mem_left (of_eq_false (eq_false Lbc))
  suffices: L = tri_ca T
  · unfold Cevian_A at hL
    tauto
  unfold tri_ca
  apply line_through_unique
  unfold Cevian_A at hL
  constructor
  · rw[← h0]
    exact intersection_mem_left (of_eq_false (eq_false Lbc))
  tauto
}

@[simp] lemma squotl_cevian_b_neq_zero{T : Triangle}{L : Line}(hL: Cevian_B T L): sQuotL L T.c T.a ≠ 0 := by{
  unfold sQuotL
  by_cases Lca: Parallel L (qLine_through T.c T.a)
  · simp [*]
  simp [*]
  by_contra h0
  apply squot_zero.1 at h0
  obtain h0|h0 := h0
  · suffices: L = tri_bc T
    · unfold Cevian_B at hL
      tauto
    unfold tri_bc
    apply line_through_unique
    unfold Cevian_B at hL
    constructor
    · tauto
    rw[← h0]
    exact intersection_mem_left (of_eq_false (eq_false Lca))
  suffices: L = tri_ab T
  · unfold Cevian_B at hL
    tauto
  unfold tri_ab
  apply line_through_unique
  unfold Cevian_B at hL
  constructor
  · rw[← h0]
    exact intersection_mem_left (of_eq_false (eq_false Lca))
  tauto
}

@[simp] lemma squotl_cevian_c_neq_zero{T : Triangle}{L : Line}(hL: Cevian_C T L): sQuotL L T.a T.b ≠ 0 := by{
  unfold sQuotL
  by_cases Lab: Parallel L (qLine_through T.a T.b)
  · simp [*]
  simp [*]
  by_contra h0
  apply squot_zero.1 at h0
  obtain h0|h0 := h0
  · suffices: L = tri_ca T
    · unfold Cevian_C at hL
      tauto
    unfold tri_ca
    apply line_through_unique
    unfold Cevian_C at hL
    constructor
    · tauto
    rw[← h0]
    exact intersection_mem_left (of_eq_false (eq_false Lab))
  suffices: L = tri_bc T
  · unfold Cevian_C at hL
    tauto
  unfold tri_bc
  apply line_through_unique
  unfold Cevian_C at hL
  constructor
  · rw[← h0]
    exact intersection_mem_left (of_eq_false (eq_false Lab))
  tauto
}

/-To prove the special case, we will need two lemmas
First we show (basically) the converse of ceva_spec, the we show that sQuot is surjective for fixed a, b with a ≠ b.-/

/-Note that:-/
lemma cevian_intersection_not_on_perimiter{T : Triangle}{L U : Line}(hL: Cevian_A T L)(hU: Cevian_B T U)(h: ¬Parallel L U): not_on_perimiter (Intersection h) T := by{
  set p := Intersection h
  have pa: p ≠ T.a := by{
    by_contra h0
    suffices: U = tri_ab T
    · unfold Cevian_B at hU
      tauto
    unfold tri_ab
    apply line_through_unique
    constructor
    · rw[← h0]
      exact intersection_mem_right h
    unfold Cevian_B at hU
    tauto
  }
  have pb: p ≠ T.b := by{
    by_contra h0
    suffices: L = tri_ab T
    · unfold Cevian_A at hL
      tauto
    unfold tri_ab
    apply line_through_unique
    constructor
    · unfold Cevian_A at hL
      tauto
    rw[← h0]
    exact intersection_mem_left h
  }
  unfold not_on_perimiter
  by_contra h0
  have h0': Lies_on p (tri_ab T) ∨ Lies_on p (tri_bc T) ∨ Lies_on p (tri_ca T) := by{tauto}
  clear h0
  obtain h0|h0|h0 := h0'
  · suffices: L = tri_ab T
    · unfold Cevian_A at hL
      tauto
    unfold tri_ab
    apply line_through_unique
    constructor
    · unfold Cevian_A at hL
      tauto
    have hL': L = Line_through pa := by{
      apply line_through_unique
      constructor
      · exact intersection_mem_left h
      unfold Cevian_A at hL
      tauto
    }
    rw[hL']
    unfold Lies_on Line_through
    unfold Lies_on tri_ab Line_through at h0
    simp at *
    apply colinear_perm13
    apply colinear_perm12
    assumption
  · suffices : U = tri_bc T
    · unfold Cevian_B at hU
      tauto
    unfold tri_bc
    apply line_through_unique
    constructor
    · unfold Cevian_B at hU
      tauto
    have hU': U = Line_through pb := by{
      apply line_through_unique
      constructor
      · exact intersection_mem_right h
      unfold Cevian_B at hU
      tauto
    }
    rw[hU']
    unfold Lies_on Line_through
    unfold Lies_on tri_bc Line_through at h0
    simp at *
    apply colinear_perm13
    apply colinear_perm12
    assumption
  · suffices : L = tri_ca T
    · unfold Cevian_A at hL
      tauto
    unfold tri_ca
    apply line_through_unique
    constructor
    swap
    · unfold Cevian_A at hL
      tauto
    have hL': L = Line_through pa := by{
      apply line_through_unique
      constructor
      · exact intersection_mem_left h
      unfold Cevian_A at hL
      tauto
    }
    rw[hL']
    unfold Lies_on Line_through
    unfold Lies_on tri_ca Line_through at h0
    simp at *
    apply colinear_perm13
    assumption
}

theorem ceva_spec_converse{T : Triangle}{L U R : Line}(hL: Cevian_A T L)(hU: Cevian_B T U)(hR: Cevian_C T R)(LU: ¬Parallel L U)(h: sQuotL L T.b T.c * sQuotL U T.c T.a * sQuotL R T.a T.b = 1): Copunctal L U R := by{
  apply copunctal_simp
  · unfold lines_not_same
    left
    exact cevians_not_same_ab hL hU
  use Intersection LU
  simp [*, intersection_mem_left, intersection_mem_right]
  set p := Intersection LU
  have pc : p ≠ T.c := by{
    by_contra h0
    suffices: L = tri_ca T
    · unfold Cevian_A at hL
      tauto
    unfold tri_ca
    apply line_through_unique
    constructor
    · rw[← h0]
      unfold p
      exact intersection_mem_left LU
    unfold Cevian_A at hL
    tauto
  }
  have pa: p ≠ T.a := by{
    by_contra h0
    suffices: U = tri_ab T
    · unfold Cevian_B at hU
      tauto
    unfold tri_ab
    apply line_through_unique
    constructor
    · rw[← h0]
      exact intersection_mem_right LU
    unfold Cevian_B at hU
    tauto
  }
  have pb: p ≠ T.b := by{
    by_contra h0
    suffices: L = tri_ab T
    · unfold Cevian_A at hL
      tauto
    unfold tri_ab
    apply line_through_unique
    constructor
    · unfold Cevian_A at hL
      tauto
    rw[← h0]
    exact intersection_mem_left LU
  }
  have hp: not_on_perimiter p T := by{
    exact cevian_intersection_not_on_perimiter hL hU LU
  }
  suffices: R = Line_through pc
  · rw[this]
    exact line_through_mem_left pc
  rw[← qline_through_line_through]
  have p1: ¬Lies_on T.c (Line_through (tri_diff_ab T)) := by{
    unfold Lies_on Line_through
    simp
    suffices: noncolinear T.a T.b T.c
    · unfold noncolinear at this
      tauto
    exact T.noncolinear
  }
  set R' := qLine_through p T.c
  have CR': Cevian_C T R' := by{
    unfold Cevian_C
    constructor
    · exact qline_through_mem_right p T.c
    constructor
    · by_contra h0
      have : R' = L := by{
        have l: L = Line_through pa := by{
          unfold Cevian_A at hL
          apply line_through_unique
          simp [*]
          exact intersection_mem_left LU
        }
        rw[l]
        apply line_through_unique
        constructor
        · exact qline_through_mem_left p T.c
        rw[h0]
        exact tri_a_on_ca T
      }
      unfold Cevian_A at hL
      rw[this] at h0
      tauto
    by_contra h0
    have : R' = U := by{
      have r: U = Line_through pb := by{
        unfold Cevian_B at hU
        apply line_through_unique
        simp [*]
        exact intersection_mem_right LU
      }
      rw[r]
      apply line_through_unique
      constructor
      · exact qline_through_mem_left p T.c
      rw[h0]
      exact tri_b_on_bc T
    }
    unfold Cevian_B at hU
    rw[this] at h0
    tauto
  }
  have hL': L = Line_through pa := by{
    apply line_through_unique
    constructor
    · exact intersection_mem_left LU
    unfold Cevian_A at hL
    tauto
  }
  have hU': U = Line_through pb := by{
    apply line_through_unique
    constructor
    · exact intersection_mem_right LU
    unfold Cevian_B at hU
    tauto
  }
  have hR': sQuotL L T.b T.c * sQuotL U T.c T.a * sQuotL R' T.a T.b = 1 := by{
    rw[← ceva_spec T p hp, qline_through_symm T.b p, qline_through_symm T.a p]
    simp [*]
    rw[← hL', ← hU']
    field_simp
    unfold R'
    rw[qline_through_symm]
  }
  apply squotl_inj (tri_diff_ab T) p1
  · unfold Cevian_C at hR
    tauto
  · exact qline_through_mem_right p T.c
  swap
  · exact squotl_cevian_c_neq_zero hR
  swap
  · exact squotl_cevian_c_neq_zero CR'
  calc
    sQuotL R T.a T.b = 1/ (sQuotL L T.b T.c * sQuotL U T.c T.a) := by{
      field_simp [squotl_cevian_a_neq_zero, squotl_cevian_b_neq_zero]
      rw[← h]
      ring
    }
      _= sQuotL (qLine_through p T.c) T.a T.b := by{
        field_simp
        rw[← hR']
        unfold R'
        rw[← qline_through_line_through]
        ring
      }
}

/-Now the proof that squot is surjective (except for -1):-/
lemma squot_surj{a b : Point}{t : ℝ}(ht : t ≠ -1)(ab : a ≠ b): ∃(p : Point), colinear a b p ∧ sQuot a p b = t := by{
  by_cases t0: t = 0
  · use a
    simp [colinear_self, t0]
    refine squot_zero.mpr ?h.a
    tauto
  by_cases tpos: 0 < t
  · use go_along a b (((t*(point_abs a b)))/(t+1))
    constructor
    · exact go_along_colinear a b (((t*(point_abs a b)))/(t+1))
    have : in_between a b (go_along a b (((t*(point_abs a b)))/(t+1))) := by{
      sorry
    }
    unfold sQuot
    simp [this]
    rw[go_along_abs1, point_abs_symm (go_along a b (t * point_abs a b / (t + 1))), go_along_abs2]
    sorry
  sorry
}

/-Similarly, sQuotL is surjective for Cevians. We will only need the version for "C", so we don't bother
doing anything further:-/
lemma squotl_surj_cevian_c{T : Triangle}{t : ℝ}(ht: t ≠ 0): ∃(L : Line), Cevian_C T L ∧ sQuotL L T.a T.b = t := by{
  by_cases negone: t = -1
  · use parallel_through (tri_ab T) T.c
    constructor
    · unfold Cevian_C
      constructor
      · exact point_lies_on_parallel_through (tri_ab T) T.c
      constructor
      · by_contra h0
        have par: Parallel (tri_ab T) (tri_ca T) := by{
          rw[← h0]
          exact parallel_through_is_parallel (tri_ab T) T.c
        }
        obtain := tri_not_parallel_ab_ca T
        contradiction
      by_contra h0
      have par: Parallel (tri_ab T) (tri_bc T) := by{
        rw[← h0]
        exact parallel_through_is_parallel (tri_ab T) T.c
      }
      obtain := tri_not_parallel_ab_bc T
      contradiction
    unfold sQuotL
    obtain u := parallel_through_is_parallel (tri_ab T) T.c
    apply parallel_symm at u
    nth_rw 2[tri_ab] at u
    rw[← qline_through_line_through] at u
    simp [*]
  obtain ab := tri_diff_ab T
  obtain ⟨p, hp,hpt⟩ := squot_surj negone ab
  have pa: p ≠ T.a := by{
    contrapose ht
    simp at *
    rw[← hpt]
    refine squot_zero.mpr ?_
    tauto
  }
  have pb: p ≠ T.b := by{
    contrapose ht
    simp at *
    rw[← hpt]
    refine squot_zero.mpr ?_
    tauto
  }
  have pc: p ≠ T.c := by{
    by_contra h0
    have : noncolinear T.a T.b p := by{
      rw[h0]
      exact T.noncolinear
    }
    unfold noncolinear at this
    tauto
  }
  have lp: Lies_on p (tri_ab T) := by{
    unfold tri_ab Line_through Lies_on
    assumption
  }
  use qLine_through p T.c
  constructor
  · unfold Cevian_C
    constructor
    · exact qline_through_mem_right p T.c
    constructor
    · by_contra h0
      suffices : p = T.a
      · contradiction
      calc
        p = Intersection (tri_not_parallel_ab_ca T) := by{
          apply intersection_unique
          constructor
          · assumption
          rw[← h0]
          exact qline_through_mem_left p T.c
        }
          _= T.a := by{
            symm
            apply intersection_unique
            constructor
            · exact tri_a_on_ab T
            exact tri_a_on_ca T
          }
    by_contra h0
    suffices : p = T.b
    · contradiction
    calc
        p = Intersection (tri_not_parallel_ab_bc T) := by{
          apply intersection_unique
          constructor
          · assumption
          rw[← h0]
          exact qline_through_mem_left p T.c
        }
          _= T.b := by{
            symm
            apply intersection_unique
            constructor
            · exact tri_b_on_ab T
            exact tri_b_on_bc T
          }
  unfold sQuotL
  have g: ¬Parallel (qLine_through p T.c) (qLine_through T.a T.b) := by{
    by_contra h0
    suffices goal : (qLine_through p T.c) = (qLine_through T.a T.b)
    · have : Lies_on T.c (tri_ab T) := by{
        unfold tri_ab
        rw[← qline_through_line_through, ← goal]
        exact qline_through_mem_right p T.c
      }
      contrapose this
      exact tri_c_not_on_ab T
    refine lines_eq_parallel_point_ex h0 ?goal.a
    use p
    constructor
    · exact qline_through_mem_left p T.c
    simp [ab]
    unfold Lies_on Line_through
    simp
    assumption
  }
  simp [g]
  have hp' : p = Intersection g := by{
    apply intersection_unique
    constructor
    · exact qline_through_mem_left p T.c
    simp [ab]
    unfold Lies_on Line_through
    simp
    assumption
  }
  rw[← hp', hpt]
}

theorem squotl_parallel{T : Triangle}{L U R : Line}(hL: Cevian_A T L)(hU: Cevian_B T U)(hR: Cevian_C T R)(LU: Parallel L U)(UR: Parallel U R): sQuotL L T.b T.c * sQuotL U T.c T.a * sQuotL R T.a T.b = 1 := by{
  have npR: ¬Parallel R (qLine_through T.a T.b) := by{
    by_contra h0
    suffices goal: Parallel U (tri_ab T)
    · have : U = tri_ab T := by{
        apply lines_eq_parallel_point_ex
        · assumption
        use T.b
        constructor
        · unfold Cevian_B at hU
          tauto
        exact tri_b_on_ab T
      }
      unfold Cevian_B at hU
      tauto
    unfold tri_ab
    rw[← qline_through_line_through]
    exact parallel_trans UR h0
  }

  sorry
}

/-With this we can now state and prove Ceva's theorem in its whole glory:-/

/-We have have more or less proved 3 out of 4 cases for this theorem, so the actualy proof doesn't become too compilcated now:-/

theorem Ceva{T : Triangle}{L U R : Line}(hL: Cevian_A T L)(hU: Cevian_B T U)(hR: Cevian_C T R): Copunctal L U R ∨ ((Parallel L U) ∧ (Parallel U R)) ↔ sQuotL L T.b T.c * sQuotL U T.c T.a * sQuotL R T.a T.b = 1 := by{
  constructor
  intro h
  obtain h|h := h

  sorry
  sorry
  sorry
}
