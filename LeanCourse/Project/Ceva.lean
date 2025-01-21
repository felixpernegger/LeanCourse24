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

theorem Ceva_spec(T : Triangle)(p : Point)(hp: not_on_perimiter p T): (sQuotL (qLine_through T.a p) T.b T.c) * (sQuotL (qLine_through T.b p) T.c T.a) * (sQuotL (qLine_through T.c p) T.a T.b) = 1 := by{
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

lemma squot_inj{a b p q: Point}(ab : a ≠ b)(hp: Lies_on p (Line_through ab))(hq : Lies_on q (Line_through ab))(pa: p ≠ a)(pb: p ≠ b)(qa: q ≠ a)(qb: q ≠ b)(h: sQuot a p b = sQuot a q b): p = q := by{
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
      sorry
    }
    have ninq: ¬in_between a b q := by{
      sorry
    }
    unfold sQuot at h
    simp [*] at h
    sorry
  sorry
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

--this could be proven by first showing a "weak" converse for non parallel lines. This also could be reused later
--for the main proof, so i am not actually doing extra work

theorem squotl_parallel{T : Triangle}{L U R : Line}(hL: Cevian_A T L)(hU: Cevian_B T U)(hR: Cevian_C T R)(LU: Parallel L U)(UR: Parallel U R): sQuotL L T.b T.c * sQuotL U T.c T.a * sQuotL R T.a T.b = 1 := by{
  sorry
}

/-With this we can now state and prove Ceva's theorem in its whole glory:-/

theorem Ceva{T : Triangle}{L U R : Line}(hL: Cevian_A T L)(hU: Cevian_B T U)(hR: Cevian_C T R): Copunctal L U R ∨ ((Parallel L U) ∧ (Parallel U R)) ↔ sQuotL L T.b T.c * sQuotL U T.c T.a * sQuotL R T.a T.b = 1 := by{
  constructor
  intro h
  obtain h|h|h := h

  sorry
  sorry
  sorry
}
