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

lemma squotl_not_parallel{p : Point}{a b c : Point}(np: qnot_on_perimiter_points p a b c)(h : ¬Parallel (qLine_through a p) (qLine_through b c)): sQuotL (qLine_through a p) b c = area_points b p a / area_points a p c := by{
  sorry
}

/-Using this Ceva theorem can be formulated as followed:-/

theorem Ceva(T : Triangle)(p : Point)(hp: not_on_perimiter p T): (sQuotL (qLine_through T.a p) T.b T.c) * (sQuotL (qLine_through T.b p) T.c T.a) * (sQuotL (qLine_through T.c p) T.a T.b) = 1 := by{
  /-The interesting case is when nothing is parallel, we have to get the first though.-/
  have ab: T.a ≠ T.b := by{exact tri_diff_ab T}
  have bc: T.b ≠ T.c := by{exact tri_diff_bc T}
  have ca: T.c ≠ T.a := by{exact tri_diff_ca T}
  have ha: p ≠ T.a := by{
    unfold not_on_perimiter tri_ab Lies_on Line_through at hp
    simp at hp
    contrapose hp
    simp at hp
    rw[hp]
    have : colinear T.a T.b T.a := by{
      apply colinear_self
      tauto
    }
    tauto
  }
  have hb: p ≠ T.b := by{
    unfold not_on_perimiter tri_ab Lies_on Line_through at hp
    simp at hp
    contrapose hp
    simp at hp
    rw[hp]
    have : colinear T.a T.b T.b := by{
      apply colinear_self
      tauto
    }
    tauto
  }
  have hc: p ≠ T.c := by{
    unfold not_on_perimiter tri_bc Lies_on Line_through at hp
    simp at hp
    contrapose hp
    simp at hp
    rw[hp]
    have : colinear T.b T.c T.c := by{
      apply colinear_self
      tauto
    }
    tauto
  }
  by_cases hbc: Parallel (qLine_through T.a p) (tri_bc T)
  · unfold tri_bc at hbc
    nth_rw 1[sQuotL]
    simp [*]
    by_cases hca: Parallel (qLine_through T.b p) (tri_ca T)
    · unfold tri_ca at hca
      nth_rw 1[sQuotL]
      simp [*]
      unfold sQuotL
      have hhp: p = reflection_point_point T.c (pmidpoint T.a T.b) := by{
        symm at ha
        symm at hb
        simp [*] at *
        have s0: ¬ Parallel (Line_through ha) (Line_through hb) := by{
          by_contra h0
          have par: Parallel (tri_bc T) (tri_ca T) := by{
            unfold tri_bc tri_ca
            have : Parallel (Line_through bc) (Line_through hb) := by{
              apply parallel_symm at hbc
              exact parallel_trans hbc h0
            }
            exact parallel_trans this hca
          }
          obtain u := tri_not_parallel_bc_ca T
          contradiction
        }
        have s1: p = Intersection s0 := by{
          apply intersection_unique
          constructor
          · exact line_through_mem_right ha
          exact line_through_mem_right hb
        }
        rw[s1]
        symm
        apply intersection_unique
        have t1: Line_through ha = parallel_through (tri_bc T) T.a := by{
          apply parallel_through_unique
          constructor
          · exact line_through_mem_left ha
          unfold tri_bc
          apply parallel_symm
          exact hbc
        }
        have t2: Line_through hb = parallel_through (tri_ca T) T.b := by{
          apply parallel_through_unique
          constructor
          · exact line_through_mem_left hb
          unfold tri_ca
          apply parallel_symm
          exact hca
        }
        rw[t1,t2]
        clear t1 t2 s1 s0 hbc hca hp ha hb hc p
        constructor
        · have q1: reflection_point_point T.c (pmidpoint T.a T.b) ≠ T.a := by{
            by_contra h0
            unfold reflection_point_point pmidpoint pneg padd p_scal_mul at *
            simp at h0
            contrapose bc
            obtain ⟨a,b,c,hh⟩ := T
            simp at *
            ext
            have : ({ x := 2 * ((a.x + b.x) / 2) + -c.x } : Point).x = a.x := by{
              rw[h0]
            }
            simp at this
            field_simp at this
            calc
              b.x = -a.x + (a.x + b.x + -c.x) + c.x := by{ring}
                _= -a.x + (a.x) + c.x := by{rw[this]}
                _= c.x := by{ring}
          }
          suffices g : Parallel (Line_through q1) (tri_bc T)
          · have : Line_through q1 = parallel_through (tri_bc T) T.a := by{
            apply parallel_through_unique
            constructor
            · exact line_through_mem_right q1
            apply parallel_symm
            assumption
            }
            rw[← this]
            apply line_through_mem_left
          unfold tri_bc
          refine (parallel_quot q1 (tri_bc.proof_1 T)).mpr ?g.a
          unfold reflection_point_point pmidpoint p_scal_mul padd pneg
          simp
          suffices : ((2 * ((T.a.x + T.b.x) / 2) + -T.c.x - T.a.x) / (T.b.x - T.c.x)) = (1 : ℂ)
          · rw[this]
            simp
          obtain u := sub_neq_zero bc
          field_simp
          ring
        sorry
      }
      have g: ¬Parallel (qLine_through T.c p) (qLine_through T.a T.b) := by{
        by_contra h0
        obtain h'|h' := (parallel_def (qLine_through T.c p) (qLine_through T.a T.b)).1 h0
        · suffices g: Lies_on (pmidpoint T.a T.b) (qLine_through T.c p) ∧ Lies_on (pmidpoint T.a T.b) (qLine_through T.a T.b)
          have : (pmidpoint T.a T.b) ∈ ∅ := by{
            rw[← h']
            simp
            unfold Lies_on at g
            tauto
          }
          tauto

          constructor
          · simp [Ne.symm hc]
            unfold Lies_on Line_through
            simp
            rw[hhp]
            unfold pmidpoint reflection_point_point padd pneg p_scal_mul colinear det conj
            simp
            ring
          simp [ab]
          unfold Lies_on Line_through pmidpoint colinear det conj
          simp
          ring
        have h'': qLine_through T.c p = qLine_through T.a T.b := by{
          ext
          rw[h']
        }
        simp [ab] at h''
        have col: colinear T.a T.b p := by{
          suffices: Lies_on p (Line_through ab)
          · unfold Lies_on Line_through at this
            simp at this
            assumption
          rw[← h'']
          exact qline_through_mem_right T.c p
        }
        rw[hhp] at col
        have col2 : colinear T.a T.b T.c := by{
          unfold colinear at *
          have : (0 : ℝ) = -0 := by{norm_num}
          rw[this]
          rw[← col]
          unfold reflection_point_point pmidpoint padd pneg p_scal_mul det conj
          simp
          ring_nf
          have : (starRingEnd ℂ) 2 = 2 := by{exact Complex.conj_eq_iff_re.mpr rfl}
          rw[this]
          field_simp
          ring
        }
        have : noncolinear T.a T.b T.c := by{exact T.noncolinear}
        unfold noncolinear at this
        contradiction
      }
      simp [g]
      have q: Intersection g = pmidpoint T.a T.b := by{
        symm
        apply intersection_unique
        simp [ab, Ne.symm hc]
        constructor
        · unfold Lies_on Line_through
          simp
          rw[hhp]
          unfold reflection_point_point pmidpoint padd pneg p_scal_mul colinear det conj
          simp
          ring
        unfold pmidpoint Line_through Lies_on colinear det conj
        simp
        ring
      }
      rw[q]
      unfold sQuot
      simp [pmidpoint_in_between]
      rw[point_abs_pmidpoint, point_abs_symm (pmidpoint T.a T.b), pmidpoint_symm, point_abs_pmidpoint, point_abs_symm]
      have : point_abs T.b T.a ≠ 0 := by{
        exact point_abs_neq_zero (id (Ne.symm ab))
      }
      field_simp
    sorry
  by_cases hca: Parallel (qLine_through T.b p) (tri_ca T)
  · sorry
  by_cases hab: Parallel (qLine_through T.c p) (tri_ab T)
  · sorry

  /-Now we finally get to the actually interesting part:-/


  sorry
}
