import LeanCourse.Project.Lines
import Mathlib

open Function Set Classical

noncomputable section


/- Lets define parallel lines. We say a line is parallel to itself, so we can get a nice equivalence relation-/
def Parallel(L R : Line) : Prop :=
  ∃p : Point, R = shift_line L p

/-The goal of this section is to prove the parallel postulate from our definition of paralllel
and colinear. This will be quite unconfortable.-/

lemma shift_line_parallel (L : Line)(a : Point): Parallel L (shift_line L a) := by{
  unfold Parallel
  use a
}

/-With colinear alt we can give a neat alternative notion of colinear:-/
lemma parallel_quot {a b c d : Point}(ab : a ≠ b)(cd : c ≠ d): Parallel (Line_through ab) (Line_through cd) ↔ ((a.x-b.x)/(c.x-d.x)).im = 0 := by{
  constructor
  intro h
  unfold Parallel at h
  obtain ⟨p,ph⟩ := h
  have cmem: Lies_on c (Line_through cd) := by {exact line_through_mem_left cd}
  have dmem: Lies_on d (Line_through cd) := by {exact line_through_mem_right cd}
  rw[ph] at cmem
  rw[ph] at dmem
  unfold shift_line at cmem dmem
  unfold Lies_on at cmem dmem
  simp at *
  obtain ⟨r,rh1,rh2⟩ := cmem
  obtain ⟨s,sh1,sh2⟩ := dmem
  by_cases sbo : b=s
  have as: a ≠ s := by{
    rw[sbo] at ab
    assumption
  }
  have uwu: Line_through ab = Line_through as := by{
    apply line_through_unique
    constructor
    exact line_through_mem_left ab
    rw[← sbo]
    exact line_through_mem_right ab
  }
  rw[uwu]at sh1 rh1 ph
  clear ab uwu
  have : b.x = s.x := by{
    rw[sbo]
  }
  rw[this]
  clear this b sbo
  rw[rh2,sh2]
  unfold padd
  simp
  have rs: r ≠ s := by{
    by_contra rs
    have : c=d := by{
      rw[rh2,sh2]
      ext
      unfold padd
      simp
      rw[rs]
    }
    contradiction
  }
  clear ph rh2 sh2 cd c d sh1
  unfold Line_through at rh1
  simp at rh1
  apply colinear_perm12 at rh1
  apply (colinear_alt s a r).1 at rh1
  rw[← rh1]
  obtain ⟨a1,a2⟩ := a
  obtain ⟨s1,s2⟩ := s
  obtain ⟨r1,r2⟩ := r
  simp
  ring


  unfold Line_through at sh1 rh1
  simp at *
  rw[rh2,sh2]
  unfold padd
  simp
  have brs : colinear b r s := by{exact colinear_trans a b r s rh1 sh1 ab}
  have : ((a.x - b.x) / (s.x - r.x)).im = 0 := by{
    apply colinear_perm13 at brs
    apply colinear_perm23 at brs
    apply colinear_perm12 at sh1
    apply (colinear_alt s b r).1 at brs
    apply (colinear_alt b a s).1 at sh1
    have : (b.x - a.x) / (b.x - s.x) = (a.x-b.x)/(s.x-b.x) := by{
      by_cases bs: b.x=s.x
      rw[bs]
      simp

      have bssub: b.x-s.x ≠ 0 := by{
        contrapose bs
        simp at *
        calc
          b.x = b.x - 0 := by ring
            _= b.x - (b.x-s.x) := by{rw[bs]}
            _= s.x := by{ring}
      }
      have sbsub: s.x-b.x ≠ 0 := by{
        contrapose bs
        simp at *
        calc
          b.x = b.x + 0 := by{ring}
            _= b.x + (s.x-b.x) := by{rw[bs]}
            _= s.x := by{ring}
      }
      field_simp
      ring
    }
    rw[this] at sh1
    clear this
    by_cases sbsub: s.x-b.x = 0
    swap
    have : (a.x - b.x) / (s.x - r.x) = (a.x - b.x) / (s.x - b.x) * ((s.x - b.x) / (s.x - r.x)) := by{field_simp}
    rw[this]
    clear this
    exact complex_real_mul sh1 brs

    have sb: s = b := by{
      ext
      calc
        s.x = s.x - 0 := by{ring}
          _= s.x - (s.x-b.x) := by{rw[sbsub]}
          _= b.x := by ring
    }
    tauto
  }
  calc
    ((a.x - b.x) / (r.x - s.x)).im = -1 * ((a.x - b.x) / (s.x - r.x)).im := by{
      obtain ⟨a1,a2⟩ := a
      obtain ⟨b1,b2⟩ := b
      obtain ⟨s1,s2⟩ := s
      obtain ⟨r1,r2⟩ := r
      simp
      ring
    }
      _= -1*0 := by{rw[this]}
      _= 0 := by ring



  intro h
  unfold Parallel
  let p := Point.mk (c.x-a.x)
  use p
  have nice: colinear a b (padd d (pneg p)) := by{
    apply (colinear_alt a b (padd d (pneg p))).2
    unfold padd pneg p
    simp
    rw[← h]
    obtain ⟨a1,a2⟩ := a
    obtain ⟨b1,b2⟩ := b
    obtain ⟨c1,c2⟩ := c
    obtain⟨d1,d2⟩ := d
    simp
    ring
  }
  symm
  apply line_through_unique
  unfold Lies_on shift_line Line_through
  simp
  constructor
  use a
  unfold p
  constructor
  apply colinear_self
  right
  right
  rfl
  ext
  unfold padd
  ring

  use (padd d (pneg p))
  constructor
  assumption
  unfold padd pneg
  ext
  simp
  ring
}

/- A big Lemma is the following: Two Lines are parallel, if one is the other one shifted:
 The cool thing about this, that we have defined enough for this to be proven (almost) purely geometrically-/
 /-It still is quite a bummer though, unfortunately-/

theorem parallel_def (L R : Line) : Parallel L R ↔ L.range ∩ R.range = ∅ ∨ L.range = R.range := by{
  unfold Parallel
  constructor
  intro h
  obtain ⟨p,ph⟩ := h
  obtain ⟨a,ah⟩ := ex_point_on_line L
  by_cases ap: Lies_on (padd a p) L
  have : R = L := by{
    by_cases h0: p = Point.mk (0)
    rw[h0] at ph
    rw[ph]
    exact shift_line_zero L


    apply lines_eq_ex
    use a
    use (padd a p)
    constructor
    contrapose h0
    simp at *
    unfold padd at h0
    have : a.x = a.x + p.x := by{
      nth_rw 1 [h0]
    }
    ext
    simp
    calc
      p.x = -a.x + (a.x + p.x) := by ring
        _= -a.x + a.x := by rw[← this]
        _= 0 := by ring
    constructor
    unfold Lies_on
    rw[ph]
    unfold shift_line
    simp
    use padd a (pneg p)
    have aap: a ≠ padd a p := by{
      contrapose h0
      unfold padd at h0
      simp at *
      ext
      simp
      have : a.x = ({ x := a.x + p.x } : Point).x := by{rw[← h0]}
      simp at this
      assumption
    }
    have Lh: L = Line_through aap := by{
      apply line_through_unique
      constructor
      assumption
      assumption
    }
    constructor
    rw[Lh]
    unfold Line_through
    simp
    unfold padd pneg colinear det conj
    simp
    ring

    ext
    unfold pneg padd
    simp

    constructor
    assumption
    constructor
    rw[ph]
    exact mem_line_shift a p L ah
    assumption
  }
  rw[this]
  right
  rfl

  left
  by_contra h0
  have : (L.range ∩ R.range).Nonempty := by{exact nonempty_iff_ne_empty.mpr h0}
  apply Set.nonempty_def.1 at this
  obtain ⟨b,bh⟩ := this
  have ab: a ≠ b := by{
    by_contra u
    rw[← u] at bh
    clear u b
    have aR: a ∈ R.range := by exact bh.2
    clear bh
    rw[ph] at aR
    unfold shift_line at aR
    simp at aR
    obtain ⟨c,ch1,ch2⟩ := aR
    rw[ch2] at ah
    rw[ch2] at ap
    contrapose ap
    simp
    clear ch2 ap a h0 ph R
    have cL: Lies_on c L := by{
      unfold Lies_on
      assumption
    }
    clear ch1
    by_cases p0: p= Point.mk 0
    rw[p0]
    simp [padd_comm, padd_zero, cL]

    have ccp: c ≠ padd c p := by{
      contrapose p0
      simp at *
      ext
      simp
      unfold padd at p0
      have : c.x = ({ x := c.x + p.x } : Point).x := by{rw[← p0]}
      simp at this
      assumption
    }
    have hL: L = Line_through ccp := by{
      apply line_through_unique
      constructor
      assumption
      assumption
    }
    rw[hL]
    clear ah L hL cL
    unfold Line_through Lies_on padd colinear det conj
    simp
    ring
  }
  obtain ⟨bh1,bh2⟩ := bh
  rw[ph] at bh2
  unfold shift_line at bh2
  simp at bh2
  obtain ⟨c,⟨ch1,ch2⟩⟩ := bh2
  rw[ch2] at bh1
  clear ab ch2 b ph
  have hp: p ≠ Point.mk (0) := by{
    contrapose ap
    simp at *
    rw[ap]
    rw[padd_zero a]
    assumption
  }
  have ccp: c ≠ padd c p := by{
    contrapose hp
    simp at *
    unfold padd at hp
    have : c.x = ({ x := c.x + p.x } : Point).x := by{rw[← hp]}
    simp at this
    ext
    assumption
  }
  have hL : L = Line_through ccp := by{
    apply line_through_unique
    constructor
    assumption
    assumption
  }
  contrapose ap
  simp
  clear h0 ap
  rw[hL] at ah
  rw[hL]
  unfold Line_through at *
  unfold Lies_on at *
  simp at *
  clear hL ccp hp ch1 bh1 L R
  unfold colinear at *
  rw[← ah]
  unfold padd det conj
  simp
  ring

  intro h
  obtain h|h := h
  swap
  have : L = R := by{
    ext x
    rw[h]
  }
  rw[this]
  use Point.mk 0
  rw[shift_line_zero R]

  obtain ⟨a,b,ab,aL,bL⟩ := ex_points_on_line L
  obtain ⟨c,ch⟩ := ex_point_on_line R
  let p := Point.mk (c.x-a.x)
  use p
  have : L = Line_through ab := by{
    apply line_through_unique
    constructor
    assumption
    assumption
  }
  rw[this]
  let d := padd b p
  have cd: c ≠ d := by{
    unfold d
    have p0: p ≠ Point.mk (0) := by{
      unfold p
      simp
      contrapose h
      simp at h
      have : a.x = c.x := by{
        calc
          a.x = a.x + (0:ℂ) := by ring
            _=a.x + (c.x-a.x) := by rw[h]
            _= c.x := by ring
      }
      have ac: a = c := by{ext;exact this}
      rw[ac] at aL
      unfold Lies_on at *
      by_contra z
      have : c ∈ L.range ∩ R.range := by{constructor;assumption;assumption}
      rw[z] at this
      contradiction
    }
    have : c = padd a p := by{
      unfold p padd
      ext
      ring
    }
    rw[this]
    unfold padd
    simp
    by_contra h0
    have : a = b := by{
      ext
      calc
        a.x = a.x + c.x - c.x := by ring
          _= a.x + (b.x + (c.x - a.x)) - c.x := by nth_rw 1 [h0]
          _= b.x := by ring
    }
    contradiction
  }
  --following is the last main result, having proved it, rest gets easy
  have hR: R = Line_through cd := by{
    apply line_through_unique
    constructor
    assumption
    obtain ⟨e,f,ef,re,rf⟩ := ex_points_on_line R
    have : c ≠ e ∨ c ≠ f := by{
      by_contra h0
      simp at h0
      have : e = f := by{
        calc
          e = c := by rw[h0.1]
            _= f := by rw[h0.2]
      }
      contradiction
    }
    obtain ce|cf := this
    /-ab hier-/
    have hR : R = Line_through ce := by{
      apply line_through_unique
      constructor
      assumption
      exact re
    }
    rw[hR]
    unfold Lies_on
    unfold Line_through
    simp
    clear f ef rf
    by_contra h0
    let m := ((conj a.x) - (conj b.x))*(c.x-e.x)-(a.x-b.x)*(conj c.x - conj e.x)
    --n IST FALSCH DEFINIERT OJE
    let n := (((conj a.x)*b.x-a.x*(conj b.x))*(c.x-e.x)-(a.x-b.x)*((conj c.x)*e.x-c.x*(conj e.x)))
    have t1: m ≠ 0 := by{
      by_contra h1
      unfold m at h1
      have h2: (conj a.x - conj b.x) * (c.x - e.x) = (a.x - b.x) * (conj c.x - conj e.x) := by{
        calc
          (conj a.x - conj b.x) * (c.x - e.x) = (conj a.x - conj b.x) * (c.x - e.x) - 0 := by ring
            _= (conj a.x - conj b.x) * (c.x - e.x) - ((conj a.x - conj b.x) * (c.x - e.x) - (a.x - b.x) * (conj c.x - conj e.x)) := by rw[h1]
            _= (a.x - b.x) * (conj c.x - conj e.x) := by ring
      }
      clear h1
      have ab_sub: a.x-b.x ≠ 0 := by{
        by_contra ab
        have : a=b := by{
        simp at *
        ext
        calc
          a.x = a.x -0 := by ring
            _= a.x -(a.x-b.x) := by rw[ab]
            _= b.x := by ring
        }
        contradiction
      }
      have ce_conj_sub : conj c.x - conj e.x ≠ 0 := by{
        by_contra h3
        simp at *
        have : conj c.x = conj e.x := by{
          calc
            conj c.x = conj c.x - 0 := by ring
              _= conj c.x - (conj c.x - conj e.x) := by{rw[h3]}
              _= conj e.x := by ring
        }
        have : c=e := by{
          ext
          rw[← conj_twice c.x, ← conj_twice e.x, this]
        }
        contradiction
      }
      have ce_sub : c.x - e.x ≠ 0 := by{
        by_contra ab
        have : c=e := by{
        simp at *
        ext
        calc
          c.x = c.x -0 := by ring
            _= c.x -(c.x-e.x) := by rw[ab]
            _= e.x := by ring
        }
        contradiction
      }
      have abce: conj ((a.x-b.x)/(c.x-e.x)) = (a.x-b.x)/(c.x-e.x) := by{
        simp
        field_simp
        assumption
      }
      --focus on h0
      have imzero: ( (a.x - b.x) / (c.x - e.x)).im = 0 := by{
        exact Complex.conj_eq_iff_im.mp abce
      }
      /-Aus dem könnte man mit colinear_alt folgern:
      ab parallel zu ce
      und dann wird h0 halt zum problem-/
      have LR_parallel: Parallel L R := by{
        rw[this,hR]
        exact (parallel_quot ab ce).mpr imzero
      }
      obtain ⟨q,qh⟩ := LR_parallel
      clear abce ce_sub ce_conj_sub ab_sub h2 m n
      contrapose h0
      simp
      rw[qh] at ch re
      unfold Lies_on shift_line at re ch
      simp at *
      obtain ⟨u,uh1,uh2⟩ := ch
      obtain ⟨v,vh1,vh2⟩ := re
      unfold d p
      rw[uh2,vh2]
      unfold padd
      simp
      unfold colinear
      have : det { x := u.x + q.x } { x := v.x + q.x } { x := b.x + (u.x + q.x - a.x) } = det u v (padd u (Point.mk (b.x-a.x))) := by{
        unfold det padd conj
        simp
        ring
      }
      rw[this]
      clear this
      have goal: colinear u v (padd u (Point.mk (b.x - a.x))) := by{
        rw[this] at vh1 uh1
        unfold Line_through at vh1 uh1
        simp at vh1 uh1
        have abshift: colinear a b (padd u (Point.mk (b.x-a.x))) := by{
          unfold colinear at uh1
          unfold colinear
          calc
            det a b (padd u { x := b.x - a.x }) = det a b u := by{
              unfold det padd
              simp
              ring
            }
              _= 0 := by{assumption}
        }
        have shiftmem: Lies_on (padd u (Point.mk (b.x-a.x))) (Line_through ab) := by{
          unfold Lies_on Line_through
          simp
          assumption
        }
        have uv : u ≠ v := by{
          by_contra ce
          have : c = e := by{
            rw[uh2,vh2]
            ext
            unfold padd
            rw[ce]
          }
          contradiction
        }
        have uvL: Line_through ab = Line_through uv := by{
          apply line_through_unique
          constructor
          repeat
            unfold Lies_on Line_through
            assumption
        }
        rw[uvL] at shiftmem
        unfold Lies_on Line_through at shiftmem
        assumption
      }
      unfold colinear at goal
      assumption
    }
    --I also have to do the reverse...
    unfold conj at t1
    have t2: conj m ≠ 0 := by{
      by_contra h0
      rw[← conj_twice m] at t1
      rw[h0] at t1
      unfold conj at t1
      simp at t1
    }
    let q := Point.mk (n / m)
    have : conj m = -m := by{
      unfold m
      simp
    }
    rw[this] at t2
    have colinear1 : colinear a b q := by{
      unfold colinear
      rw[det_detproper a b q]
      have goal: (detproper a.x (conj a.x) 1 b.x (conj b.x) 1 q.x (conj q.x) 1) = 0 := by{
        unfold q
        simp
        rw[this]
        have : detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n / m) (conj n / - m) 1 = 1/m * detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n) (-conj n) (m) := by{
            calc
              detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n / m) (conj n / - m) 1 = detproper a.x (conj a.x) 1 b.x (conj b.x) 1 ((1/m)*(n)) ((1/m)*(-conj n)) (1/m * m) := by{
                field_simp
                have : conj n / -m = - conj n / m := by{
                  field_simp
                }
                rw[this]
              }
                _= 1/m * detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n) (-conj n) (m) := by{rw [detproper_row3]}
        }
        rw[this]
        clear this
        field_simp
        unfold n m
        unfold detproper
        simp
        ring
      }
      rw[goal]
      rfl
    }

    have colinear2: colinear c e q := by{
      unfold colinear
      rw[det_detproper c e q]
      have goal: detproper c.x (conj c.x) 1 e.x (conj e.x) 1 q.x (conj q.x) 1 = 0 := by{
        unfold q
        simp
        rw[this]
        have : detproper c.x (conj c.x) 1 e.x (conj e.x) 1 (n / m) (conj n / - m) 1 = 1/m * detproper c.x (conj c.x) 1 e.x (conj e.x) 1 (n) (-conj n) (m) := by{
            calc
              detproper c.x (conj c.x) 1 e.x (conj e.x) 1 (n / m) (conj n / - m) 1 = detproper c.x (conj c.x) 1 e.x (conj e.x) 1 ((1/m)*(n)) ((1/m)*(-conj n)) (1/m * m) := by{
                field_simp
                have : conj n / -m = - conj n / m := by{
                  field_simp
                }
                rw[this]
              }
                _= 1/m * detproper c.x (conj c.x) 1 e.x (conj e.x) 1 (n) (-conj n) (m) := by{rw [detproper_row3]}
        }
        rw[this]
        clear this
        field_simp
        unfold n m
        unfold detproper
        simp
        ring
      }
      rw[goal]
      rfl
    }
    have qbad: q ∈ L.range ∩ R.range := by{
      constructor
      swap
      rw[hR]
      unfold Line_through
      simp
      assumption

      have : L = Line_through ab := by{assumption}
      rw[this]
      unfold Line_through
      simp
      assumption
    }
    rw[h] at qbad
    contradiction

    --letzte 200 zeilen nohcmal bruhhh

    have hR : R = Line_through cf := by{
      apply line_through_unique
      constructor
      assumption
      exact rf
    }
    rw[hR]
    unfold Lies_on
    unfold Line_through
    simp
    clear e ef re
    by_contra h0
    let m := ((conj a.x) - (conj b.x))*(c.x-f.x)-(a.x-b.x)*(conj c.x - conj f.x)
    let n := (((conj a.x)*b.x-a.x*(conj b.x))*(c.x-f.x)-(a.x-b.x)*((conj c.x)*f.x-c.x*(conj f.x)))
    have t1: m ≠ 0 := by{
      by_contra h1
      unfold m at h1
      have h2: (conj a.x - conj b.x) * (c.x - f.x) = (a.x - b.x) * (conj c.x - conj f.x) := by{
        calc
          (conj a.x - conj b.x) * (c.x - f.x) = (conj a.x - conj b.x) * (c.x - f.x) - 0 := by ring
            _= (conj a.x - conj b.x) * (c.x - f.x) - ((conj a.x - conj b.x) * (c.x - f.x) - (a.x - b.x) * (conj c.x - conj f.x)) := by rw[h1]
            _= (a.x - b.x) * (conj c.x - conj f.x) := by ring
      }
      clear h1
      have ab_sub: a.x-b.x ≠ 0 := by{
        by_contra ab
        have : a=b := by{
        simp at *
        ext
        calc
          a.x = a.x -0 := by ring
            _= a.x -(a.x-b.x) := by rw[ab]
            _= b.x := by ring
        }
        contradiction
      }
      have cf_conj_sub : conj c.x - conj f.x ≠ 0 := by{
        by_contra h3
        simp at *
        have : conj c.x = conj f.x := by{
          calc
            conj c.x = conj c.x - 0 := by ring
              _= conj c.x - (conj c.x - conj f.x) := by{rw[h3]}
              _= conj f.x := by ring
        }
        have : c=f := by{
          ext
          rw[← conj_twice c.x, ← conj_twice f.x, this]
        }
        contradiction
      }
      have cf_sub : c.x - f.x ≠ 0 := by{
        by_contra ab
        have : c=f := by{
        simp at *
        ext
        calc
          c.x = c.x -0 := by ring
            _= c.x -(c.x-f.x) := by rw[ab]
            _= f.x := by ring
        }
        contradiction
      }
      have abcf: conj ((a.x-b.x)/(c.x-f.x)) = (a.x-b.x)/(c.x-f.x) := by{
        simp
        field_simp
        assumption
      }
      --focus on h0
      have imzero: ( (a.x - b.x) / (c.x - f.x)).im = 0 := by{
        exact Complex.conj_eq_iff_im.mp abcf
      }
      have LR_parallel: Parallel L R := by{
        rw[this,hR]
        exact (parallel_quot ab cf).mpr imzero
      }
      obtain ⟨q,qh⟩ := LR_parallel
      clear abcf cf_sub cf_conj_sub ab_sub h2 m n
      contrapose h0
      simp
      rw[qh] at ch rf
      unfold Lies_on shift_line at rf ch
      simp at *
      obtain ⟨u,uh1,uh2⟩ := ch
      obtain ⟨v,vh1,vh2⟩ := rf
      unfold d p
      rw[uh2,vh2]
      unfold padd
      simp
      unfold colinear
      have : det { x := u.x + q.x } { x := v.x + q.x } { x := b.x + (u.x + q.x - a.x) } = det u v (padd u (Point.mk (b.x-a.x))) := by{
        unfold det padd conj
        simp
        ring
      }
      rw[this]
      clear this
      have goal: colinear u v (padd u (Point.mk (b.x - a.x))) := by{
        rw[this] at vh1 uh1
        unfold Line_through at vh1 uh1
        simp at vh1 uh1
        have abshift: colinear a b (padd u (Point.mk (b.x-a.x))) := by{
          unfold colinear at uh1
          unfold colinear
          calc
            det a b (padd u { x := b.x - a.x }) = det a b u := by{
              unfold det padd
              simp
              ring
            }
              _= 0 := by{assumption}
        }
        have shiftmem: Lies_on (padd u (Point.mk (b.x-a.x))) (Line_through ab) := by{
          unfold Lies_on Line_through
          simp
          assumption
        }
        have uv : u ≠ v := by{
          by_contra cf
          have : c = f := by{
            rw[uh2,vh2]
            ext
            unfold padd
            rw[cf]
          }
          contradiction
        }
        have uvL: Line_through ab = Line_through uv := by{
          apply line_through_unique
          constructor
          repeat
            unfold Lies_on Line_through
            assumption
        }
        rw[uvL] at shiftmem
        unfold Lies_on Line_through at shiftmem
        assumption
      }
      unfold colinear at goal
      assumption
    }

    unfold conj at t1
    have t2: conj m ≠ 0 := by{
      by_contra h0
      rw[← conj_twice m] at t1
      rw[h0] at t1
      unfold conj at t1
      simp at t1
    }
    let q := Point.mk (n / m)
    have : conj m = -m := by{
      unfold m
      simp
    }
    rw[this] at t2
    have colinear1 : colinear a b q := by{
      unfold colinear
      rw[det_detproper a b q]
      have goal: (detproper a.x (conj a.x) 1 b.x (conj b.x) 1 q.x (conj q.x) 1) = 0 := by{
        unfold q
        simp
        rw[this]
        have : detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n / m) (conj n / - m) 1 = 1/m * detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n) (-conj n) (m) := by{
            calc
              detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n / m) (conj n / - m) 1 = detproper a.x (conj a.x) 1 b.x (conj b.x) 1 ((1/m)*(n)) ((1/m)*(-conj n)) (1/m * m) := by{
                field_simp
                have : conj n / -m = - conj n / m := by{
                  field_simp
                }
                rw[this]
              }
                _= 1/m * detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n) (-conj n) (m) := by{rw [detproper_row3]}
        }
        rw[this]
        clear this
        field_simp
        unfold n m
        unfold detproper
        simp
        ring
      }
      rw[goal]
      rfl
    }

    have colinear2: colinear c f q := by{
      unfold colinear
      rw[det_detproper c f q]
      have goal: detproper c.x (conj c.x) 1 f.x (conj f.x) 1 q.x (conj q.x) 1 = 0 := by{
        unfold q
        simp
        rw[this]
        have : detproper c.x (conj c.x) 1 f.x (conj f.x) 1 (n / m) (conj n / - m) 1 = 1/m * detproper c.x (conj c.x) 1 f.x (conj f.x) 1 (n) (-conj n) (m) := by{
            calc
              detproper c.x (conj c.x) 1 f.x (conj f.x) 1 (n / m) (conj n / - m) 1 = detproper c.x (conj c.x) 1 f.x (conj f.x) 1 ((1/m)*(n)) ((1/m)*(-conj n)) (1/m * m) := by{
                field_simp
                have : conj n / -m = - conj n / m := by{
                  field_simp
                }
                rw[this]
              }
                _= 1/m * detproper c.x (conj c.x) 1 f.x (conj f.x) 1 (n) (-conj n) (m) := by{rw [detproper_row3]}
        }
        rw[this]
        clear this
        field_simp
        unfold n m
        unfold detproper
        simp
        ring
      }
      rw[goal]
      rfl
    }
    have qbad: q ∈ L.range ∩ R.range := by{
      constructor
      swap
      rw[hR]
      unfold Line_through
      simp
      assumption

      have : L = Line_through ab := by{assumption}
      rw[this]
      unfold Line_through
      simp
      assumption
    }
    rw[h] at qbad
    contradiction
  }
  rw[hR]
  unfold Line_through shift_line
  simp
  ext r
  simp
  unfold d
  constructor
  intro th
  use padd r (pneg p)
  constructor
  swap
  unfold padd pneg
  ext
  ring

  have : c = padd a p := by{
    unfold p padd
    ext
    ring
  }
  rw[this] at th
  have : r = padd (padd r (pneg p)) p := by{
    unfold padd pneg
    ring_nf
  }
  rw[this] at th
  exact colinear_shift_bw a b (padd r (pneg p)) p th

  intro rh
  obtain ⟨u,uh1,uh2⟩ := rh
  have : c = padd a p := by{
    unfold p padd
    ext
    ring
  }
  rw[this]
  rw[uh2]
  exact colinear_shift p uh1
}

lemma parallel_refl (L : Line) : Parallel L L := by{
  apply (parallel_def L L).2
  right
  rfl
}


/-With this we can now talk about Intersections of lines:-/

theorem lines_intersect {L R : Line}(h : ¬Parallel L R) : ∃! s : Point, Lies_on s L ∧ Lies_on s R := by{
  unfold Lies_on

  have : Set.encard (L.range ∩ R.range) = 1 := by{
    by_cases p: Set.encard (L.range ∩ R.range) ≤ 1
    have : Set.encard (L.range ∩ R.range) = 0 ∨ Set.encard (L.range ∩ R.range) = 1 := by{
      apply Set.encard_le_one_iff_eq.1 at p
      obtain p|p := p
      left
      rw[p]
      exact Set.encard_empty
      right
      exact Set.encard_eq_one.2 p
    }
    obtain this|this := this
    have : (L.range ∩ R.range = ∅) := by exact encard_eq_zero.mp this
    have : Parallel L R := by{
      apply (parallel_def L R).2
      left
      assumption
    }
    contradiction
    assumption

    exfalso
    contrapose h
    simp at *
    have : ∃ (a b : Point), a ≠ b ∧ a ∈ (L.range ∩ R.range) ∧ b ∈ (L.range ∩ R.range) := by{
      apply Set.one_lt_encard_iff.1 at p
      tauto
    }
    obtain ⟨a,b,ab,ah,bh⟩ := this

    apply ex_unique_line_mem at ab
    obtain ⟨U,⟨hU1,hU2⟩⟩ := ab
    simp at hU2
    have LU: L = U := by{
      apply hU2
      unfold Lies_on
      exact mem_of_mem_inter_left ah
      unfold Lies_on
      exact mem_of_mem_inter_left bh
    }
    have RU: R = U := by{
      apply hU2
      unfold Lies_on
      exact mem_of_mem_inter_right ah
      unfold Lies_on
      exact mem_of_mem_inter_right bh
    }
    rw[LU,RU]
    exact parallel_refl U
  }
  have : ∃! s : Point, s ∈ (L.range ∩ R.range) := by{
    apply Set.encard_eq_one.1 at this
    obtain ⟨s,hs⟩ := this
    rw[hs]
    exact ExistsUnique.intro s rfl fun y ↦ congrArg fun y ↦ y
  }
  assumption
}

def Intersection {L R : Line}(h : ¬ Parallel L R) : Point :=
  (lines_intersect h).choose

/-This indeed is in the intersection:-/

lemma intersection_mem {L R : Line}(LR : ¬ Parallel L R) : Lies_on (Intersection LR) L ∧ Lies_on (Intersection LR) R := by{
  exact (Classical.choose_spec (lines_intersect LR)).1
}

/-lines_intersect lemma now become nicer:-/

lemma intersection_unique {L R : Line}{a : Point}(LR : ¬ Parallel L R)(ah: Lies_on a L ∧ Lies_on a R) : a = Intersection LR := by{
  have : ∃! s, Lies_on s L ∧ Lies_on s R := by{exact lines_intersect LR}
  obtain ⟨s,sh1,sh2⟩ := this
  simp at sh2
  have as: a=s := by{specialize sh2 a ah.1 ah.2; assumption}
  have is: Intersection LR = s := by{specialize sh2 (Intersection LR) (intersection_mem LR).1 (intersection_mem LR).2; assumption}
  rw[as,is]
}

/-In some rare cases, one might want to use an explicit formula for the intersection of lines.
There is one but it is not pretty:-/
/-Note I actually *copied* the proof from  the awful parallel_def proof for (most of) this. There is nothing new to see here.-/
lemma intersection_explicit{a b c d : Point}{ab : a ≠ b}{cd : c ≠ d}(h : ¬Parallel (Line_through ab) (Line_through cd)):
  Intersection h = Point.mk ((((conj a.x)*(b.x)-(a.x)*(conj b.x))*(c.x-d.x)-((a.x-b.x)*((conj c.x)*(d.x)-(c.x)*(conj d.x))))/(((conj a.x)-(conj b.x))*(c.x-d.x)-(a.x-b.x)*((conj c.x)-(conj d.x)))) := by{

  let m := (((conj a.x)-(conj b.x))*(c.x-d.x)-(a.x-b.x)*((conj c.x)-(conj d.x)))
  let n := ((conj a.x)*(b.x)-(a.x)*(conj b.x))*(c.x-d.x)-((a.x-b.x)*((conj c.x)*(d.x)-(c.x)*(conj d.x)))
  have s1: m ≠ 0 := by{
    contrapose h
    simp at *
    clear n
    apply (parallel_quot ab cd).2
    have absub: a.x-b.x ≠ 0 := by{exact sub_neq_zero ab}
    have cdsub: c.x-d.x ≠ 0 := by{exact sub_neq_zero cd}
    have conjself: conj ((a.x - b.x) / (c.x - d.x)) = (a.x-b.x)/(c.x-d.x) := by{
      simp
      have : (conj c.x - conj d.x) ≠ 0 := by{
        contrapose cdsub
        simp at *
        calc
          c.x - d.x = conj (conj (c.x-d.x)) := by{simp}
            _= conj (conj (c.x) - conj (d.x)) := by{simp}
            _= conj (0) := by{rw[cdsub]}
            _= 0 := by{unfold conj; simp}
      }
      field_simp
      unfold m at h
      clear m
      calc
        (conj a.x - conj b.x) * (c.x - d.x) = (conj a.x - conj b.x) * (c.x - d.x) - 0 := by{ring}
          _= (conj a.x - conj b.x) * (c.x - d.x) - ( (conj a.x - conj b.x) * (c.x - d.x) - (a.x - b.x) * (conj c.x - conj d.x)) := by{rw[h]}
          _= (a.x - b.x) * (conj c.x - conj d.x) := by{ring}
    }
    exact Complex.conj_eq_iff_im.mp conjself
  }
  let q := Point.mk (n / m)
  have : conj m = -m := by{
    unfold m
    simp
  }
  have colinear1 : colinear a b q := by{
      unfold colinear
      rw[det_detproper a b q]
      have goal: (detproper a.x (conj a.x) 1 b.x (conj b.x) 1 q.x (conj q.x) 1) = 0 := by{
        unfold q
        simp
        rw[this]
        have : detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n / m) (conj n / - m) 1 = 1/m * detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n) (-conj n) (m) := by{
            calc
              detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n / m) (conj n / - m) 1 = detproper a.x (conj a.x) 1 b.x (conj b.x) 1 ((1/m)*(n)) ((1/m)*(-conj n)) (1/m * m) := by{
                field_simp
                have : conj n / -m = - conj n / m := by{
                  have : -m ≠ 0 := by{
                    contrapose s1
                    simp at *
                    assumption
                  }
                  field_simp
                }
                rw[this]
              }
                _= 1/m * detproper a.x (conj a.x) 1 b.x (conj b.x) 1 (n) (-conj n) (m) := by{rw [detproper_row3]}
        }
        rw[this]
        clear this
        field_simp
        unfold n m
        unfold detproper
        simp
        ring
      }
      rw[goal]
      rfl
    }

  have colinear2: colinear c d q := by{
    unfold colinear
    rw[det_detproper c d q]
    have goal: detproper c.x (conj c.x) 1 d.x (conj d.x) 1 q.x (conj q.x) 1 = 0 := by{
      unfold q
      simp
      rw[this]
      have : detproper c.x (conj c.x) 1 d.x (conj d.x) 1 (n / m) (conj n / - m) 1 = 1/m * detproper c.x (conj c.x) 1 d.x (conj d.x) 1 (n) (-conj n) (m) := by{
          calc
            detproper c.x (conj c.x) 1 d.x (conj d.x) 1 (n / m) (conj n / - m) 1 = detproper c.x (conj c.x) 1 d.x (conj d.x) 1 ((1/m)*(n)) ((1/m)*(-conj n)) (1/m * m) := by{
              field_simp
              have : conj n / -m = - conj n / m := by{
                have : -m ≠ 0 := by{
                  contrapose s1
                  simp at *
                  assumption
                }
                field_simp
              }
              rw[this]
            }
              _= 1/m * detproper c.x (conj c.x) 1 d.x (conj d.x) 1 (n) (-conj n) (m) := by{rw [detproper_row3]}
      }
      rw[this]
      clear this
      field_simp
      unfold n m
      unfold detproper
      simp
      ring
    }
    rw[goal]
    rfl
  }
  symm
  apply intersection_unique
  unfold Lies_on Line_through
  simp
  have mdef: m = (((conj a.x)-(conj b.x))*(c.x-d.x)-(a.x-b.x)*((conj c.x)-(conj d.x))) := by{
    unfold m
    rfl
  }
  rw[← mdef]
  have ndef: n = ((conj a.x)*(b.x)-(a.x)*(conj b.x))*(c.x-d.x)-((a.x-b.x)*((conj c.x)*(d.x)-(c.x)*(conj d.x))) := by{
    unfold n
    rfl
  }
  rw[← ndef]
  unfold q at colinear2
  unfold q at colinear1
  constructor
  assumption
  assumption
  }


/- With this we now show being parallel is an equivalence relation:-/

lemma parallel_symm (L R : Line)(h : Parallel L R) : Parallel R L := by{
  apply (parallel_def L R).1 at h
  apply (parallel_def R L).2
  obtain h|h := h
  · left
    rw[Set.inter_comm]
    assumption
  · right
    symm
    assumption
}

lemma parallel_trans {L R S : Line}(LR : Parallel L R)(RS : Parallel R S) : Parallel L S := by{
  unfold Parallel at *
  obtain ⟨p,hp⟩ := LR
  obtain ⟨q,hq⟩ := RS
  use padd p q
  rw[hp] at hq
  rw[← shift_line_trans L p q]
  assumption
}

/-Note: I should probably redo this section a bit, define parallel_through first and then use it
for weak_parallel_postulate. Else everyhting is quite redundant-/

lemma weak_parallel_postulate (L : Line)(a : Point) : ∃ Q : Line, Lies_on a Q ∧ Parallel L Q := by{
  obtain ⟨b,bh⟩ := ex_point_on_line L
  use (shift_line L (Point.mk (a.x-b.x)))
  constructor
  unfold Lies_on shift_line
  simp

  use b
  constructor
  assumption
  ext
  unfold padd
  ring
  exact shift_line_parallel L (Point.mk (a.x-b.x))
}

theorem parallel_postulate (L : Line)(a : Point) : ∃! Q : Line, Lies_on a Q ∧ Parallel L Q := by{
  obtain ⟨U,Uh⟩ := weak_parallel_postulate L a
  use U
  constructor
  assumption

  intro R Rh
  by_cases UR: Parallel U R
  unfold Parallel at UR
  obtain h|h := UR
  unfold Lies_on at *
  have : a ∈ U.range ∧ a ∈ R.range := by{
    constructor
    exact Uh.1
    exact Rh.1
  }
  have : a ∈ U.range ∩ R.range := by exact this
  have UR: Parallel U R := by{
    obtain ⟨_,hi⟩ := Uh
    apply parallel_symm at hi
    exact parallel_trans hi Rh.2
  }
  apply (parallel_def U R).1 at UR
  obtain h'|h' := UR
  rw[h'] at this
  contradiction
  ext
  rw[h']

  exfalso
  obtain ⟨_,hU⟩ := Uh
  obtain ⟨_,hR⟩ := Rh
  have : Parallel U R := by{
    apply parallel_symm at hU
    exact parallel_trans hU hR
  }
  contradiction
}

def parallel_through : Line → Point → Line :=
  fun L a ↦ (weak_parallel_postulate L a).choose

/-This really has the properties we want: -/

lemma point_lies_on_parallel_through (L: Line)(a : Point) : Lies_on a (parallel_through L a) := by{
  unfold parallel_through
  exact (Exists.choose_spec (weak_parallel_postulate L a)).1
}

lemma parallel_through_is_parallel (L : Line)(a : Point) : Parallel L (parallel_through L a) := by{
  unfold parallel_through
  exact (Exists.choose_spec (weak_parallel_postulate L a)).2
}

lemma parallel_through_is_parallel_through (L : Line)(a : Point) : Lies_on a (parallel_through L a) ∧ Parallel L (parallel_through L a) := by{
  unfold parallel_through
  exact Exists.choose_spec (weak_parallel_postulate L a)
}

/-Now we can formulate the parallel postualte in a nice way:-/

theorem parallel_through_unique (L R : Line)(a : Point)(h : Lies_on a R ∧ Parallel L R) : R = parallel_through L a := by{
  obtain ⟨S,hS1,hS2⟩ := parallel_postulate L a
  simp at hS2
  have RS: R = S := by{
    exact hS2 R h.1 h.2
  }
  have PTS: parallel_through L a = S := by{
    exact hS2 (parallel_through L a) (point_lies_on_parallel_through L a) (parallel_through_is_parallel L a)
  }
  rw[RS,PTS]
}
