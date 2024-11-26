import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Nat.Choose.Dvd
noncomputable section
open Function Ideal Polynomial Classical
open scoped Matrix
-- This is removed intentionally and should not be used manually in the exercises
attribute [-ext] LinearMap.prod_ext


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 8.2 and 9.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 26.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice.
Feel free to skip these exercises-/

example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by {
  rw [span_gcd]
  exact Eq.symm (span_insert n {m})
  }

example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by {
  ext x
  constructor
  swap
  intro xh
  have uno: x∈ span {n} := by{
    have d: n ∣ lcm n m := by exact dvd_lcm_left n m
    obtain ⟨k,kh⟩ := d
    rw[kh] at xh
    unfold span at *
    unfold Submodule.span at *
    unfold sInf at *
    unfold Submodule.instInfSet at *
    simp at *
    intro u
    intro uh
    specialize xh u
    apply xh
    exact mul_mem_right k u uh
  }
  have duo: x∈ span {m} := by{
    have d: m ∣ lcm n m := by exact dvd_lcm_right n m
    obtain ⟨k,kh⟩ := d
    rw[kh] at xh
    unfold span at *
    unfold Submodule.span at *
    unfold sInf at *
    unfold Submodule.instInfSet at *
    simp at *
    intro u
    intro uh
    specialize xh u
    apply xh
    exact mul_mem_right k u uh
  }
  apply mem_inf.2
  exact ⟨uno,duo⟩

  intro xh
  apply mem_inf.1 at xh
  obtain ⟨xn,xm⟩ := xh
  have nx: n ∣ x := by{
    unfold span at xn
    exact mem_span_singleton.mp xn
  }
  have mx: m ∣ x := by{
    unfold span at xm
    exact mem_span_singleton.mp xm
  }
  have dx: (lcm n m) ∣ x := by{
    exact lcm_dvd nx mx
  }
  obtain ⟨k,kh⟩ := dx
  rw[kh]
  rw[mul_comm]
  unfold span
  unfold Submodule.span
  unfold sInf
  unfold Submodule.instInfSet
  simp at *
  intro u
  intro uh
  exact mul_mem_left u k uh
  }

/- Show that transposing a matrix gives rise to a linear equivalence. -/
example {R M m n : Type*} [Ring R] [AddCommGroup M] [Module R M] :
  Matrix m n M ≃ₗ[R] Matrix n m M where
    toFun := fun M ↦ Mᵀ
    map_add' := by{
      intro x y
      ext a b
      simp
    }
    map_smul' := by exact fun m_1 x ↦ rfl
    invFun := by exact fun a a_1 a_2 ↦ a a_2 a_1
    left_inv := by exact congrFun rfl
    right_inv := by exact congrFun rfl

/- A ring has characteristic `p` if `1 + ⋯ + 1 = 0`, where we add `1` `p` times to itself.
This is written `CharP` in Lean.
In a module over a ring with characteristic 2, for every element `m` we have `m + m = 0`. -/
example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [CharP R 2] (m : M) :
    m + m = 0 := by {
    have : (1 :R) • m = m := by exact MulAction.one_smul m
    calc
      m + m = (1:R) • m + (1:R) • m := by rw[this]
        _= ((1:R) + (1:R)) • m := by exact Eq.symm (Module.add_smul 1 1 m)
        _= (0:R) • m := by {
          have : (1:R) + (1:R) = (0:R) := by{
            exact CharTwo.add_self_eq_zero 1
          }
          rw[this]
        }
        _= (0 : M) := by exact zero_smul R m
  }

section Frobenius
variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]
/- Let's define the Frobenius morphism `x ↦ x ^ p`.
You can use lemmas from the library.
We state that `p` is prime using `Fact p.Prime`.
This allows type-class inference to see that this is true.
You can access the fact that `p` is prime using `hp.out`. -/

def frobeniusMorphism (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p] :
  R →+* R where
    toFun := fun x ↦ x ^ p
    map_one' := by simp
    map_mul' := by{
      intro x y
      simp
      rw[mul_pow]
    }
    map_zero' := by{
      simp
      by_cases h0 : p = 0
      have : Nat.Prime p := by {exact hp.out}
      have : 2 ≤ p := by exact Nat.Prime.two_le this
      rw[h0] at this
      contradiction

      exact zero_pow h0
    }
    map_add' := by{
      intro x y
      simp
      rw [add_pow_expChar]
    }

@[simp] lemma frobeniusMorphism_def (x : R) : frobeniusMorphism p R x = x ^ p := rfl

/- Prove the following equality for iterating the frobenius morphism. -/
lemma iterate_frobeniusMorphism (n : ℕ) (x : R) : (frobeniusMorphism p R)^[n] x = x ^ p ^ n := by {
  unfold frobeniusMorphism
  simp
  }

/- Show that the Frobenius morphism is injective on a domain. -/
lemma frobeniusMorphism_injective [IsDomain R] :
    Function.Injective (frobeniusMorphism p R) := by {
  intro x y xy
  unfold frobeniusMorphism at xy
  simp at xy
  by_cases h2: p = 2
  rw[h2] at xy
  have : (x + y)*(x-y)=0 := by{
    calc
      (x + y)*(x-y) = x^2 - y^2 := by ring
        _=y^2-y^2 := by rw[xy]
        _= 0 := by ring
  }
  have : (x+y) = 0 ∨ (x-y) = 0 := by exact mul_eq_zero.mp this
  obtain h|h := this
  have : CharP R 2 := by{
    exact CharP.congr p h2
  }
  have : x + x =0 := by{
    exact CharTwo.add_self_eq_zero x
  }
  rw[← h] at this
  calc
    x = -x + (x + x) := by ring
      _= -x + (x + y) := by rw[this]
      _= y := by ring

  calc
    x =  x - y + y := by ring
      _= 0 + y := by rw[h]
      _= y := by ring

  have prime: Nat.Prime p := by exact hp.out

  have (z : R): (-z)^p = -z^p := by{
    refine Odd.neg_pow ?_ z
    exact Nat.Prime.odd_of_ne_two prime h2
  }
  have : (x+ -y)^p = 0 := by
    calc
      (x + -y)^p = x^p + (-y)^p := by exact add_pow_char R x (-y)
        _= x^p + -y^p := by rw[this y]
        _= y^p + -y^p := by rw[xy]
        _= 0 := by ring
  by_cases h0: p=0
  exfalso
  apply Nat.prime_def_lt''.1 at prime
  obtain ⟨u,_⟩ := prime
  linarith

  have : (x + -y) = 0 := by exact pow_eq_zero this
  calc
    x = x  + -y + y := by ring
      _= 0 + y := by rw[this]
      _= y := by ring
  }

/- Show that the Frobenius morphism is bijective on a finite domain. -/
lemma frobeniusMorphism_bijective [IsDomain R] [Finite R] :
    Function.Bijective (frobeniusMorphism p R) := by {
  apply Function.Injective.bijective_of_finite
  exact frobeniusMorphism_injective p R
  }

example [IsDomain R] [Finite R] (k : ℕ) (x : R) : x ^ p ^ k = 1 ↔ x = 1 := by {
  constructor
  swap
  intro h
  rw[h]
  ring

  intro h
  induction' k with r rh
  have : p^0 = 1 := rfl
  rw[this] at h
  rw[pow_one] at h
  assumption

  have : x ^ p ^ (r + 1) = (x ^ p ^ r )^p := by ring
  rw[this] at h
  have : (1:R)^p = 1 := by ring
  rw[← this] at h
  have t: Function.Injective (frobeniusMorphism p R) := by
    apply Bijective.injective
    exact frobeniusMorphism_bijective p R
  unfold Injective at t
  unfold frobeniusMorphism at t
  simp at t
  have : x^p^r = 1 := by exact t h
  exact rh this
  }

example {R : Type*} [CommRing R] [IsDomain R] [Finite R] [CharP R 2] (x : R) : IsSquare x := by {
  unfold IsSquare
  have : Function.Surjective (frobeniusMorphism 2 R) := by
    apply Bijective.surjective
    exact frobeniusMorphism_bijective 2 R

  specialize this x
  simp at this
  obtain ⟨a,ah⟩ := this
  use a
  ring
  symm
  assumption
  }


end Frobenius


section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
prove that the units of a ring form a group.
Hint: I recommend that you first prove that the product of two units is again a unit,
and that you define the inverse of a unit separately using `Exists.choose`.
Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
(`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

def IsAUnit.mul {x y : R} (hx : IsAUnit x) (hy : IsAUnit y) : IsAUnit (x * y) := by {
  obtain ⟨a,ah⟩ := hx
  obtain ⟨b,bh⟩ := hy
  use b*a
  calc
    b * a * (x * y) = b * (a*x) * y := by ring
      _= b*1*y := by rw[ah]
      _= b*y := by ring
      _= 1 := by rw[bh]
  }

--I didnt manage to define inv direct, so i used this lemma for what its worth
lemma ex_inv {a : R}(h: IsAUnit a): ∃(y:R), y*a = 1 := by{
  unfold IsAUnit at h
  assumption
}

instance groupUnits : Group {x : R // IsAUnit x} where
  mul := fun x y ↦ ⟨x.val * y.val, IsAUnit.mul x.property y.property⟩
  mul_assoc := by{
    intros a b c
    ext
    apply mul_assoc}
  one := ⟨(1:R), by{
    use 1
    ring
  }⟩
  one_mul := by{
    intro a
    ext
    apply one_mul
  }
  mul_one := by{
    intro a
    ext
    apply mul_one
  }
  inv := fun x ↦ ⟨Exists.choose (ex_inv x.property), by{
    use x
    rw[mul_comm]
    exact Exists.choose_spec (ex_inv x.property)
  }⟩
  inv_mul_cancel := by{
    intros a
    ext
    simp
    exact Exists.choose_spec (ex_inv a.property)
  }

-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by rfl

end Ring

/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).-/
#check exists_ne


--Isnt this just wrong in general?
lemma commutative_of_module {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by {
  by_contra p
  have : s*r - r*s ≠ 0 := by{
    by_contra t
    have : r*s = s*r := by
      calc
        r*s = r*s + 0 := by rw [@self_eq_add_right]
          _= r*s+(s*r - r*s) := by rw[t]
          _= s*r := by noncomm_ring
    contradiction
  }
  have : ∃ y : M, y ≠ 0 := by{
    exact exists_ne 0
  }
  obtain ⟨v,vh⟩ := this
  have : (s*r - r*s) • v ≠ 0 := by{
    by_contra o
    apply smul_eq_zero.1 at o
    tauto
  }
  have tt: (s * r - r * s) • v = (s*r)• v - (r * s)• v := by exact sub_smul (s * r) (r * s) v
  rw[tt] at this
  have j: (s * r) • v ≠ (r * s) • v := by{exact sub_ne_zero.mp this}
  sorry
  }

  --I actually doubt this theorem is even true. For Example just take M=R with R noncommutaive and normal multiplication * = •.
  -- For commutativity you also need to require right scalar multiplication

/-! # Exercises to hand-in. -/

/- The Frobenius morphism in a domain of characteristic `p` is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. A proof sketch is given, and the following results will be useful. -/

#check add_pow
#check CharP.cast_eq_zero_iff

variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R] [CharP R p] in
open Nat Finset in
lemma add_pow_eq_pow_add_pow (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by {
  have hp' : p.Prime := hp.out
  have range_eq_insert_Ioo : range p = insert 0 (Ioo 0 p) := by
    ext x
    constructor
    intro xh
    by_cases h0: x=0
    rw[h0]
    exact mem_insert_self 0 (Ioo 0 p)
    have : 0<x ∧ x<p:= by{
      constructor
      exact zero_lt_of_ne_zero h0
      exact List.mem_range.mp xh}
    have : x ∈ (Ioo 0 p) := by{
      exact mem_Ioo.mpr this
    }
    exact mem_insert_of_mem this

    intro h
    apply mem_range.2
    simp at h
    obtain h|h := h
    rw[h]
    exact pos_of_neZero p
    exact h.2
  have dvd_choose : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    intro i ih
    rw[Nat.choose_eq_factorial_div_factorial]
    have p1: p ∣ p ! := by {
      refine dvd_factorial ?_ ?_
      exact pos_of_neZero p
      linarith
    }
    have p2: ¬ p ∣ (i ! * (p - i)!) := by{
      refine Nat.Prime.not_dvd_mul hp' ?Hm ?Hn
      by_contra h0
      have pi: p ≤ i := by{
        exact (Prime.dvd_factorial hp').mp h0
      }
      have : 0 < i ∧ i < p := by exact (LocallyFiniteOrder.finset_mem_Ioo 0 p i).mp ih
      obtain ⟨h1,h2⟩ := this
      linarith

      by_contra h0
      have pi: p ≤ p-i := by{
        exact (Prime.dvd_factorial hp').mp h0
      }
      have : 0 < i ∧ i < p := by exact (LocallyFiniteOrder.finset_mem_Ioo 0 p i).mp ih
      obtain ⟨h1,h2⟩ := this
      have : p - i < p := by{
        refine sub_lt ?_ h1
        exact pos_of_neZero p
      }
      linarith
    }
    have u: p ! = p* (p-1) ! := by refine Eq.symm (mul_factorial_pred ?hn); exact pos_of_neZero p
    rw[u]
    have o: (i ! * (p - i)!) ∣ p ! := by{
      apply Nat.factorial_mul_factorial_dvd_factorial
      simp at ih
      linarith
    }
    rw[u] at o
    have : (i ! * (p - i)!) ∣ (p-1) ! := by{
      obtain ⟨k,hk⟩ := o
      use k / p
      have : p ∣ k := by{
        have h: p ∣ p * (p - 1)! := by exact Nat.dvd_mul_right p (p - 1)!
        rw[hk] at h
        apply (Nat.Prime.dvd_mul hp').mp at h
        obtain h|h := h
        apply (Nat.Prime.dvd_mul hp').mp at h
        obtain h|h := h
        exfalso
        apply (Nat.Prime.dvd_factorial hp').1 at h
        simp at ih
        linarith

        exfalso
        apply (Nat.Prime.dvd_factorial hp').1 at h
        simp at ih
        obtain ⟨ih1,ih2⟩ := ih
        have : p-i < p := by refine sub_lt ?_ ih1; exact pos_of_neZero p
        linarith

        assumption
      }
      obtain  ⟨r,hr⟩ := this
      rw[hr]
      rw[hr] at hk
      have hh: (p * r / p) = r := by refine Eq.symm (Nat.eq_div_of_mul_eq_right ?hc rfl); exact Nat.Prime.ne_zero hp'
      rw[hh]
      have y: i ! * (p - i)! * (p * r) = p * (i ! * (p - i) ! * r) := by ring
      rw[y] at hk
      have : p > 0 := by exact pos_of_neZero p
      exact Nat.eq_of_mul_eq_mul_left this hk


    }
    have : p * (p - 1)! / (i ! * (p - i)!) = p * ((p - 1)! / (i ! * (p - i)!)) := by {
      exact Nat.mul_div_assoc p this
    }
    exact Dvd.intro ((p - 1)! / (i ! * (p - i)!)) (id (Eq.symm this))

    simp at ih
    linarith

  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
  calc
    _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by{
      apply sum_congr rfl
      intro a ah
      specialize dvd_choose a ah
      by_cases s: x ^ a * y ^ (p - a) = 0
      rw[s]
      ring
      refine (mul_right_inj' s).mpr ?_
      exact (CharP.cast_eq_zero_iff R p (p.choose a)).mpr dvd_choose
    }

    _ = 0 := by simp

  rw[add_pow]
  have :  ∑ m ∈ range (p + 1), x ^ m * y ^ (p - m) * ↑(p.choose m) = (∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i) + (x^0 * y ^ (p-0)  * ↑(p.choose 0)) + (x ^ p * y ^ (p - p) * ↑(p.choose p)) := by{
    rw [@sum_range_add]
    rw[range_eq_insert_Ioo]
    simp
    ring
  }
  rw[this]
  clear this
  rw[h6]
  ring
  rw[Nat.choose_self]
  rw[Nat.choose_zero_right]
  ring
  have whydoesntringdothis : p-p = 0 := by exact Nat.sub_self p
  calc
    x ^ p * y ^ (p - p) + y ^ (p - 0) = x^p * y^ (0) + y ^ (p - 0) := by rw [whydoesntringdothis]
      _= x^p * y^ (0) + y ^ (p) := rfl
      _= x^p * 1 + y^p := by rw [@npow_zero]
      _= x^p +y^p := by ring
  }


section LinearMap

variable {R M₁ M₂ N M' : Type*} [CommRing R]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup M']
  [Module R M₁] [Module R M₂] [Module R N] [Module R M']

/- Define the coproduct of two linear maps, and prove the characterization below.
Note that this proof works exactly the same for vector spaces over a field as it works
for modules over a ring, so feel free to think of `M₁`, `M₂`, `N` and `M'` as vector spaces.
You might recognize this as the characterization of a *coproduct* in category theory. -/

def coproduct (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun x :=  (f x.1)+(g x.2)
  map_add' x y := by{
    simp
    module
  }
  map_smul' r x := by{
    simp
  }

-- this can be useful to have as a simp-lemma, and should be proven by `rfl`
@[simp] lemma coproduct_def (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  coproduct f g (x, y) = f x + g y := rfl

lemma coproduct_unique {f : M₁ →ₗ[R] N} {g : M₂ →ₗ[R] N} {l : M₁ × M₂ →ₗ[R] N} :
    l = coproduct f g ↔
    l.comp (LinearMap.inl R M₁ M₂) = f ∧
    l.comp (LinearMap.inr R M₁ M₂) = g := by {
  constructor
  intro h
  constructor
  repeat
    ext x
    simp
    rw[h]
    unfold coproduct
    simp

  intro h
  obtain ⟨h1,h2⟩ := h
  ext x
  unfold coproduct
  simp
  have : (x.1,0)+(0,x.2) = (x.1,x.2) := by exact Prod.fst_add_snd x
  calc
    l x = l (x.1, x.2) := by rfl
      _= l ((x.1, 0) + (0, x.2)) := by rw[this]
      _= l (x.1,0) + l (0,x.2) := by exact LinearMap.map_add l (x.1, 0) (0, x.2)
      _=  ((l ∘ₗ LinearMap.inl R M₁ M₂) x.1) +  ((l ∘ₗ LinearMap.inr R M₁ M₂) x.2) := rfl
      _= f x.1 + g x.2 := by rw[h1,h2]
  }


end LinearMap
