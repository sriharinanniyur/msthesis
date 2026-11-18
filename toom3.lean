-- Co-authored by: Fable 5.1

def nDigits (β : Nat) (hβ : 2 ≤ β) (m : Nat) : Nat :=
  if m = 0 then 0 else nDigits β hβ (m / β) + 1
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) hβ

theorem lt_pow_nDigits (β : Nat) (hβ : 2 ≤ β) (m : Nat) : m < β ^ nDigits β hβ m := by
  rw [nDigits]
  split
  · simp [*]
  · have ih := lt_pow_nDigits β hβ (m / β)
    have h1 := Nat.div_add_mod m β
    have h2 := Nat.mod_lt m (by omega : β > 0)
    calc m < β * (m / β + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ β * β ^ nDigits β hβ (m / β) := Nat.mul_le_mul_left β ih
      _ = β ^ (nDigits β hβ (m / β) + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) ‹_›

theorem nDigits_le_of_lt_pow (β : Nat) (hβ : 2 ≤ β) (m j : Nat) (h : m < β ^ j) :
    nDigits β hβ m ≤ j := by
  rw [nDigits]
  split
  · omega
  · cases j with
    | zero => simp at h; omega
    | succ j =>
      have : m / β < β ^ j := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        rw [Nat.pow_succ] at h
        exact h
      have := nDigits_le_of_lt_pow β hβ (m / β) j this
      omega
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) ‹_›


theorem limb_bounds (β : Nat) (hβ : 2 ≤ β) (x : Int) (n : Nat) (hx : x.natAbs < β ^ n) :
    let i := (n + 2) / 3
    let β' : Int := (β : Int) ^ i
    0 ≤ x % β' ∧ x % β' < β' ∧ 0 ≤ x / β' % β' ∧ x / β' % β' < β' ∧
      -β' ≤ x / β' / β' ∧ x / β' / β' < β' ∧ 8 * β' ≤ ((β ^ (i + 3) : Nat) : Int) := by
  intro i β'
  have hpos : 0 < β' := Int.pow_pos (by omega)
  have hpos2 : 0 < β' * β' := Int.mul_pos hpos hpos
  have h3 : ((β ^ n : Nat) : Int) ≤ β' * β' * β' := by
    rw [show β' * β' * β' = (β : Int) ^ (3 * i) by
          rw [show 3 * i = i + i + i by omega, Int.pow_add, Int.pow_add],
      ← Int.natCast_pow]
    exact Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega) (by omega))
  have h8 : 8 * β' ≤ ((β ^ (i + 3) : Nat) : Int) := by
    rw [Int.natCast_pow, show i + 3 = i + 1 + 1 + 1 by omega, Int.pow_succ, Int.pow_succ,
      Int.pow_succ]
    have h2 : (2 : Int) ≤ β := by omega
    have h4 : (4 : Int) ≤ β * β := by
      calc (4 : Int) = 2 * 2 := rfl
        _ ≤ β * β := Int.mul_le_mul h2 h2 (by omega) (by omega)
    have h8 : (8 : Int) ≤ β * β * β := by
      calc (8 : Int) = 4 * 2 := rfl
        _ ≤ β * β * β := Int.mul_le_mul h4 h2 (by omega) (by omega)
    calc 8 * β' = β' * 8 := Int.mul_comm _ _
      _ ≤ β' * (β * β * β) := Int.mul_le_mul_of_nonneg_left h8 (by omega)
      _ = β' * β * β * β := by ac_rfl
  have hx' : x < β' * β' * β' ∧ -(β' * β' * β') < x := by omega
  rw [Int.ediv_ediv_of_nonneg (by omega)]
  refine ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hpos,
    Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hpos, ?_, ?_, h8⟩
  · rw [Int.le_ediv_iff_mul_le hpos2]
    have : -β' * (β' * β') = -(β' * β' * β') := by rw [Int.neg_mul, Int.mul_assoc]
    omega
  · rw [Int.ediv_lt_iff_lt_mul hpos2]
    have : β' * (β' * β') = β' * β' * β' := by rw [Int.mul_assoc]
    omega

theorem nDigits_lt_of_bounds (β : Nat) (hβ : 2 ≤ β) (x y : Int) (j n : Nat)
    (hx : x.natAbs < β ^ j) (hy : y.natAbs < β ^ j) (hj : j < n) :
    nDigits β hβ (max x.natAbs y.natAbs) < n := by
  have := nDigits_le_of_lt_pow β hβ (max x.natAbs y.natAbs) j (by omega)
  omega

theorem calls_lt (β : Nat) (hβ : 2 ≤ β) (x y : Int) (n i : Nat) (β' : Int)
    (hn : 6 ≤ n) (hM : max x.natAbs y.natAbs < β ^ n)
    (hi : i = (n + 2) / 3) (hpos : β' = (β : Int) ^ i) :
    nDigits β hβ (max (x % β').natAbs (y % β').natAbs) < n ∧
    nDigits β hβ (max (x % β' + x / β' / β' + x / β' % β').natAbs
      (y % β' + y / β' / β' + y / β' % β').natAbs) < n ∧
    nDigits β hβ (max (x % β' + x / β' / β' - x / β' % β').natAbs
      (y % β' + y / β' / β' - y / β' % β').natAbs) < n ∧
    nDigits β hβ (max (x % β' + 2 * (x / β' % β') + 4 * (x / β' / β')).natAbs
      (y % β' + 2 * (y / β' % β') + 4 * (y / β' / β')).natAbs) < n ∧
    nDigits β hβ (max (x / β' / β').natAbs (y / β' / β').natAbs) < n := by
  subst hi hpos
  obtain ⟨hx0, hx0', hx1, hx1', hx2, hx2', h8⟩ := limb_bounds β hβ x n (by omega)
  obtain ⟨hy0, hy0', hy1, hy1', hy2, hy2', -⟩ := limb_bounds β hβ y n (by omega)
  have hpos : 0 < (β : Int) ^ ((n + 2) / 3) := Int.pow_pos (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact nDigits_lt_of_bounds β hβ _ _ ((n + 2) / 3 + 3) n (by omega) (by omega) (by omega)

def toom3 (β : Nat) (hβ : 2 ≤ β) (x y : Int) : Int :=
  let n := nDigits β hβ (max x.natAbs y.natAbs)
  if n < 6 then x * y
  else
    let i := (n + 2) / 3
    let β' : Int := (β : Int) ^ i
    let x0 := x % β'
    let x1 := x / β' % β'
    let x2 := x / β' / β'
    let y0 := y % β'
    let y1 := y / β' % β'
    let y2 := y / β' / β'
    let x02 := x0 + x2
    let y02 := y0 + y2
    let v0 := toom3 β hβ x0 y0
    let v1 := toom3 β hβ (x02 + x1) (y02 + y1)
    let vm1 := toom3 β hβ (x02 - x1) (y02 - y1)
    let v2 := toom3 β hβ (x0 + 2 * x1 + 4 * x2) (y0 + 2 * y1 + 4 * y2)
    let vinf := toom3 β hβ x2 y2
    let t1 := (3 * v0 + 2 * vm1 + v2) / 6 - 2 * vinf
    let t2 := (v1 + vm1) / 2
    let c0 := v0
    let c1 := v1 - t1
    let c2 := t2 - v0 - vinf
    let c3 := t1 - t2
    let c4 := vinf
    c0 + c1 * β' + c2 * β' ^ 2 + c3 * β' ^ 3 + c4 * β' ^ 4
termination_by nDigits β hβ (max x.natAbs y.natAbs)
decreasing_by
  all_goals (have hc := calls_lt β hβ x y n i β' (by omega) (lt_pow_nDigits β hβ _) rfl rfl)
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2.1
  · exact hc.2.2.2.1
  · exact hc.2.2.2.2

#eval toom3 2 (by decide) 7 7
#eval toom3 2 (by decide) 123456 654321
#eval toom3 10 (by decide) (-123456) 654321
#eval toom3 10 (by decide) 1000003 999983
#eval 1000003 * 999983

theorem split3 (x β' : Int) : x = x % β' + (x / β' % β') * β' + (x / β' / β') * β' ^ 2 := by
  have h1 := Int.emod_add_mul_ediv x β'
  have h2 := Int.emod_add_mul_ediv (x / β') β'
  grind

theorem interp_div6 (x0 x1 x2 y0 y1 y2 : Int) :
    3 * (x0 * y0) + 2 * ((x0 + x2 - x1) * (y0 + y2 - y1))
      + (x0 + 2 * x1 + 4 * x2) * (y0 + 2 * y1 + 4 * y2)
      = 6 * (x0 * y0 + (x0 * y2 + x1 * y1 + x2 * y0) + (x1 * y2 + x2 * y1) + 3 * (x2 * y2)) := by
  grind

theorem interp_div2 (x0 x1 x2 y0 y1 y2 : Int) :
    (x0 + x2 + x1) * (y0 + y2 + y1) + (x0 + x2 - x1) * (y0 + y2 - y1)
      = 2 * (x0 * y0 + (x0 * y2 + x1 * y1 + x2 * y0) + x2 * y2) := by
  grind

theorem recombine (x0 x1 x2 y0 y1 y2 β' : Int) :
    let c0 := x0 * y0
    let c2 := x0 * y2 + x1 * y1 + x2 * y0
    let c3 := x1 * y2 + x2 * y1
    let c4 := x2 * y2
    let v1 := (x0 + x2 + x1) * (y0 + y2 + y1)
    let t1 := c0 + c2 + c3 + 3 * c4 - 2 * c4
    let t2 := c0 + c2 + c4
    c0 + (v1 - t1) * β' + (t2 - c0 - c4) * β' ^ 2 + (t1 - t2) * β' ^ 3 + c4 * β' ^ 4
      = (x0 + x1 * β' + x2 * β' ^ 2) * (y0 + y1 * β' + y2 * β' ^ 2) := by
  intro c0 c2 c3 c4 v1 t1 t2
  grind

theorem toom3_step (x y β' x0 x1 x2 y0 y1 y2 v0 v1 vm1 v2 vinf : Int)
    (hx : x = x0 + x1 * β' + x2 * β' ^ 2) (hy : y = y0 + y1 * β' + y2 * β' ^ 2)
    (h0 : v0 = x0 * y0)
    (h1 : v1 = (x0 + x2 + x1) * (y0 + y2 + y1))
    (hm1 : vm1 = (x0 + x2 - x1) * (y0 + y2 - y1))
    (h2 : v2 = (x0 + 2 * x1 + 4 * x2) * (y0 + 2 * y1 + 4 * y2))
    (hinf : vinf = x2 * y2) :
    let t1 := (3 * v0 + 2 * vm1 + v2) / 6 - 2 * vinf
    let t2 := (v1 + vm1) / 2
    v0 + (v1 - t1) * β' + (t2 - v0 - vinf) * β' ^ 2 + (t1 - t2) * β' ^ 3 + vinf * β' ^ 4 = x * y := by
  intro t1 t2
  subst h0 h1 hm1 h2 hinf
  simp only [t1, t2]
  rw [interp_div6, interp_div2, Int.mul_ediv_cancel_left _ (by decide),
    Int.mul_ediv_cancel_left _ (by decide), recombine, ← hx, ← hy]

theorem toom3_correct (β : Nat) (hβ : 2 ≤ β) (x y : Int) : toom3 β hβ x y = x * y := by
  induction x, y using toom3.induct β hβ with
  | case1 x y n h =>
    rw [toom3]
    exact ite_eq_left h
  | case2 x y n h i β' x0 x1 x2 y0 y1 y2 x02 y02 ih0 ih1 ihm1 ih2 ihinf =>
    rw [toom3]
    exact (ite_eq_right h).trans (toom3_step x y β' x0 x1 x2 y0 y1 y2 _ _ _ _ _
      (split3 x β') (split3 y β') ih0 ih1 ihm1 ih2 ihinf)
