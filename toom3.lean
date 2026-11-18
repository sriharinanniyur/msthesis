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


theorem limb_bounds (β : Nat) (hβ : 2 ≤ β) (a : Int) (n : Nat) (ha : a.natAbs < β ^ n) :
    let i := (n + 2) / 3
    let β' : Int := (β : Int) ^ i
    0 ≤ a % β' ∧ a % β' < β' ∧ 0 ≤ a / β' % β' ∧ a / β' % β' < β' ∧
      -β' ≤ a / β' / β' ∧ a / β' / β' < β' ∧ 8 * β' ≤ ((β ^ (i + 3) : Nat) : Int) := by
  intro i β'
  have hx : 0 < β' := Int.pow_pos (by omega)
  have hxx : 0 < β' * β' := Int.mul_pos hx hx
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
  have ha' : a < β' * β' * β' ∧ -(β' * β' * β') < a := by omega
  rw [Int.ediv_ediv_of_nonneg (by omega)]
  refine ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hx,
    Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hx, ?_, ?_, h8⟩
  · rw [Int.le_ediv_iff_mul_le hxx]
    have : -β' * (β' * β') = -(β' * β' * β') := by rw [Int.neg_mul, Int.mul_assoc]
    omega
  · rw [Int.ediv_lt_iff_lt_mul hxx]
    have : β' * (β' * β') = β' * β' * β' := by rw [Int.mul_assoc]
    omega

theorem nDigits_lt_of_bounds (β : Nat) (hβ : 2 ≤ β) (a b : Int) (j n : Nat)
    (ha : a.natAbs < β ^ j) (hb : b.natAbs < β ^ j) (hj : j < n) :
    nDigits β hβ (max a.natAbs b.natAbs) < n := by
  have := nDigits_le_of_lt_pow β hβ (max a.natAbs b.natAbs) j (by omega)
  omega

theorem calls_lt (β : Nat) (hβ : 2 ≤ β) (a b : Int) (n i : Nat) (β' : Int)
    (hn : 6 ≤ n) (hM : max a.natAbs b.natAbs < β ^ n)
    (hi : i = (n + 2) / 3) (hx : β' = (β : Int) ^ i) :
    nDigits β hβ (max (a % β').natAbs (b % β').natAbs) < n ∧
    nDigits β hβ (max (a % β' + a / β' / β' + a / β' % β').natAbs
      (b % β' + b / β' / β' + b / β' % β').natAbs) < n ∧
    nDigits β hβ (max (a % β' + a / β' / β' - a / β' % β').natAbs
      (b % β' + b / β' / β' - b / β' % β').natAbs) < n ∧
    nDigits β hβ (max (a % β' + 2 * (a / β' % β') + 4 * (a / β' / β')).natAbs
      (b % β' + 2 * (b / β' % β') + 4 * (b / β' / β')).natAbs) < n ∧
    nDigits β hβ (max (a / β' / β').natAbs (b / β' / β').natAbs) < n := by
  subst hi hx
  obtain ⟨ha0, ha0', ha1, ha1', ha2, ha2', h8⟩ := limb_bounds β hβ a n (by omega)
  obtain ⟨hb0, hb0', hb1, hb1', hb2, hb2', -⟩ := limb_bounds β hβ b n (by omega)
  have hx : 0 < (β : Int) ^ ((n + 2) / 3) := Int.pow_pos (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact nDigits_lt_of_bounds β hβ _ _ ((n + 2) / 3 + 3) n (by omega) (by omega) (by omega)

def toom3 (β : Nat) (hβ : 2 ≤ β) (a b : Int) : Int :=
  let n := nDigits β hβ (max a.natAbs b.natAbs)
  if n < 6 then a * b
  else
    let i := (n + 2) / 3
    let β' : Int := (β : Int) ^ i
    let a0 := a % β'
    let a1 := a / β' % β'
    let a2 := a / β' / β'
    let b0 := b % β'
    let b1 := b / β' % β'
    let b2 := b / β' / β'
    let a02 := a0 + a2
    let b02 := b0 + b2
    let v0 := toom3 β hβ a0 b0
    let v1 := toom3 β hβ (a02 + a1) (b02 + b1)
    let vm1 := toom3 β hβ (a02 - a1) (b02 - b1)
    let v2 := toom3 β hβ (a0 + 2 * a1 + 4 * a2) (b0 + 2 * b1 + 4 * b2)
    let vinf := toom3 β hβ a2 b2
    let t1 := (3 * v0 + 2 * vm1 + v2) / 6 - 2 * vinf
    let t2 := (v1 + vm1) / 2
    let c0 := v0
    let c1 := v1 - t1
    let c2 := t2 - v0 - vinf
    let c3 := t1 - t2
    let c4 := vinf
    c0 + c1 * β' + c2 * β' ^ 2 + c3 * β' ^ 3 + c4 * β' ^ 4
termination_by nDigits β hβ (max a.natAbs b.natAbs)
decreasing_by
  all_goals (have hc := calls_lt β hβ a b n i β' (by omega) (lt_pow_nDigits β hβ _) rfl rfl)
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

theorem split3 (a x : Int) : a = a % x + (a / x % x) * x + (a / x / x) * x ^ 2 := by
  have h1 := Int.emod_add_mul_ediv a x
  have h2 := Int.emod_add_mul_ediv (a / x) x
  grind

theorem interp_div6 (a0 a1 a2 b0 b1 b2 : Int) :
    3 * (a0 * b0) + 2 * ((a0 + a2 - a1) * (b0 + b2 - b1))
      + (a0 + 2 * a1 + 4 * a2) * (b0 + 2 * b1 + 4 * b2)
      = 6 * (a0 * b0 + (a0 * b2 + a1 * b1 + a2 * b0) + (a1 * b2 + a2 * b1) + 3 * (a2 * b2)) := by
  grind

theorem interp_div2 (a0 a1 a2 b0 b1 b2 : Int) :
    (a0 + a2 + a1) * (b0 + b2 + b1) + (a0 + a2 - a1) * (b0 + b2 - b1)
      = 2 * (a0 * b0 + (a0 * b2 + a1 * b1 + a2 * b0) + a2 * b2) := by
  grind

theorem recombine (a0 a1 a2 b0 b1 b2 x : Int) :
    let c0 := a0 * b0
    let c2 := a0 * b2 + a1 * b1 + a2 * b0
    let c3 := a1 * b2 + a2 * b1
    let c4 := a2 * b2
    let v1 := (a0 + a2 + a1) * (b0 + b2 + b1)
    let t1 := c0 + c2 + c3 + 3 * c4 - 2 * c4
    let t2 := c0 + c2 + c4
    c0 + (v1 - t1) * x + (t2 - c0 - c4) * x ^ 2 + (t1 - t2) * x ^ 3 + c4 * x ^ 4
      = (a0 + a1 * x + a2 * x ^ 2) * (b0 + b1 * x + b2 * x ^ 2) := by
  intro c0 c2 c3 c4 v1 t1 t2
  grind

theorem toom3_step (a b x a0 a1 a2 b0 b1 b2 v0 v1 vm1 v2 vinf : Int)
    (ha : a = a0 + a1 * x + a2 * x ^ 2) (hb : b = b0 + b1 * x + b2 * x ^ 2)
    (h0 : v0 = a0 * b0)
    (h1 : v1 = (a0 + a2 + a1) * (b0 + b2 + b1))
    (hm1 : vm1 = (a0 + a2 - a1) * (b0 + b2 - b1))
    (h2 : v2 = (a0 + 2 * a1 + 4 * a2) * (b0 + 2 * b1 + 4 * b2))
    (hinf : vinf = a2 * b2) :
    let t1 := (3 * v0 + 2 * vm1 + v2) / 6 - 2 * vinf
    let t2 := (v1 + vm1) / 2
    v0 + (v1 - t1) * x + (t2 - v0 - vinf) * x ^ 2 + (t1 - t2) * x ^ 3 + vinf * x ^ 4 = a * b := by
  intro t1 t2
  subst h0 h1 hm1 h2 hinf
  simp only [t1, t2]
  rw [interp_div6, interp_div2, Int.mul_ediv_cancel_left _ (by decide),
    Int.mul_ediv_cancel_left _ (by decide), recombine, ← ha, ← hb]

theorem toom3_correct (β : Nat) (hβ : 2 ≤ β) (a b : Int) : toom3 β hβ a b = a * b := by
  induction a, b using toom3.induct β hβ with
  | case1 a b n h =>
    rw [toom3]
    exact ite_eq_left h
  | case2 a b n h i β' a0 a1 a2 b0 b1 b2 a02 b02 ih0 ih1 ihm1 ih2 ihinf =>
    rw [toom3]
    exact (ite_eq_right h).trans (toom3_step a b β' a0 a1 a2 b0 b1 b2 _ _ _ _ _
      (split3 a β') (split3 b β') ih0 ih1 ihm1 ih2 ihinf)
