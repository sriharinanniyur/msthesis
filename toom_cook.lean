-- Co-authored by: Aristotle, GPT-5, and Fable 5.1

import Mathlib

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise


--- GENERAL UTILITY FUNCTIONS AND LEMMAS
def digits (b : ℕ) (x : ℤ) : ℕ :=
  if x = 0 then 1 else (Nat.log b (Int.natAbs x)) + 1

def eval_vec_as_poly {K : ℕ} (split : Vector ℕ K) (x : ℤ) : ℤ :=
  ∑ i : Fin K, (split.get i : ℤ) * x ^ (i.1)

def eval_vec_as_poly_Q {K : ℕ} (split : Vector ℚ K) (x : ℚ) : ℚ :=
  ∑ i : Fin K, (split.get i : ℚ) * x ^ (i.1)

---------------------------------------------------------------------
-- SHARED VARIABLES AND CONSTRAINTS
---------------------------------------------------------------------
def tk_P (BASE : ℕ) (x y : ℤ) : ℕ :=
  (digits BASE (max x.natAbs y.natAbs))

def tk_i (KX KY BASE : ℕ) (x y : ℤ) : ℕ :=
  (max
    (((digits BASE x) + KX - 1) / KX) -- ceiling-division trick
    (((digits BASE y) + KY - 1) / KY))

def tk_B (KX KY BASE : ℕ) (x y : ℤ) : ℕ :=
  BASE ^ (tk_i KX KY BASE x y)

def tk_split (KX KY KZ BASE : ℕ) (x y : ℕ) (z : ℕ) : Vector ℕ KZ :=
  Vector.ofFn (fun i : Fin KZ =>
    (z / (tk_B KX KY BASE x y) ^ i.1) % (tk_B KX KY BASE x y))


def tk_vmax
  (KX KY : ℕ) (POINTS : Vector ℤ (KX+KY-1)) : ℕ :=
  POINTS.toList.foldl (fun acc z => max acc z.natAbs) 0

def tk_CX
  (BASE KX KY : ℕ)
  (POINTS : Vector ℤ (KX+KY-1))
: ℕ :=
  let v_max := tk_vmax KX KY POINTS
  digits BASE ((∑ i ∈ Finset.range KX, v_max ^ i) : ℤ)

def tk_CY
  (BASE KX KY : ℕ)
  (POINTS : Vector ℤ (KX+KY-1))
: ℕ :=
  let v_max := tk_vmax KX KY POINTS
  digits BASE ((∑ i ∈ Finset.range KY, v_max ^ i) : ℤ)

def tk_C
  (BASE KX KY : ℕ)
  (POINTS : Vector ℤ (KX+KY-1))
: ℕ :=
  (max (tk_CX BASE KX KY POINTS) (tk_CY BASE KX KY POINTS)) + 1

def tk_THETA
  (BASE KX KY : ℕ)
  (POINTS : Vector ℤ (KX+KY-1))
: ℚ :=
  let C := ((tk_C BASE KX KY POINTS) : ℚ)
  let K_MIN := ((min KX KY) : ℚ)
  (C * K_MIN) / (K_MIN - (1 : ℚ))

/-- `digits` only depends on the absolute value. -/
lemma digits_eq_natAbs (b : ℕ) (x : ℤ) : digits b x = digits b (x.natAbs : ℤ) := by
  unfold digits
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx, Int.natAbs_abs]

/-- `digits` of a natural number, as a natural number. -/
lemma digits_nat (b : ℕ) (n : ℕ) :
    digits b (n : ℤ) = if n = 0 then 1 else Nat.log b n + 1 := by
  unfold digits
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

lemma one_le_digits (b : ℕ) (x : ℤ) : 1 ≤ digits b x := by
  unfold digits
  by_cases hx : x = 0 <;> simp [hx]

lemma digits_pos (b : ℕ) (x : ℤ) : 0 < digits b x := one_le_digits b x

/-- Any number is smaller than `b ^ (number of its digits)`. -/
lemma lt_pow_digits {b : ℕ} (hb : 1 < b) (x : ℤ) : x.natAbs < b ^ (digits b x) := by
  rw [digits_eq_natAbs, digits_nat]
  by_cases hx : x.natAbs = 0
  · simp [hx, Nat.lt_of_lt_of_le Nat.zero_lt_one (by simpa using hb.le)]
  · simp only [hx, ite_false]
    exact Nat.lt_pow_succ_log_self hb _

/-- If `|x| < b ^ k` with `k ≥ 1` then `x` has at most `k` digits. -/
lemma digits_le_of_lt_pow {b : ℕ} {x : ℤ} {k : ℕ} (hk : 0 < k)
    (h : x.natAbs < b ^ k) : digits b x ≤ k := by
  rw [digits_eq_natAbs, digits_nat]
  by_cases hx : x.natAbs = 0
  · grind
  · simp only [hx, ite_false]
    exact Nat.log_lt_of_lt_pow hx h

lemma digits_abs (b : ℕ) (x : ℤ) : digits b |x| = digits b x := by
  rw [digits_eq_natAbs b |x|, digits_eq_natAbs b x, Int.natAbs_abs]

lemma digits_mono {b : ℕ} {x y : ℤ} (h : x.natAbs ≤ y.natAbs) :
    digits b x ≤ digits b y := by
  rw [digits_eq_natAbs b x, digits_eq_natAbs b y, digits_nat, digits_nat]
  by_cases hx : x.natAbs = 0
  · simp only [hx, ite_true]
    by_cases hy : y.natAbs = 0 <;> simp [hy]
  · have hy : y.natAbs ≠ 0 := by omega
    simp only [hx, hy, ite_false]
    exact Nat.succ_le_succ (Nat.log_mono_right h)

/-!
## Supporting material for the termination lemmas
-/

/-- A convenient variant of `digits_le_of_lt_pow` phrased with `|·|` over `ℤ`. -/
lemma digits_le_of_abs_lt {b : ℕ} {x : ℤ} {k : ℕ} (hk : 0 < k)
    (h : |x| < (b : ℤ) ^ k) : digits b x ≤ k := by
  refine digits_le_of_lt_pow hk ?_
  have h1 : ((x.natAbs : ℕ) : ℤ) < ((b : ℤ)) ^ k := by
    rwa [← Int.abs_eq_natAbs]
  have h2 : ((x.natAbs : ℕ) : ℤ) < ((b ^ k : ℕ) : ℤ) := by
    simpa using h1
  exact_mod_cast h2

/-! ### Basic facts about the split -/

lemma tk_i_pos (KX KY BASE : ℕ) (hk : 0 < KX ∨ 0 < KY) (x y : ℤ) :
    0 < tk_i KX KY BASE x y := by
  have hx := one_le_digits BASE x
  have hy := one_le_digits BASE y
  unfold tk_i
  rcases hk with hk | hk
  · have : 1 ≤ (digits BASE x + KX - 1) / KX := by
      apply Nat.one_le_div_iff hk |>.mpr
      omega
    omega
  · have : 1 ≤ (digits BASE y + KY - 1) / KY := by
      apply Nat.one_le_div_iff hk |>.mpr
      omega
    omega

lemma tk_B_pos (KX KY BASE : ℕ) (hb : 0 < BASE) (x y : ℤ) : 0 < tk_B KX KY BASE x y :=
  pow_pos hb _

lemma tk_split_lt (KX KY KZ BASE : ℕ) (hb : 1 < BASE) (x y z : ℕ) (i : Fin KZ) :
    (tk_split KX KY KZ BASE x y z).get i < tk_B KX KY BASE x y := by
  have hB : 0 < tk_B KX KY BASE x y := tk_B_pos KX KY BASE (by omega) _ _
  simp only [tk_split, Vector.get_ofFn]
  exact Nat.mod_lt _ hB

/-! ### Bounding the size of an evaluated split -/

/-- The absolute value of a polynomial with limbs `< B` evaluated at a point of size `≤ V`. -/
lemma abs_eval_vec_lt {KZ : ℕ} (hKZ : 0 < KZ) (s : Vector ℕ KZ) (B V : ℕ)
    (hs : ∀ i : Fin KZ, s.get i < B) (p : ℤ) (hp : p.natAbs ≤ V) :
    |eval_vec_as_poly s p| < (B : ℤ) * ∑ j ∈ Finset.range KZ, (V : ℤ) ^ j := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hs ⟨0, hKZ⟩)
  have hSpos : (0 : ℤ) < ∑ j ∈ Finset.range KZ, (V : ℤ) ^ j := by
    have : ∀ j ∈ Finset.range KZ, (0 : ℤ) ≤ (V : ℤ) ^ j := by
      intro j _; positivity
    have h0 : (0 : ℕ) ∈ Finset.range KZ := Finset.mem_range.mpr hKZ
    calc (0:ℤ) < (V:ℤ) ^ (0:ℕ) := by norm_num
      _ ≤ _ := Finset.single_le_sum this h0
  have habs : |p| ≤ (V : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hp
  have step : |eval_vec_as_poly s p| ≤ ((B : ℤ) - 1) * ∑ j ∈ Finset.range KZ, (V : ℤ) ^ j := by
    have h1 : |eval_vec_as_poly s p| ≤ ∑ i : Fin KZ, |(s.get i : ℤ) * p ^ (i.1)| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ i : Fin KZ, |(s.get i : ℤ) * p ^ (i.1)| ≤ ((B : ℤ) - 1) * (V : ℤ) ^ (i.1) := by
      intro i
      have hsi : ((s.get i : ℤ)) ≤ (B : ℤ) - 1 := by
        have := hs i
        have : (s.get i : ℤ) < (B : ℤ) := by exact_mod_cast this
        omega
      have hpp : |p| ^ (i.1) ≤ (V : ℤ) ^ (i.1) :=
        pow_le_pow_left₀ (abs_nonneg p) habs _
      calc |(s.get i : ℤ) * p ^ (i.1)| = (s.get i : ℤ) * |p| ^ (i.1) := by
            rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0:ℤ) ≤ (s.get i : ℤ))]
        _ ≤ ((B : ℤ) - 1) * (V : ℤ) ^ (i.1) := by
            apply mul_le_mul hsi hpp (by positivity) (by omega)
    calc |eval_vec_as_poly s p| ≤ ∑ i : Fin KZ, |(s.get i : ℤ) * p ^ (i.1)| := h1
      _ ≤ ∑ _i : Fin KZ, ((B : ℤ) - 1) * (V : ℤ) ^ ((_i : Fin KZ).1) :=
          Finset.sum_le_sum (fun i _ => h2 i)
      _ = ((B : ℤ) - 1) * ∑ i : Fin KZ, (V : ℤ) ^ (i.1) := by rw [← Finset.mul_sum]
      _ = ((B : ℤ) - 1) * ∑ j ∈ Finset.range KZ, (V : ℤ) ^ j := by
          rw [Fin.sum_univ_eq_sum_range (fun j => (V : ℤ) ^ j) KZ]
  have : ((B : ℤ) - 1) * ∑ j ∈ Finset.range KZ, (V : ℤ) ^ j
      < (B : ℤ) * ∑ j ∈ Finset.range KZ, (V : ℤ) ^ j := by
    have := hSpos
    nlinarith
  linarith

/-- Digit bound on the evaluation of a split at a point of size at most `V`. -/
lemma digits_eval_split_le {KX KY KZ BASE : ℕ} (h_base : 1 < BASE) (hKZ : 0 < KZ)
    (hk : 0 < KX ∨ 0 < KY) (x y z : ℕ) (V : ℕ) (p : ℤ) (hp : p.natAbs ≤ V) :
    digits BASE (eval_vec_as_poly (tk_split KX KY KZ BASE x y z) p)
      ≤ tk_i KX KY BASE x y + digits BASE ((∑ j ∈ Finset.range KZ, (V : ℤ) ^ j)) := by
  set S : ℤ := ∑ j ∈ Finset.range KZ, (V : ℤ) ^ j with hS
  set CZ : ℕ := digits BASE S with hCZ
  have hSnonneg : (0 : ℤ) ≤ S := by
    rw [hS]; positivity
  have hSlt : S < (BASE : ℤ) ^ CZ := by
    have := lt_pow_digits h_base S
    have h2 : ((S.natAbs : ℕ) : ℤ) < ((BASE ^ CZ : ℕ) : ℤ) := by exact_mod_cast this
    rw [Int.natAbs_of_nonneg hSnonneg] at h2
    simpa using h2
  have hbound := abs_eval_vec_lt hKZ (tk_split KX KY KZ BASE x y z)
      (tk_B KX KY BASE x y) V (fun i => tk_split_lt KX KY KZ BASE h_base x y z i) p hp
  have hBpos : (0 : ℤ) < (tk_B KX KY BASE x y : ℤ) := by
    exact_mod_cast tk_B_pos KX KY BASE (by omega) (x : ℤ) (y : ℤ)
  have hfinal : |eval_vec_as_poly (tk_split KX KY KZ BASE x y z) p|
      < (BASE : ℤ) ^ (tk_i KX KY BASE x y + CZ) := by
    have h1 : (tk_B KX KY BASE x y : ℤ) * S ≤ (tk_B KX KY BASE x y : ℤ) * (BASE : ℤ) ^ CZ := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hSlt) (le_of_lt hBpos)
    have h2 : (tk_B KX KY BASE x y : ℤ) = (BASE : ℤ) ^ (tk_i KX KY BASE x y) := by
      simp [tk_B]
    calc |eval_vec_as_poly (tk_split KX KY KZ BASE x y z) p|
        < (tk_B KX KY BASE x y : ℤ) * S := by simpa [hS] using hbound
      _ ≤ (tk_B KX KY BASE x y : ℤ) * (BASE : ℤ) ^ CZ := h1
      _ = (BASE : ℤ) ^ (tk_i KX KY BASE x y + CZ) := by rw [h2, pow_add]
  refine digits_le_of_abs_lt ?_ hfinal
  have := tk_i_pos KX KY BASE hk (x : ℤ) (y : ℤ)
  omega

/-! ### `tk_vmax` bounds the points -/

private lemma acc_le_foldl_max (l : List ℤ) (acc : ℕ) :
    acc ≤ l.foldl (fun a w => max a w.natAbs) acc := by
  induction l generalizing acc with
  | nil => simp
  | cons w t ih =>
      have := ih (max acc w.natAbs)
      simp only [List.foldl_cons]
      omega

private lemma mem_le_foldl_max (l : List ℤ) (acc : ℕ) (z : ℤ) (hz : z ∈ l) :
    z.natAbs ≤ l.foldl (fun a w => max a w.natAbs) acc := by
  induction l generalizing acc with
  | nil => simp at hz
  | cons w t ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hz with h | h
      · subst h
        have := acc_le_foldl_max t (max acc z.natAbs)
        omega
      · exact ih (max acc w.natAbs) h

lemma le_tk_vmax {KX KY : ℕ} (POINTS : Vector ℤ (KX + KY - 1)) {p : ℤ} (hp : p ∈ POINTS) :
    p.natAbs ≤ tk_vmax KX KY POINTS :=
  mem_le_foldl_max _ 0 p (Vector.mem_toList_iff.mpr hp)

/-! ### The two evaluation bounds -/

lemma tk_i_le (KX KY BASE : ℕ) (hk : 1 < KX ∧ 1 < KY) (x y : ℕ) :
    (tk_i KX KY BASE x y : ℚ) ≤ (tk_P BASE x y : ℚ) / (min KX KY : ℚ) + 1 := by
  obtain ⟨hKX, hKY⟩ := hk
  set Km := min KX KY with hKm
  have hKm0 : 0 < Km := by simp [hKm]; omega
  set P := tk_P BASE (x : ℤ) (y : ℤ) with hP
  have hPx : digits BASE (x : ℤ) ≤ P := by
    rw [hP, tk_P]
    exact digits_mono (by omega)
  have hPy : digits BASE (y : ℤ) ≤ P := by
    rw [hP, tk_P]
    exact digits_mono (by omega)
  have key : ∀ (d K : ℕ), Km ≤ K → d ≤ P → (d + K - 1) / K ≤ P / Km + 1 := by
    intro d K hKK hd
    have hK0 : 0 < K := lt_of_lt_of_le hKm0 hKK
    have hPlt : P < (P / Km + 1) * Km := by
      have := Nat.div_add_mod P Km
      have hm : P % Km < Km := Nat.mod_lt _ hKm0
      nlinarith [Nat.div_add_mod P Km]
    have hPlt' : P < (P / Km + 1) * K := by
      calc P < (P / Km + 1) * Km := hPlt
        _ ≤ (P / Km + 1) * K := Nat.mul_le_mul_left _ hKK
    have hexp : (P / Km + 2) * K = (P / Km + 1) * K + K := by ring
    have : d + K - 1 < (P / Km + 2) * K := by omega
    have := (Nat.div_lt_iff_lt_mul hK0).mpr this
    omega
  have hnat : tk_i KX KY BASE x y ≤ P / Km + 1 := by
    unfold tk_i
    have h1 := key (digits BASE (x : ℤ)) KX (by simp [hKm]) hPx
    have h2 := key (digits BASE (y : ℤ)) KY (by simp [hKm]) hPy
    omega
  have hcast : ((P / Km : ℕ) : ℚ) ≤ (P : ℚ) / (Km : ℚ) := Nat.cast_div_le
  have hmin : ((Km : ℕ) : ℚ) = min (KX : ℚ) (KY : ℚ) := by
    rw [hKm]; push_cast; ring
  have h3 : ((tk_i KX KY BASE x y : ℕ) : ℚ) ≤ ((P / Km : ℕ) : ℚ) + 1 := by
    exact_mod_cast hnat
  rw [← hmin]
  linarith

lemma eval_bound_gen
  (KX KY KZ BASE : ℕ)
  (h_base : 1 < BASE)
  (hk : 1 < KX ∧ 1 < KY)
  (hKZ : 0 < KZ)
  (x y z : ℕ)
  (POINTS : Vector ℤ (KX+KY-1))
  (CZ : ℕ)
  (hCZ : digits BASE ((∑ j ∈ Finset.range KZ, ((tk_vmax KX KY POINTS : ℕ) : ℤ) ^ j)) ≤ CZ)
: ∀ p ∈ POINTS, ((digits BASE (eval_vec_as_poly (tk_split KX KY KZ BASE x y z) p) : ℚ))
    ≤ ((tk_P BASE x y : ℚ) / (min KX KY : ℚ)) + (1 + CZ) := by
  intro p hp
  have hpv : p.natAbs ≤ tk_vmax KX KY POINTS := le_tk_vmax POINTS hp
  have h1 := digits_eval_split_le (KX := KX) (KY := KY) (KZ := KZ) h_base hKZ
      (Or.inl (by omega)) x y z (tk_vmax KX KY POINTS) p hpv
  have h2 := tk_i_le KX KY BASE hk x y
  have h1' : ((digits BASE (eval_vec_as_poly (tk_split KX KY KZ BASE x y z) p) : ℕ) : ℚ)
      ≤ (tk_i KX KY BASE x y : ℚ) + (CZ : ℚ) := by
    have hn : digits BASE (eval_vec_as_poly (tk_split KX KY KZ BASE x y z) p)
        ≤ tk_i KX KY BASE x y + CZ := le_trans h1 (by omega)
    exact_mod_cast hn
  linarith

/-- `tk_P` is the max of the two digit counts. -/
lemma tk_P_eq (BASE : ℕ) (a b : ℤ) :
    tk_P BASE a b = max (digits BASE a) (digits BASE b) := by
  unfold tk_P
  rcases le_total a.natAbs b.natAbs with h | h
  · have hz : ((a.natAbs : ℤ)) ≤ ((b.natAbs : ℤ)) := by exact_mod_cast h
    rw [max_eq_right hz, ← digits_eq_natAbs, max_eq_right (digits_mono h)]
  · have hz : ((b.natAbs : ℤ)) ≤ ((a.natAbs : ℤ)) := by exact_mod_cast h
    rw [max_eq_left hz, ← digits_eq_natAbs, max_eq_left (digits_mono h)]

lemma tk_P_natAbs (BASE : ℕ) (a b : ℤ) :
    tk_P BASE (a.natAbs : ℤ) (b.natAbs : ℤ) = tk_P BASE a b := by
  rw [tk_P_eq, tk_P_eq, ← digits_eq_natAbs, ← digits_eq_natAbs]

lemma eval_bound_y
  (KX KY BASE : ℕ)
  (h_base : 1 < BASE)
  (hk : 1 < KX ∧ 1 < KY)
  (x y : ℕ)
  (POINTS : Vector ℤ (KX+KY-1))
: ∀ p ∈ POINTS, ((digits BASE (eval_vec_as_poly (tk_split KX KY KY BASE x y y) p) : ℚ))
≤ ((tk_P BASE x y : ℚ) / (min KX KY : ℚ)) + (tk_C BASE KX KY POINTS : ℚ) := by
  intro p hp
  have hCY : digits BASE ((∑ j ∈ Finset.range KY, ((tk_vmax KX KY POINTS : ℕ) : ℤ) ^ j))
      ≤ tk_CY BASE KX KY POINTS := le_of_eq (by simp [tk_CY])
  have hgen := eval_bound_gen KX KY KY BASE h_base hk (by omega) x y y POINTS
      (tk_CY BASE KX KY POINTS) hCY p hp
  have hC : tk_CY BASE KX KY POINTS + 1 ≤ tk_C BASE KX KY POINTS := by
    simp [tk_C]
  have hC' : ((tk_CY BASE KX KY POINTS : ℚ)) + 1 ≤ (tk_C BASE KX KY POINTS : ℚ) := by
    exact_mod_cast hC
  linarith

lemma decrease_property_aux
  (KX KY BASE : ℕ)
  (hk : 1 < KX ∧ 1 < KY)
  (x y : ℕ)
  (POINTS : Vector ℤ (KX+KY-1))
  (h_THETA : (tk_P BASE x y) > (tk_THETA BASE KX KY POINTS))
: ((tk_P BASE x y : ℚ) / (min KX KY : ℚ)) + (tk_C BASE KX KY POINTS : ℚ) < (tk_P BASE x y : ℚ)
:= by
  obtain ⟨hKX, hKY⟩ := hk
  set Km := min KX KY with hKm
  have hKm2 : 2 ≤ Km := by simp [hKm]; omega
  set P := tk_P BASE (x : ℤ) (y : ℤ) with hP
  set C := tk_C BASE KX KY POINTS with hC
  have hKmQ : (2 : ℚ) ≤ (Km : ℚ) := by exact_mod_cast hKm2
  have hden : (0 : ℚ) < (Km : ℚ) - 1 := by linarith
  have hKmpos : (0 : ℚ) < (Km : ℚ) := by linarith
  have hmin : ((Km : ℕ) : ℚ) = min (KX : ℚ) (KY : ℚ) := by
    rw [hKm]; push_cast; ring
  have hth : ((C : ℚ) * (Km : ℚ)) / ((Km : ℚ) - 1) < (P : ℚ) := by
    have := h_THETA
    simpa [tk_THETA, hC, hKm, hP] using this
  have hmul : (C : ℚ) * (Km : ℚ) < (P : ℚ) * ((Km : ℚ) - 1) := by
    rw [div_lt_iff₀ hden] at hth
    linarith
  have hdiv : (P : ℚ) / (Km : ℚ) < (P : ℚ) - (C : ℚ) := by
    rw [div_lt_iff₀ hKmpos]
    nlinarith
  rw [← hmin]
  linarith

lemma eval_bound_x
  (KX KY BASE : ℕ)
  (h_base : 1 < BASE)
  (hk : 1 < KX ∧ 1 < KY)
  (x y : ℕ)
  (POINTS : Vector ℤ (KX+KY-1))
: ∀ p ∈ POINTS, ((digits BASE (eval_vec_as_poly (tk_split KX KY KX BASE x y x) p) : ℚ))
≤ ((tk_P BASE x y : ℚ) / (min KX KY : ℚ)) + (tk_C BASE KX KY POINTS : ℚ) := by
  intro p hp
  have hCX : digits BASE ((∑ j ∈ Finset.range KX, ((tk_vmax KX KY POINTS : ℕ) : ℤ) ^ j))
      ≤ tk_CX BASE KX KY POINTS := le_of_eq (by simp [tk_CX])
  have hgen := eval_bound_gen KX KY KX BASE h_base hk (by omega) x y x POINTS
      (tk_CX BASE KX KY POINTS) hCX p hp
  have hC : tk_CX BASE KX KY POINTS + 1 ≤ tk_C BASE KX KY POINTS := by
    simp [tk_C]
  have hC' : ((tk_CX BASE KX KY POINTS : ℚ)) + 1 ≤ (tk_C BASE KX KY POINTS : ℚ) := by
    exact_mod_cast hC
  linarith

lemma decrease_property
  (KX KY BASE : ℕ)
  (h_base : 1 < BASE)
  (hk : 1 < KX ∧ 1 < KY)
  (x y : ℤ)
  (POINTS : Vector ℤ (KX+KY-1))
  (i : Fin (KX+KY - 1))
  (h_THETA : (tk_P BASE x y) > (tk_THETA BASE KX KY POINTS))
: tk_P BASE
    |(eval_vec_as_poly (tk_split KX KY KX BASE x.natAbs y.natAbs x.natAbs) (POINTS.get i))|
    |(eval_vec_as_poly (tk_split KX KY KY BASE x.natAbs y.natAbs y.natAbs) (POINTS.get i))|
  < tk_P BASE x y := by
  have hPnat : tk_P BASE (x.natAbs : ℤ) (y.natAbs : ℤ) = tk_P BASE x y := by
    simp [tk_P]
  have hmem : POINTS.get i ∈ POINTS := Vector.mem_of_getElem rfl
  have hx := eval_bound_x KX KY BASE h_base hk x.natAbs y.natAbs POINTS (POINTS.get i) hmem
  have hy := eval_bound_y KX KY BASE h_base hk x.natAbs y.natAbs POINTS (POINTS.get i) hmem
  have haux := decrease_property_aux KX KY BASE hk x.natAbs y.natAbs POINTS
      (by rw [hPnat]; exact h_THETA)
  rw [hPnat] at hx hy haux
  set ex := eval_vec_as_poly (tk_split KX KY KX BASE x.natAbs y.natAbs x.natAbs) (POINTS.get i)
      with hex
  set ey := eval_vec_as_poly (tk_split KX KY KY BASE x.natAbs y.natAbs y.natAbs) (POINTS.get i)
      with hey
  have key : tk_P BASE |ex| |ey| = max (digits BASE ex) (digits BASE ey) := by
    rw [tk_P_eq, digits_abs, digits_abs]
  have hxn : digits BASE ex < tk_P BASE x y := by
    have h : ((digits BASE ex : ℕ) : ℚ) < ((tk_P BASE x y : ℕ) : ℚ) := by linarith
    exact_mod_cast h
  have hyn : digits BASE ey < tk_P BASE x y := by
    have h : ((digits BASE ey : ℕ) : ℚ) < ((tk_P BASE x y : ℕ) : ℚ) := by linarith
    exact_mod_cast h
  omega

-- END TERMINATION LEMMAS

/-!
## Auxiliary results for the correctness proof

* `nat_split_sum` / `eval_split_eq` : the limbs of `tk_split` reassemble the original number.
* `vandermonde_inv_mulVec` : Vandermonde interpolation recovers the coefficients.
* `exists_product_coeffs` : the coefficient vector of a product of two polynomials.
* `sign_mul_natAbs` : the sign bookkeeping used by the algorithm.
-/

/-! ### Reassembling a split -/

/-- Base-`B` decomposition: the first `K` limbs of `z` reassemble `z % B ^ K`. -/
lemma nat_split_sum (B : ℕ) (z : ℕ) :
    ∀ K : ℕ, ∑ i ∈ Finset.range K, (z / B ^ i % B) * B ^ i = z % B ^ K := by
  intro K
  induction K with
  | zero => simp [Nat.mod_one]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul]
      ring

/-- Evaluating the `KZ`-limb split of `z` at the split radix returns `z`, provided `z` fits. -/
lemma eval_split_eq (KX KY KZ BASE : ℕ) (x y z : ℕ)
    (hz : z < (tk_B KX KY BASE x y) ^ KZ) :
    eval_vec_as_poly (tk_split KX KY KZ BASE x y z) ((tk_B KX KY BASE x y : ℕ) : ℤ)
      = (z : ℤ) := by
  have hnat := nat_split_sum (tk_B KX KY BASE x y) z KZ
  have key : eval_vec_as_poly (tk_split KX KY KZ BASE x y z) ((tk_B KX KY BASE x y : ℕ) : ℤ)
      = ((∑ i ∈ Finset.range KZ,
            (z / (tk_B KX KY BASE x y) ^ i % (tk_B KX KY BASE x y))
              * (tk_B KX KY BASE x y) ^ i : ℕ) : ℤ) := by
    unfold eval_vec_as_poly tk_split
    simp only [Vector.get_ofFn]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ((z / (tk_B KX KY BASE x y) ^ i % (tk_B KX KY BASE x y) : ℕ) : ℤ)
        * ((tk_B KX KY BASE x y : ℕ) : ℤ) ^ i) KZ]
    push_cast
    ring
  rw [key, hnat, Nat.mod_eq_of_lt hz]

/-- If the ceiling division `⌈d/K⌉` is at most `i`, then `d ≤ i * K`. -/
lemma le_of_ceil_div_le (K : ℕ) (hK : 0 < K) (d i : ℕ)
    (hi : (d + K - 1) / K ≤ i) : d ≤ i * K := by
  have h1 : K * ((d + K - 1) / K) + (d + K - 1) % K = d + K - 1 := Nat.div_add_mod _ _
  have h2 : (d + K - 1) % K < K := Nat.mod_lt _ hK
  obtain ⟨m, hm⟩ : ∃ m, K * ((d + K - 1) / K) = m := ⟨_, rfl⟩
  have h3 : ((d + K - 1) / K) * K = m := by rw [← hm]; ring
  rw [hm] at h1
  have h4 : d ≤ m := by omega
  have h5 : m ≤ i * K := by
    rw [← h3]
    exact Nat.mul_le_mul_right K hi
  omega

/-- `x` fits into `KX` limbs of the split. -/
lemma lt_tk_B_pow_x (KX KY BASE : ℕ) (hb : 1 < BASE) (hKX : 0 < KX) (x y : ℕ) :
    x < (tk_B KX KY BASE x y) ^ KX := by
  have hd : digits BASE (x : ℤ) ≤ (tk_i KX KY BASE x y) * KX :=
    le_of_ceil_div_le KX hKX (digits BASE (x : ℤ)) (tk_i KX KY BASE x y)
      (by unfold tk_i; exact le_max_left _ _)
  have h1 : x < BASE ^ (digits BASE (x : ℤ)) := by
    have := lt_pow_digits hb (x : ℤ)
    simpa using this
  have h2 : BASE ^ (digits BASE (x : ℤ)) ≤ BASE ^ ((tk_i KX KY BASE x y) * KX) :=
    Nat.pow_le_pow_right (by omega) hd
  calc x < BASE ^ (digits BASE (x : ℤ)) := h1
    _ ≤ BASE ^ ((tk_i KX KY BASE x y) * KX) := h2
    _ = (tk_B KX KY BASE x y) ^ KX := by rw [tk_B, ← pow_mul]

/-- `y` fits into `KY` limbs of the split. -/
lemma lt_tk_B_pow_y (KX KY BASE : ℕ) (hb : 1 < BASE) (hKY : 0 < KY) (x y : ℕ) :
    y < (tk_B KX KY BASE x y) ^ KY := by
  have hd : digits BASE (y : ℤ) ≤ (tk_i KX KY BASE x y) * KY :=
    le_of_ceil_div_le KY hKY (digits BASE (y : ℤ)) (tk_i KX KY BASE x y)
      (by unfold tk_i; exact le_max_right _ _)
  have h1 : y < BASE ^ (digits BASE (y : ℤ)) := by
    have := lt_pow_digits hb (y : ℤ)
    simpa using this
  have h2 : BASE ^ (digits BASE (y : ℤ)) ≤ BASE ^ ((tk_i KX KY BASE x y) * KY) :=
    Nat.pow_le_pow_right (by omega) hd
  calc y < BASE ^ (digits BASE (y : ℤ)) := h1
    _ ≤ BASE ^ ((tk_i KX KY BASE x y) * KY) := h2
    _ = (tk_B KX KY BASE x y) ^ KY := by rw [tk_B, ← pow_mul]

/-- Casting an integer polynomial evaluation into `ℚ`. -/
lemma eval_vec_as_poly_cast {K : ℕ} (s : Vector ℕ K) (t : ℤ) :
    ((eval_vec_as_poly s t : ℤ) : ℚ) = ∑ i : Fin K, (s.get i : ℚ) * ((t : ℚ)) ^ (i : ℕ) := by
  unfold eval_vec_as_poly
  push_cast
  rfl

/-! ### Vandermonde interpolation -/

lemma vandermonde_mulVec {N : ℕ} (v : Fin N → ℚ) (c : Fin N → ℚ) :
    (Matrix.vandermonde v).mulVec c = fun i => ∑ j : Fin N, c j * (v i) ^ (j : ℕ) := by
  funext i
  simp [Matrix.mulVec, Matrix.vandermonde, dotProduct, mul_comm]

lemma vandermonde_inv_mulVec {N : ℕ} (v : Fin N → ℚ) (hv : Function.Injective v)
    (c : Fin N → ℚ) :
    (Matrix.vandermonde v)⁻¹.mulVec (fun i => ∑ j : Fin N, c j * (v i) ^ (j : ℕ)) = c := by
  have hdet : (Matrix.vandermonde v).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hv
  rw [← vandermonde_mulVec v c, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

/-! ### Coefficients of a product of polynomials -/

lemma exists_product_coeffs {KX KY : ℕ} (hKX : 0 < KX) (hKY : 0 < KY)
    (p : Fin KX → ℚ) (q : Fin KY → ℚ) :
    ∃ c : Fin (KX + KY - 1) → ℚ, ∀ t : ℚ,
      ∑ j : Fin (KX + KY - 1), c j * t ^ (j : ℕ)
        = (∑ i : Fin KX, p i * t ^ (i : ℕ)) * (∑ i : Fin KY, q i * t ^ (i : ℕ)) := by
  classical
  set P : Polynomial ℚ := ∑ i : Fin KX, Polynomial.C (p i) * Polynomial.X ^ (i : ℕ) with hP
  set Q : Polynomial ℚ := ∑ i : Fin KY, Polynomial.C (q i) * Polynomial.X ^ (i : ℕ) with hQ
  have hdP : P.natDegree ≤ KX - 1 := by
    rw [hP]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    simp only [Polynomial.natDegree_X_pow]
    omega
  have hdQ : Q.natDegree ≤ KY - 1 := by
    rw [hQ]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    simp only [Polynomial.natDegree_X_pow]
    omega
  have hdeg : (P * Q).natDegree < KX + KY - 1 := by
    have := Polynomial.natDegree_mul_le (p := P) (q := Q)
    omega
  refine ⟨fun j => (P * Q).coeff (j : ℕ), fun t => ?_⟩
  have heval := Polynomial.eval_eq_sum_range' hdeg t
  have hPe : Polynomial.eval t P = ∑ i : Fin KX, p i * t ^ (i : ℕ) := by
    rw [hP]
    simp [Polynomial.eval_finsetSum]
  have hQe : Polynomial.eval t Q = ∑ i : Fin KY, q i * t ^ (i : ℕ) := by
    rw [hQ]
    simp [Polynomial.eval_finsetSum]
  rw [Fin.sum_univ_eq_sum_range (fun j => (P * Q).coeff j * t ^ j) (KX + KY - 1),
    ← heval, Polynomial.eval_mul, hPe, hQe]

/-! ### Sign bookkeeping -/

lemma sign_mul_natAbs (a b : ℤ) :
    (if (Xor (a < 0) (b < 0)) then -((a.natAbs : ℚ) * (b.natAbs : ℚ))
      else ((a.natAbs : ℚ) * (b.natAbs : ℚ))) = ((a : ℚ) * (b : ℚ)) := by
  have ha : ((a.natAbs : ℤ)) = if a < 0 then -a else a := by
    split <;> omega
  have hb : ((b.natAbs : ℤ)) = if b < 0 then -b else b := by
    split <;> omega
  have haQ : ((a.natAbs : ℚ)) = if a < 0 then -(a : ℚ) else (a : ℚ) := by
    have : ((a.natAbs : ℤ) : ℚ) = ((if a < 0 then -a else a : ℤ) : ℚ) := by rw [ha]
    push_cast at this
    simpa using this
  have hbQ : ((b.natAbs : ℚ)) = if b < 0 then -(b : ℚ) else (b : ℚ) := by
    have : ((b.natAbs : ℤ) : ℚ) = ((if b < 0 then -b else b : ℤ) : ℚ) := by rw [hb]
    push_cast at this
    simpa using this
  by_cases h1 : a < 0 <;> by_cases h2 : b < 0 <;>
    simp [Xor, h1, h2, haQ, hbQ]

-- ----------------------------------------------------------------------
-- BEGIN RECURSIVE DEFINITION
-- ======== interpolate ========
-- this is an "unsafe" definition, as it doesn't assume injectivity.
-- the algorithm definition below does, and uses that to prove correctness.
noncomputable def interpolate
  (KX KY : ℕ)
  (POINTS_Q : Fin (KX+KY-1) → ℚ)
  (evaluated_pq_pts : Fin (KX+KY - 1) → ℚ)
: Vector ℚ (KX+KY-1) :=
  let VQ := Matrix.vandermonde (R := ℚ) POINTS_Q
  Vector.ofFn ((VQ)⁻¹.mulVec evaluated_pq_pts)

noncomputable def toomk
(BASE KX KY : ℕ)
(h_base : 1 < BASE)
(h_k : 1 < KX ∧ 1 < KY)
(x y : ℤ)
(POINTS : Vector ℤ (KX + KY - 1))
(h_inj : Function.Injective POINTS.get)
: ℚ :=
  if h : (tk_P BASE x y ≤ (tk_THETA BASE KX KY POINTS)) then
    x * y
  else

    let x_abs : ℕ := (x.natAbs)
    let y_abs : ℕ := (y.natAbs)

    let B := tk_B KX KY BASE x_abs y_abs
    let pcoeffs := tk_split KX KY KX BASE x_abs y_abs x_abs
    let qcoeffs := tk_split KX KY KY BASE x_abs y_abs y_abs

    let p_vec := fun i => eval_vec_as_poly pcoeffs (POINTS.get i)
    let q_vec := fun i => eval_vec_as_poly qcoeffs (POINTS.get i)

    let evaluated_pq : Fin (KX + KY - 1) → ℚ :=
      fun i =>
        let a := p_vec i
        let b := q_vec i
        let absprod := toomk BASE KX KY h_base h_k (a.natAbs : ℤ) (b.natAbs : ℤ) POINTS h_inj
        if (Xor (a < 0) (b < 0)) then -absprod else absprod

    let POINTS_Q := fun i => (POINTS.get i : ℚ)
    let r := interpolate KX KY POINTS_Q evaluated_pq
    let absprod := eval_vec_as_poly_Q r B

    if (Xor (x < 0) (y < 0)) then -absprod else absprod
termination_by
  tk_P BASE x y
decreasing_by
  simpa [p_vec, q_vec] using (decrease_property KX KY BASE h_base h_k x y POINTS i (lt_of_not_ge h))

-----------------------------------------------------------
-- CORRECTNESS ARGUMENT
-----------------------------------------------------------
theorem toomk_correctness
(BASE KX KY : ℕ)
(h_base : 1 < BASE)
(h_k : 1 < KX ∧ 1 < KY)
(x y : ℤ)
(POINTS : Vector ℤ (KX + KY - 1))
(h_inj : Function.Injective POINTS.get)
: (toomk BASE KX KY h_base h_k x y POINTS h_inj) = (x * y : ℚ)
:= by
  have hKX := h_k.1
  have hKY := h_k.2
  generalize hn : tk_P BASE x y = n
  induction n using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    rw [toomk]
    split
    · ring
    · rename_i hcon
      simp only []
      set pc := tk_split KX KY KX BASE x.natAbs y.natAbs x.natAbs with hpc
      set qc := tk_split KX KY KY BASE x.natAbs y.natAbs y.natAbs with hqc
      -- the coefficient vector of the product polynomial
      obtain ⟨c, hc⟩ := exists_product_coeffs (KX := KX) (KY := KY) (by omega) (by omega)
        (fun i => (pc.get i : ℚ)) (fun i => (qc.get i : ℚ))
      have hv_inj : Function.Injective (fun i => ((POINTS.get i : ℤ) : ℚ)) := by
        intro i j hij
        simp only at hij
        exact h_inj (by exact_mod_cast hij)
      -- each recursive call returns the product of the two evaluations
      have hpq : ∀ i : Fin (KX + KY - 1),
          (if Xor (eval_vec_as_poly pc (POINTS.get i) < 0)
                   (eval_vec_as_poly qc (POINTS.get i) < 0)
            then -toomk BASE KX KY h_base h_k
                    ((eval_vec_as_poly pc (POINTS.get i)).natAbs : ℤ)
                    ((eval_vec_as_poly qc (POINTS.get i)).natAbs : ℤ) POINTS h_inj
            else toomk BASE KX KY h_base h_k
                    ((eval_vec_as_poly pc (POINTS.get i)).natAbs : ℤ)
                    ((eval_vec_as_poly qc (POINTS.get i)).natAbs : ℤ) POINTS h_inj)
          = ∑ j : Fin (KX + KY - 1), c j * ((POINTS.get i : ℤ) : ℚ) ^ (j : ℕ) := by
        intro i
        have hdec0 := decrease_property KX KY BASE h_base h_k x y POINTS i (not_le.mp hcon)
        rw [← tk_P_natAbs BASE |eval_vec_as_poly pc (POINTS.get i)|
              |eval_vec_as_poly qc (POINTS.get i)|] at hdec0
        simp only [Int.natAbs_abs, hn] at hdec0
        have hrec := ih _ hdec0 ((eval_vec_as_poly pc (POINTS.get i)).natAbs : ℤ)
          ((eval_vec_as_poly qc (POINTS.get i)).natAbs : ℤ) rfl
        rw [hrec, hc ((POINTS.get i : ℤ) : ℚ),
          ← eval_vec_as_poly_cast pc (POINTS.get i), ← eval_vec_as_poly_cast qc (POINTS.get i)]
        simpa using sign_mul_natAbs (eval_vec_as_poly pc (POINTS.get i))
          (eval_vec_as_poly qc (POINTS.get i))
      rw [funext hpq, interpolate]
      rw [vandermonde_inv_mulVec _ hv_inj c]
      -- evaluating the interpolated polynomial at the radix gives the product
      have hBx : eval_vec_as_poly pc ((tk_B KX KY BASE x.natAbs y.natAbs : ℕ) : ℤ)
          = (x.natAbs : ℤ) :=
        eval_split_eq KX KY KX BASE x.natAbs y.natAbs x.natAbs
          (lt_tk_B_pow_x KX KY BASE h_base (by omega) _ _)
      have hBy : eval_vec_as_poly qc ((tk_B KX KY BASE x.natAbs y.natAbs : ℕ) : ℤ)
          = (y.natAbs : ℤ) :=
        eval_split_eq KX KY KY BASE x.natAbs y.natAbs y.natAbs
          (lt_tk_B_pow_y KX KY BASE h_base (by omega) _ _)
      have hprod : eval_vec_as_poly_Q (Vector.ofFn c)
          ((tk_B KX KY BASE x.natAbs y.natAbs : ℕ) : ℚ)
          = (x.natAbs : ℚ) * (y.natAbs : ℚ) := by
        have h1 : eval_vec_as_poly_Q (Vector.ofFn c)
            ((tk_B KX KY BASE x.natAbs y.natAbs : ℕ) : ℚ)
            = ∑ j : Fin (KX + KY - 1), c j
                * (((tk_B KX KY BASE x.natAbs y.natAbs : ℕ) : ℤ) : ℚ) ^ (j : ℕ) := by
          simp [eval_vec_as_poly_Q, Vector.get_ofFn]
        rw [h1, hc, ← eval_vec_as_poly_cast pc, ← eval_vec_as_poly_cast qc, hBx, hBy]
        norm_cast
      rw [hprod]
      exact sign_mul_natAbs x y

end
