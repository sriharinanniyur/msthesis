-- Co-authored by: Fable 5.1

import Mathlib

namespace SSC

open Finset

noncomputable def fft (K : ℕ) (ω : ℂ) (v : Vector ℂ K) : Vector ℂ K :=
  if h : K ≤ 1 then v else Id.run do
    let half := K / 2
    let e : Vector ℂ half := Vector.ofFn fun i => v[2 * i.val]'(by omega)
    let o : Vector ℂ half := Vector.ofFn fun i => v[2 * i.val + 1]'(by omega)
    let e_hat := fft half (ω ^ 2) e
    let o_hat := fft half (ω ^ 2) o
    let mut v_hat : Vector ℂ K := Vector.replicate K 0
    for j in List.finRange half do
      let p := e_hat[j]
      let q := ω ^ j.val * o_hat[j]
      v_hat := v_hat.set j.val (p + q) (by omega)
      v_hat := v_hat.set (j.val + half) (p - q) (by omega)
    return v_hat

def decompose (l K a : ℕ) : Vector ℂ K :=
  Vector.ofFn fun j => (a / 2 ^ (j.val * l) % 2 ^ l : ℕ)

noncomputable def ssc (a b : ℤ) : ℤ :=
  let n := max a.natAbs.size b.natAbs.size
  let l := max (Nat.clog 2 n) 1
  let k := Nat.clog 2 ((2 * n + l - 1) / l)
  let K : ℕ := 2 ^ k
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / K)
  let A := decompose l K a.natAbs
  let B := decompose l K b.natAbs
  let A_hat := fft K ω⁻¹ A
  let B_hat := fft K ω⁻¹ B
  let C := fft K ω (Vector.ofFn fun j => A_hat[j] * B_hat[j])
  a.sign * b.sign * ((∑ j : Fin K, (round (C[j].re / K)).toNat * 2 ^ (j.val * l) : ℕ) : ℤ)

theorem sum_range_two_mul {S : Type*} [AddCommMonoid S] {K m : ℕ} (hK : K = 2 * m) (f : ℕ → S) :
    ∑ j ∈ range K, f j = ∑ j ∈ range m, f (2 * j) + ∑ j ∈ range m, f (2 * j + 1) := by
  subst hK
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    abel

theorem sum_pow_eq_zero_of_pow_eq_neg_one {S : Type*} [CommRing S] {ζ : S} {m : ℕ}
    (hζ : ζ^m = -1) (q : ℕ) : ∑ i ∈ range (2 * m * q), ζ^i = 0 := by
  have h2m : ∑ i ∈ range (2 * m), ζ^i = 0 := by
    rw [two_mul, sum_range_add]
    simp only [pow_add, hζ, neg_one_mul, sum_neg_distrib, add_neg_cancel]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 2 * m * (q + 1) = 2 * m * q + 2 * m by ring, sum_range_add, ih]
    simp only [pow_add, ← mul_sum, h2m, mul_zero, zero_add]

theorem sum_pow_mul_eq {S : Type*} [CommRing S] (k : ℕ) (ω : S)
    (hω : k = 0 ∨ ω^(2^(k - 1)) = -1) (d : ℕ) :
    ∑ i ∈ range (2^k), ω^(i * d) = if 2^k ∣ d then ((2^k : ℕ) : S) else 0 := by
  by_cases hk : k = 0
  · subst hk; simp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hω : ω^(2^k') = -1 := by simpa using hω.resolve_left hk
  have hωK : ω^(2^(k' + 1)) = 1 := by rw [pow_succ, pow_mul, hω]; norm_num
  split_ifs with hd
  · obtain ⟨c, rfl⟩ := hd
    have : ∀ i, ω^(i * (2^(k' + 1) * c)) = 1 := fun i => by
      rw [show i * (2^(k' + 1) * c) = 2^(k' + 1) * (i * c) by ring, pow_mul, hωK, one_pow]
    simp [this]
  · have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero _)
    obtain ⟨s, t, ht, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 2 (by norm_num)
    have hs : s < k' + 1 := by
      by_contra hs
      exact hd (Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) t)
    have hodd : Odd t := by
      rcases Nat.even_or_odd t with h | h
      · exact absurd (even_iff_two_dvd.mp h) ht
      · exact h
    have hζ : (ω^(2^s * t))^(2^(k' - s)) = -1 := by
      rw [← pow_mul, show 2^s * t * 2^(k' - s) = 2^k' * t by
        rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' (by omega)], pow_mul, hω,
        hodd.neg_one_pow]
    have hdvd : 2 * 2^(k' - s) ∣ 2^(k' + 1) := by
      rw [← pow_succ']; exact pow_dvd_pow 2 (by omega)
    obtain ⟨q, hq⟩ := hdvd
    rw [hq]
    have := sum_pow_eq_zero_of_pow_eq_neg_one hζ q
    simp only [← pow_mul] at this
    refine (sum_congr rfl fun i _ => ?_).trans this
    rw [mul_comm]

theorem pow_add_half_mul_even {S : Type*} [CommRing S] (ω : S) (half : ℕ) (hω : ω^half = -1)
    (i j : ℕ) : ω^((i + half) * (2 * j)) = ω^(i * (2 * j)) := by
  rw [add_mul, pow_add, pow_mul ω half, hω, (even_two_mul j).neg_one_pow, mul_one]

theorem pow_add_half_mul_odd {S : Type*} [CommRing S] (ω : S) (half : ℕ) (hω : ω^half = -1)
    (i j : ℕ) : ω^((i + half) * (2 * j + 1)) = -ω^(i * (2 * j + 1)) := by
  rw [add_mul, pow_add, pow_mul ω half, hω, (odd_two_mul_add_one j).neg_one_pow, mul_neg_one]

def vfun {R : Type*} [Zero R] {K : ℕ} (v : Vector R K) : ℕ → R :=
  fun j => if h : j < K then v[j] else 0

theorem vfun_eq {R : Type*} [Zero R] {K : ℕ} (v : Vector R K) (j : ℕ) (hj : j < K) :
    vfun v j = v[j] := by
  simp [vfun, hj]

theorem vfun_ofFn {R : Type*} [Zero R] {K : ℕ} (f : Fin K → R) (j : ℕ) (hj : j < K) :
    vfun (Vector.ofFn f) j = f ⟨j, hj⟩ := by
  simp [vfun, hj]

def butterflyStep {R : Type*} (K half : ℕ) (hK : half + half ≤ K) (P Q : Fin half → R)
    (b : Vector R K) (a : Fin half) : Vector R K :=
  (b.set a.val (P a) (by omega)).set (a.val + half) (Q a) (by omega)

theorem foldl_butterflyStep_of_untouched {R : Type*} (K half : ℕ) (hK : half + half ≤ K)
    (P Q : Fin half → R) (l : List (Fin half)) (init : Vector R K) (i : ℕ) (hi : i < K)
    (h : ∀ a ∈ l, a.val ≠ i ∧ a.val + half ≠ i) :
    (l.foldl (butterflyStep K half hK P Q) init)[i] = init[i] := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, ih _ (fun b hb => h b (List.mem_cons_of_mem a hb))]
    have ha := h a (List.mem_cons_self ..)
    unfold butterflyStep
    rw [Vector.getElem_set, Vector.getElem_set, ite_eq_right ha.1, ite_eq_right ha.2]

theorem foldl_butterflyStep_getElem {R : Type*} (K half : ℕ) (hK : half + half ≤ K)
    (P Q : Fin half → R) (l : List (Fin half)) (init : Vector R K) (j : Fin half) (hj : j ∈ l) :
    (l.foldl (butterflyStep K half hK P Q) init)[j.val]'(by omega) = P j ∧
    (l.foldl (butterflyStep K half hK P Q) init)[j.val + half]'(by omega) = Q j := by
  induction l generalizing init with
  | nil => exact absurd hj (List.not_mem_nil)
  | cons a l ih =>
    rw [List.foldl_cons]
    by_cases hjl : j ∈ l
    · exact ih _ hjl
    · have hja : j = a := by
        rcases List.mem_cons.mp hj with h | h
        · exact h
        · exact absurd h hjl
      subst hja
      have huntouched : ∀ b ∈ l, b.val ≠ j.val ∧ b.val + half ≠ j.val + half := by
        intro b hb
        have : b ≠ j := fun h => hjl (h ▸ hb)
        constructor
        · intro h; exact this (Fin.ext h)
        · intro h; exact this (Fin.ext (by omega))
      have h1 := foldl_butterflyStep_of_untouched K half hK P Q l (butterflyStep K half hK P Q init j)
        j.val (by omega) (fun b hb => ⟨(huntouched b hb).1, by have := (huntouched b hb).1; omega⟩)
      have h2 := foldl_butterflyStep_of_untouched K half hK P Q l (butterflyStep K half hK P Q init j)
        (j.val + half) (by omega) (fun b hb => ⟨by omega, (huntouched b hb).2⟩)
      rw [h1, h2]
      unfold butterflyStep
      rw [Vector.getElem_set, Vector.getElem_set, Vector.getElem_set, Vector.getElem_set,
        ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left rfl]
      exact ⟨rfl, rfl⟩

theorem dvd_iff_add_mod_eq (K m j l : ℕ) (hm : m < K) :
    K ∣ (K - m + j + l) ↔ (j + l) % K = m := by
  rw [← Nat.modEq_zero_iff_dvd]
  have : (j + l) % K = m ↔ j + l ≡ m [MOD K] := by
    unfold Nat.ModEq; rw [Nat.mod_eq_of_lt hm]
  rw [this]
  constructor
  · intro h
    have h' := h.add_right m
    rw [show K - m + j + l + m = j + l + K by omega, zero_add] at h'
    exact Nat.add_modEq_right.symm.trans h'
  · intro h
    have h' := h.add_right (K - m)
    rw [show m + (K - m) = K by omega, show j + l + (K - m) = K - m + j + l by omega] at h'
    exact h'.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)

theorem digits_eq (x K M : ℕ) (hx : x < 2^(K * M)) :
    x = ∑ j ∈ range K, (x / 2^(j * M) % 2^M) * 2^(j * M) := by
  have h : ∀ K, x % 2^(K * M) = ∑ j ∈ range K, (x / 2^(j * M) % 2^M) * 2^(j * M) := by
    intro K
    induction K with
    | zero => simp [Nat.mod_one]
    | succ K ih =>
      rw [sum_range_succ, ← ih, show (K + 1) * M = K * M + M by ring, pow_add, Nat.mod_mul]
      ring
  conv_lhs => rw [← Nat.mod_eq_of_lt hx]
  exact h K

theorem fft_getElem (K : ℕ) (ω : ℂ) (hK : ¬ K ≤ 1) (v : Vector ℂ K) (j : Fin (K / 2)) :
    (fft K ω v)[j.val]'(by omega)
        = (fft (K / 2) (ω ^ 2) (Vector.ofFn fun j => v[2 * j.val]'(by omega)))[j]
          + ω ^ j.val * (fft (K / 2) (ω ^ 2) (Vector.ofFn fun j => v[2 * j.val + 1]'(by omega)))[j] ∧
    (fft K ω v)[j.val + K / 2]'(by omega)
        = (fft (K / 2) (ω ^ 2) (Vector.ofFn fun j => v[2 * j.val]'(by omega)))[j]
          - ω ^ j.val * (fft (K / 2) (ω ^ 2) (Vector.ofFn fun j => v[2 * j.val + 1]'(by omega)))[j] := by
  rw [fft, dite_eq_right hK]
  simp only [bind_pure, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  exact foldl_butterflyStep_getElem K (K / 2) (by omega) _ _ (List.finRange (K / 2))
    (Vector.replicate K 0) j (List.mem_finRange j)

theorem fft_eq :
    ∀ (k K : ℕ) (ω : ℂ), K = 2^k → ∀ (v : Vector ℂ K) (i : ℕ) (hi : i < K),
      (k = 0 ∨ ω^(2^(k - 1)) = -1) →
      (fft K ω v)[i] = ∑ j ∈ range K, ω^(i * j) * vfun v j
  | 0, K, ω, hK, v, i, hi, _ => by
    subst hK
    simp only [pow_zero, Nat.lt_one_iff] at hi
    subst hi
    rw [fft, dite_eq_left (by norm_num)]
    simp [vfun_eq]
  | k + 1, K, ω, hK, v, i, hi, hω => by
    have hω : ω^(2^k) = -1 := by simpa using hω.resolve_left (by omega)
    have hω' : k = 0 ∨ (ω^2)^(2^(k - 1)) = -1 := by
      rcases k with _ | k
      · exact Or.inl rfl
      · right
        rw [← pow_mul, show 2 * 2^(k + 1 - 1) = 2^(k + 1) by rw [Nat.add_sub_cancel, pow_succ]; ring]
        exact hω
    have hK2 : ¬ K ≤ 1 := by rw [hK, pow_succ]; have := Nat.one_le_two_pow (n := k); omega
    have hhalf : K / 2 = 2^k := by rw [hK, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hsub : ∀ w : Vector ℂ (K / 2), ∀ i' (hi' : i' < K / 2),
        (fft (K / 2) (ω^2) w)[i']'hi' = ∑ j ∈ range (K / 2), ω^(i' * (2 * j)) * vfun w j := by
      intro w i' hi'
      rw [fft_eq k (K / 2) (ω^2) hhalf w i' hi' hω']
      refine sum_congr rfl fun j _ => ?_
      rw [← pow_mul]
      congr 1
      ring
    have hK' : K = 2 * (K / 2) := by omega
    by_cases hlt : i < K / 2
    · have h := (fft_getElem K ω hK2 v ⟨i, hlt⟩).1
      simp only [Fin.getElem_fin] at h
      rw [h, hsub _ i hlt, hsub _ i hlt, mul_sum, sum_range_two_mul hK']
      congr 1
      · refine sum_congr rfl fun j hj => ?_
        rw [vfun_ofFn _ _ (mem_range.mp hj), vfun_eq _ _ (by have := mem_range.mp hj; omega)]
      · refine sum_congr rfl fun j hj => ?_
        rw [vfun_ofFn _ _ (mem_range.mp hj), vfun_eq _ _ (by have := mem_range.mp hj; omega),
          ← mul_assoc, ← pow_add]
        congr 2
        ring
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + K / 2 := ⟨i - K / 2, by omega⟩
      have hi' : i' < K / 2 := by omega
      have h := (fft_getElem K ω hK2 v ⟨i', hi'⟩).2
      simp only [Fin.getElem_fin] at h
      rw [h, hsub _ i' hi', hsub _ i' hi', mul_sum, sub_eq_add_neg, ← sum_neg_distrib,
        sum_range_two_mul hK']
      have hω'' : ω^(K / 2) = -1 := by rw [hhalf]; exact hω
      congr 1
      · refine sum_congr rfl fun j hj => ?_
        rw [vfun_ofFn _ _ (mem_range.mp hj),
          vfun_eq _ _ (by have := mem_range.mp hj; omega), pow_add_half_mul_even _ _ hω'']
      · refine sum_congr rfl fun j hj => ?_
        rw [vfun_ofFn _ _ (mem_range.mp hj),
          vfun_eq _ _ (by have := mem_range.mp hj; omega), pow_add_half_mul_odd _ _ hω'',
          ← mul_assoc, ← pow_add, neg_mul]
        congr 3
        ring

theorem fft_mul_fft_inv (k K : ℕ) (ω : ℂ) (hK : K = 2^k) (hωK : ω^K = 1)
    (hω : k = 0 ∨ ω^(2^(k - 1)) = -1) (va vb : Vector ℂ K) (m : ℕ) (hm : m < K) :
    (fft K ω (Vector.ofFn fun i => (fft K ω⁻¹ va)[i] * (fft K ω⁻¹ vb)[i]))[m]
      = (K : ℂ) * ∑ j ∈ range K, ∑ l ∈ range K,
          if (j + l) % K = m then vfun va j * vfun vb l else 0 := by
  have hζ : k = 0 ∨ (ω⁻¹)^(2^(k - 1)) = -1 := by
    rcases hω with h | h
    · exact Or.inl h
    · right; rw [inv_pow, h, inv_neg, inv_one]
  have hωm : ω^m = (ω⁻¹)^(K - m) := by
    rw [inv_pow]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, Nat.add_sub_cancel' hm.le, hωK]
  have hfa : ∀ i (hi : i < K), (fft K ω⁻¹ va)[i] = ∑ j ∈ range K, (ω⁻¹)^(i * j) * vfun va j :=
    fun i hi => fft_eq k K ω⁻¹ hK va i hi hζ
  have hfb : ∀ i (hi : i < K), (fft K ω⁻¹ vb)[i] = ∑ l ∈ range K, (ω⁻¹)^(i * l) * vfun vb l :=
    fun i hi => fft_eq k K ω⁻¹ hK vb i hi hζ
  rw [fft_eq k K ω hK _ m hm hω]
  rw [sum_congr rfl (fun i hi => by
    rw [vfun_ofFn _ _ (mem_range.mp hi)]
    simp only [Fin.getElem_fin]
    rw [hfa i (mem_range.mp hi), hfb i (mem_range.mp hi), pow_mul, hωm, ← pow_mul])]
  subst hK
  generalize ω⁻¹ = ζ at hζ ⊢
  simp_rw [sum_mul_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  calc ∑ i ∈ range (2^k), ζ^((2^k - m) * i) * (ζ^(i * j) * vfun va j * (ζ^(i * l) * vfun vb l))
      = ∑ i ∈ range (2^k), (vfun va j * vfun vb l) * ζ^(i * (2^k - m + j + l)) := by
        refine sum_congr rfl fun i _ => ?_
        ring
    _ = (vfun va j * vfun vb l) * ∑ i ∈ range (2^k), ζ^(i * (2^k - m + j + l)) := by
        rw [mul_sum]
    _ = (2^k : ℕ) * if (j + l) % 2^k = m then vfun va j * vfun vb l else 0 := by
        rw [sum_pow_mul_eq k ζ hζ]
        simp only [dvd_iff_add_mod_eq (2^k) m j l hm]
        split_ifs
        · ring
        · simp

theorem recompose_linear (K l : ℕ) (x y : ℕ → ℕ) (h0 : ∀ j j', K ≤ j + j' → x j * y j' = 0) :
    ∑ m ∈ range K,
        (∑ j ∈ range K, ∑ j' ∈ range K, if j + j' = m then x j * y j' else 0) * 2^(m * l)
      = (∑ j ∈ range K, x j * 2^(j * l)) * (∑ j' ∈ range K, y j' * 2^(j' * l)) := by
  rw [sum_mul_sum]
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j' hj' => ?_
  simp_rw [ite_mul, zero_mul]
  rw [sum_ite_eq]
  split_ifs with h
  · rw [add_mul, pow_add]; ring
  · rw [mul_mul_mul_comm, h0 j j' (by have := mem_range.mp hj; have := mem_range.mp hj'; simp at h; omega),
      zero_mul]

theorem ssc_eq (a b : ℤ) : ssc a b = a * b := by
  unfold ssc
  lift_lets
  extract_lets n l k K ω A B A_hat B_hat C
  have hl : 1 ≤ l := le_max_right _ _
  have hK : K = 2^k := rfl
  have hK0 : 0 < K := by positivity
  have hq : (2 * n + l - 1) / l ≤ K := Nat.le_pow_clog (by norm_num) _
  have h2n : 2 * n ≤ l * ((2 * n + l - 1) / l) := by
    have := Nat.lt_mul_div_succ (2 * n + l - 1) (by omega : 0 < l)
    rw [Nat.mul_succ] at this
    omega
  have hKl : 2 * n ≤ K * l := by
    calc 2 * n ≤ l * ((2 * n + l - 1) / l) := h2n
      _ ≤ l * K := Nat.mul_le_mul_left _ hq
      _ = K * l := mul_comm _ _
  have ha : a.natAbs < 2^n :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hb : b.natAbs < 2^n :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have hωK : ω^K = 1 := by
    simp only [ω]
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hK0.ne')]
    exact Complex.exp_two_pi_mul_I
  have hω : k = 0 ∨ ω^(2^(k - 1)) = -1 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact Or.inl hk
    · right
      simp only [ω]
      rw [← Complex.exp_nat_mul]
      have : ((2^(k - 1) : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (K : ℂ)) = Real.pi * Complex.I := by
        simp only [K]
        push_cast
        rw [show (2 : ℂ)^k = 2^(k - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel hk]]
        field_simp
      rw [this, Complex.exp_pi_mul_I]
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℕ, x = fun j => a.natAbs / 2^(j * l) % 2^l := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℕ, y = fun j => b.natAbs / 2^(j * l) % 2^l := ⟨_, rfl⟩
  have hzero : ∀ j j', K ≤ j + j' → x j * y j' = 0 := by
    intro j j' hjj'
    have hKjj : K * l ≤ (j + j') * l := Nat.mul_le_mul_right l hjj'
    rw [add_mul] at hKjj
    rcases le_or_gt n (j * l) with h | h
    · have : a.natAbs / 2^(j * l) = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) h))
      simp [hx, this]
    rcases le_or_gt n (j' * l) with h' | h'
    · have : b.natAbs / 2^(j' * l) = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) h'))
      simp [hy, this]
    omega
  have hvA : ∀ j (hj : j < K), vfun A j = (x j : ℂ) := by
    intro j hj
    simp only [A, decompose, vfun_ofFn _ _ hj, hx]
  have hvB : ∀ j (hj : j < K), vfun B j = (y j : ℂ) := by
    intro j hj
    simp only [B, decompose, vfun_ofFn _ _ hj, hy]
  have hC : ∀ m (hm : m < K), C[m]
      = (K : ℂ)
        * ((∑ j ∈ range K, ∑ j' ∈ range K, if j + j' = m then x j * y j' else 0 : ℕ) : ℂ) := by
    intro m hm
    simp only [C, A_hat, B_hat]
    rw [fft_mul_fft_inv k K ω hK hωK hω A B m hm]
    push_cast
    congr 1
    refine sum_congr rfl fun j hj => sum_congr rfl fun j' hj' => ?_
    rw [hvA j (mem_range.mp hj), hvB j' (mem_range.mp hj')]
    by_cases hlt : j + j' < K
    · rw [Nat.mod_eq_of_lt hlt]
    · have h0 : ((x j : ℂ)) * (y j' : ℂ) = 0 := by exact_mod_cast hzero j j' (by omega)
      rw [h0]
      simp
  have hround : ∀ m (hm : m < K), (round (C[m].re / (K : ℝ))).toNat
      = ∑ j ∈ range K, ∑ j' ∈ range K, if j + j' = m then x j * y j' else 0 := by
    intro m hm
    rw [hC m hm]
    have : (K : ℂ)
          * ((∑ j ∈ range K, ∑ j' ∈ range K, if j + j' = m then x j * y j' else 0 : ℕ) : ℂ)
        = ((K * ∑ j ∈ range K, ∑ j' ∈ range K, if j + j' = m then x j * y j' else 0 : ℕ)
            : ℂ) := by
      push_cast; ring
    rw [this, Complex.natCast_re, Nat.cast_mul,
      mul_div_cancel_left₀ _ (by exact_mod_cast hK0.ne' : (K : ℝ) ≠ 0), round_natCast,
      Int.toNat_natCast]
  have hsum : (∑ j : Fin K, (round (C[j].re / (K : ℝ))).toNat * 2^(j.val * l))
      = a.natAbs * b.natAbs := by
    rw [Finset.sum_fin_eq_sum_range]
    have hs : ∀ j ∈ range K,
        (if h : j < K then (round (C[(⟨j, h⟩ : Fin K)].re / (K : ℝ))).toNat
            * 2^((⟨j, h⟩ : Fin K).val * l) else 0)
        = (∑ i ∈ range K, ∑ i' ∈ range K, if i + i' = j then x i * y i' else 0) * 2^(j * l) := by
      intro j hj
      rw [dite_eq_left (mem_range.mp hj)]
      simp only [Fin.getElem_fin]
      rw [hround j (mem_range.mp hj)]
    rw [sum_congr rfl hs, recompose_linear K l x y hzero, hx, hy]
    have hKl' : ∀ z : ℕ, z < 2^n → z < 2^(K * l) :=
      fun z hz => lt_of_lt_of_le hz (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [← digits_eq a.natAbs K l (hKl' _ ha), ← digits_eq b.natAbs K l (hKl' _ hb)]
  rw [hsum]
  push_cast
  rw [mul_mul_mul_comm, Int.sign_mul_abs, Int.sign_mul_abs]

end SSC
