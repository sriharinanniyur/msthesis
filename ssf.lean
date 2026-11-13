-- Co-authored by: Fable 5.1

import Mathlib

namespace SSF

def mulPow2 (N t : ℕ) (x : ZMod (2^N + 1)) : ZMod (2^N + 1) :=
  (((BitVec.ofNat (2 * N) x.val).rotateLeft t).toNat : ℕ)

def mulPow2Inv (N t : ℕ) (x : ZMod (2^N + 1)) : ZMod (2^N + 1) :=
  (((BitVec.ofNat (2 * N) x.val).rotateRight t).toNat : ℕ)

def fft (N K ω : ℕ) (u : Vector (ZMod (2^N + 1)) K) : Vector (ZMod (2^N + 1)) K :=
  if h : K ≤ 1 then u else Id.run do
    let half := K / 2
    let e : Vector (ZMod (2^N + 1)) half := Vector.ofFn fun j => u[2 * j.val]'(by omega)
    let o : Vector (ZMod (2^N + 1)) half := Vector.ofFn fun j => u[2 * j.val + 1]'(by omega)
    let ê := fft N half (2 * ω) e
    let ô := fft N half (2 * ω) o
    let mut û : Vector (ZMod (2^N + 1)) K := Vector.replicate K 0
    for j in List.finRange half do
      let p := ê[j]
      let q := mulPow2 N (j.val * ω) ô[j]
      û := û.set j.val (p + q) (by omega)
      û := û.set (j.val + half) (p - q) (by omega)
    return û
termination_by K
decreasing_by all_goals omega

def ifft (N k ω : ℕ) (u : Vector (ZMod (2^N + 1)) (2^k)) : Vector (ZMod (2^N + 1)) (2^k) :=
  Vector.ofFn fun j => mulPow2Inv N k (fft N (2^k) (2 * N - ω) u)[j]

def SuitableN' (n k M n' : ℕ) : Prop :=
  2 * M + k ≤ n' ∧ 2^k ∣ n' ∧ n' < n

def SuitableKM (n k M : ℕ) : Prop :=
  n = 2^k * M ∧ ∃ n', SuitableN' n k M n'

def good_n (n : ℕ) : Prop :=
  ∃ k M, SuitableKM n k M

theorem SuitableN'.two_le {n k M n' : ℕ} (hKM : n = 2^k * M) (h : SuitableN' n k M n') :
    2 ≤ k := by
  obtain ⟨h1, -, h3⟩ := h
  by_contra hk
  interval_cases k <;> simp at hKM <;> omega

theorem good_n_of_four_dvd (n : ℕ) (hn : 4 ∣ n) (h12 : 12 ≤ n) : good_n n := by
  obtain ⟨M, rfl⟩ := hn
  exact ⟨2, M, by norm_num, 4 * ((M + 2) / 2), by omega, ⟨(M + 2) / 2, by norm_num⟩, by omega⟩

theorem good_n_next {n k M n' : ℕ} (h16 : 16 < n) (hKM : n = 2^k * M) (hn' : SuitableN' n k M n') :
    good_n n' := by
  have hk := hn'.two_le hKM
  obtain ⟨h1, h2, h3⟩ := hn'
  have h4 : 4 ∣ n' := by
    have : 2^2 ∣ 2^k := pow_dvd_pow 2 hk
    norm_num at this
    exact this.trans h2
  have h12 : 12 ≤ n' := by
    by_contra hlt
    have hk3 : k ≤ 3 := by
      by_contra hk3
      have : 2^4 ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.le_of_dvd (by omega) h2
      omega
    interval_cases k <;> norm_num at hKM h2 <;> omega
  exact good_n_of_four_dvd n' h4 h12

structure Params (n : ℕ) where
  k : ℕ
  M : ℕ
  n' : ℕ
  hKM : n = 2^k * M
  hn' : SuitableN' n k M n'

def ssf (sel : ∀ n, good_n n → Params n) (n : ℕ) (hn : good_n n) (a b : ZMod (2^n + 1)) :
    ZMod (2^n + 1) :=
  if a.val = 2^n then -b else
  if b.val = 2^n then -a else
  if h16 : n ≤ 16 then a * b else
    let ⟨k, M, n', hKM, hn'⟩ := sel n hn
    let K := 2^k
    let av : Vector (ZMod (2^n' + 1)) K := Vector.ofFn fun j => ((a.val / 2^(j.val * M)) % 2^M : ℕ)
    let bv : Vector (ZMod (2^n' + 1)) K := Vector.ofFn fun j => ((b.val / 2^(j.val * M)) % 2^M : ℕ)
    let ψ := n' / K
    let ω := 2 * ψ
    let a' : Vector (ZMod (2^n' + 1)) K := Vector.ofFn fun j => mulPow2 n' (j.val * ψ) av[j]
    let b' : Vector (ZMod (2^n' + 1)) K := Vector.ofFn fun j => mulPow2 n' (j.val * ψ) bv[j]
    let A' := fft n' K ω a'
    let B' := fft n' K ω b'
    let C' : Vector (ZMod (2^n' + 1)) K :=
      Vector.ofFn fun j => ssf sel n' (good_n_next (by omega) hKM hn') A'[j] B'[j]
    let c' : Vector (ZMod (2^n' + 1)) K := ifft n' k ω C'
    let cv : Vector (ZMod (2^n' + 1)) K := Vector.ofFn fun j => mulPow2Inv n' (j.val * ψ) c'[j]
    let cℤ : Vector ℤ K := Vector.ofFn fun j =>
      if cv[j].val ≥ (j.val + 1) * 2^(2 * M) then cv[j].val - (2^n' + 1) else cv[j].val
    ((∑ j : Fin K, cℤ[j] * 2^(j.val * M) : ℤ) : ZMod (2^n + 1))
termination_by n
decreasing_by
  exact hn'.2.2

noncomputable def choose (n : ℕ) (hn : good_n n) : Params n :=
  let k := Classical.choose hn
  let M := Classical.choose (Classical.choose_spec hn)
  have hKM : SuitableKM n k M := Classical.choose_spec (Classical.choose_spec hn)
  ⟨k, M, Classical.choose hKM.2, hKM.1, Classical.choose_spec hKM.2⟩

open Finset

theorem two_pow_eq_neg_one (N : ℕ) : (2 : ZMod (2^N + 1))^N = -1 := by
  have h : ((2^N + 1 : ℕ) : ZMod (2^N + 1)) = 0 := ZMod.natCast_self _
  push_cast at h
  linear_combination h

theorem two_pow_two_mul_eq_one (N : ℕ) : (2 : ZMod (2^N + 1))^(2 * N) = 1 := by
  rw [pow_mul', two_pow_eq_neg_one]; norm_num

theorem rotate_toNat_eq (w s V : ℕ) (hV : V < 2^w) (hs : s ≤ w) :
    (V * 2^s + V / 2^(w - s)) % 2^w = 2^s * (V % 2^(w - s)) + V / 2^(w - s) := by
  have hq : V / 2^(w - s) < 2^s := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hs]; exact hV
  have hρ : V % 2^(w - s) < 2^(w - s) := Nat.mod_lt _ (by positivity)
  have hY : 2^s * (V % 2^(w - s)) + V / 2^(w - s) < 2^w := by
    calc 2^s * (V % 2^(w - s)) + V / 2^(w - s) < 2^s * (V % 2^(w - s)) + 2^s := by omega
      _ = 2^s * (V % 2^(w - s) + 1) := by ring
      _ ≤ 2^s * 2^(w - s) := Nat.mul_le_mul_left _ hρ
      _ = 2^w := by rw [← pow_add, Nat.add_sub_cancel' hs]
  have h2w : 2^(w - s) * 2^s = 2^w := by rw [← pow_add, Nat.sub_add_cancel hs]
  have hdecomp := Nat.div_add_mod V (2^(w - s))
  set q := V / 2^(w - s)
  set ρ := V % 2^(w - s)
  rw [← hdecomp, show (2^(w - s) * q + ρ) * 2^s + q = 2^(w - s) * 2^s * q + (2^s * ρ + q) by ring,
    h2w, Nat.mul_add_mod, Nat.mod_eq_of_lt hY]

theorem val_lt_two_pow_two_mul (N : ℕ) (hN : 0 < N) (x : ZMod (2^N + 1)) :
    x.val < 2^(2 * N) := by
  have := ZMod.val_lt x
  have : 2^N < 2^(2 * N) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem mulPow2_eq (N t : ℕ) (hN : 0 < N) (x : ZMod (2^N + 1)) :
    mulPow2 N t x = 2^t * x := by
  have h22N := two_pow_two_mul_eq_one N
  have hV := val_lt_two_pow_two_mul N hN x
  have hs : t % (2 * N) < 2 * N := Nat.mod_lt _ (by omega)
  have hred : (2 : ZMod (2^N + 1))^t = 2^(t % (2 * N)) := by
    conv_lhs => rw [← Nat.mod_add_div t (2 * N), pow_add, pow_mul, h22N, one_pow, mul_one]
  unfold mulPow2
  rw [BitVec.toNat_rotateLeft_eq_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV,
    rotate_toNat_eq _ _ _ hV hs.le, hred]
  push_cast
  conv_rhs => rw [← ZMod.natCast_zmod_val x, ← Nat.div_add_mod x.val (2^(2 * N - t % (2 * N)))]
  push_cast
  have h1 : (2 : ZMod (2^N + 1))^(t % (2 * N)) * 2^(2 * N - t % (2 * N)) = 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hs.le, h22N]
  linear_combination -((x.val / 2^(2 * N - t % (2 * N)) : ℕ) : ZMod (2^N + 1)) * h1

theorem mulPow2Inv_eq (N t : ℕ) (hN : 0 < N) (ht : t ≤ 2 * N) (x : ZMod (2^N + 1)) :
    mulPow2Inv N t x = 2^(2 * N - t) * x := by
  have h22N := two_pow_two_mul_eq_one N
  have hV := val_lt_two_pow_two_mul N hN x
  have hs : t % (2 * N) < 2 * N := Nat.mod_lt _ (by omega)
  have key := rotate_toNat_eq (2 * N) (2 * N - t % (2 * N)) x.val hV (Nat.sub_le _ _)
  rw [Nat.sub_sub_self hs.le] at key
  unfold mulPow2Inv
  rw [BitVec.toNat_rotateRight_eq_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV,
    Nat.add_comm (x.val / 2^(t % (2 * N))), key]
  push_cast
  conv_rhs => rw [← ZMod.natCast_zmod_val x, ← Nat.div_add_mod x.val (2^(t % (2 * N)))]
  push_cast
  have h1 : (2 : ZMod (2^N + 1))^(2 * N - t % (2 * N)) * 2^(t % (2 * N)) = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hs.le, h22N]
  have h2 : (2 : ZMod (2^N + 1))^(2 * N - t) = 2^(2 * N - t % (2 * N)) := by
    rcases Nat.lt_or_eq_of_le ht with h | h
    · rw [Nat.mod_eq_of_lt h]
    · subst h; rw [Nat.mod_self, Nat.sub_self, Nat.sub_zero, pow_zero, h22N]
  rw [h2]
  linear_combination -((x.val / 2^(t % (2 * N)) : ℕ) : ZMod (2^N + 1)) * h1

theorem mulPow2_spec (N s : ℕ) (hN : 0 < N) (hs : s ≤ N) (x : ZMod (2^N + 1)) :
    mulPow2 N s x
      = (((x.val <<< s) % 2^N : ℕ) : ZMod (2^N + 1))
        - ((x.val >>> (N - s) : ℕ) : ZMod (2^N + 1)) := by
  rw [mulPow2_eq N s hN x, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hdecomp := Nat.div_add_mod x.val (2^(N - s))
  have hr : x.val % 2^(N - s) < 2^(N - s) := Nat.mod_lt _ (by positivity)
  have hpow : 2^(N - s) * 2^s = 2^N := by rw [← pow_add, Nat.sub_add_cancel hs]
  set q := x.val / 2^(N - s)
  set r := x.val % 2^(N - s)
  have hmod : x.val * 2^s % 2^N = r * 2^s := by
    rw [← hdecomp, show (2^(N - s) * q + r) * 2^s = 2^N * q + r * 2^s by rw [← hpow]; ring,
      Nat.mul_add_mod, Nat.mod_eq_of_lt]
    calc r * 2^s < 2^(N - s) * 2^s := Nat.mul_lt_mul_of_pos_right hr (by positivity)
      _ = 2^N := hpow
  rw [hmod]
  conv_lhs => rw [← ZMod.natCast_zmod_val x, ← hdecomp]
  push_cast
  have h : (2 : ZMod (2^N + 1))^s * 2^(N - s) = -1 := by
    rw [← pow_add, Nat.add_sub_cancel' hs, two_pow_eq_neg_one]
  linear_combination (q : ZMod (2^N + 1)) * h

theorem mulPow2_add_N (N t : ℕ) (hN : 0 < N) (x : ZMod (2^N + 1)) :
    mulPow2 N (t + N) x = -mulPow2 N t x := by
  rw [mulPow2_eq N _ hN, mulPow2_eq N _ hN, pow_add, two_pow_eq_neg_one]
  ring

theorem mulPow2_mod (N t : ℕ) (x : ZMod (2^N + 1)) :
    mulPow2 N (t % (2 * N)) x = mulPow2 N t x := by
  unfold mulPow2
  rw [BitVec.rotateLeft_mod_eq_rotateLeft]

theorem mulPow2Inv_eq_mulPow2 (N t : ℕ) (hN : 0 < N) (ht : t ≤ 2 * N) (x : ZMod (2^N + 1)) :
    mulPow2Inv N t x = mulPow2 N (2 * N - t) x := by
  rw [mulPow2Inv_eq N t hN ht x, mulPow2_eq N _ hN]

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

theorem fft_getElem (N K ω : ℕ) (hK : ¬ K ≤ 1) (v : Vector (ZMod (2^N + 1)) K) (j : Fin (K / 2)) :
    (fft N K ω v)[j.val]'(by omega)
        = (fft N (K / 2) (2 * ω) (Vector.ofFn fun j => v[2 * j.val]'(by omega)))[j]
          + mulPow2 N (j.val * ω)
              (fft N (K / 2) (2 * ω) (Vector.ofFn fun j => v[2 * j.val + 1]'(by omega)))[j] ∧
    (fft N K ω v)[j.val + K / 2]'(by omega)
        = (fft N (K / 2) (2 * ω) (Vector.ofFn fun j => v[2 * j.val]'(by omega)))[j]
          - mulPow2 N (j.val * ω)
              (fft N (K / 2) (2 * ω) (Vector.ofFn fun j => v[2 * j.val + 1]'(by omega)))[j] := by
  rw [fft, dite_eq_right hK]
  simp only [bind_pure, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  exact foldl_butterflyStep_getElem K (K / 2) (by omega) _ _ (List.finRange (K / 2))
    (Vector.replicate K 0) j (List.mem_finRange j)

theorem fft_eq (N : ℕ) (hN : 0 < N) :
    ∀ (k K ω : ℕ), K = 2^k → ∀ (v : Vector (ZMod (2^N + 1)) K) (i : ℕ) (hi : i < K),
      (k = 0 ∨ ((2 : ZMod (2^N + 1))^ω)^(2^(k - 1)) = -1) →
      (fft N K ω v)[i] = ∑ j ∈ range K, ((2 : ZMod (2^N + 1))^ω)^(i * j) * vfun v j
  | 0, K, ω, hK, v, i, hi, _ => by
    subst hK
    simp only [pow_zero, Nat.lt_one_iff] at hi
    subst hi
    rw [fft, dite_eq_left (by norm_num)]
    simp [vfun_eq]
  | k + 1, K, ω, hK, v, i, hi, hω => by
    have hω : ((2 : ZMod (2^N + 1))^ω)^(2^k) = -1 := by
      simpa using hω.resolve_left (by omega)
    have hω' : k = 0 ∨ ((2 : ZMod (2^N + 1))^(2 * ω))^(2^(k - 1)) = -1 := by
      rcases k with _ | k
      · exact Or.inl rfl
      · right
        rw [← pow_mul, show 2 * ω * 2^(k + 1 - 1) = ω * 2^(k + 1) by
          rw [Nat.add_sub_cancel, pow_succ]; ring, pow_mul]
        exact hω
    have hK2 : ¬ K ≤ 1 := by rw [hK, pow_succ]; have := Nat.one_le_two_pow (n := k); omega
    have hhalf : K / 2 = 2^k := by rw [hK, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hsub : ∀ w : Vector (ZMod (2^N + 1)) (K / 2), ∀ i' (hi' : i' < K / 2),
        (fft N (K / 2) (2 * ω) w)[i']'hi'
          = ∑ j ∈ range (K / 2), ((2 : ZMod (2^N + 1))^ω)^(i' * (2 * j)) * vfun w j := by
      intro w i' hi'
      rw [fft_eq N hN k (K / 2) (2 * ω) hhalf w i' hi' hω']
      refine sum_congr rfl fun j _ => ?_
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    have hK' : K = 2 * (K / 2) := by omega
    by_cases hlt : i < K / 2
    ·
      have h := (fft_getElem N K ω hK2 v ⟨i, hlt⟩).1
      simp only [Fin.getElem_fin] at h
      rw [h, hsub _ i hlt, hsub _ i hlt, mulPow2_eq N _ hN, mul_sum]
      rw [sum_range_two_mul hK']
      congr 1
      · refine sum_congr rfl fun j hj => ?_
        rw [vfun_ofFn _ _ (mem_range.mp hj), vfun_eq _ _ (by have := mem_range.mp hj; omega)]
      · refine sum_congr rfl fun j hj => ?_
        rw [vfun_ofFn _ _ (mem_range.mp hj), vfun_eq _ _ (by have := mem_range.mp hj; omega),
          ← mul_assoc, show i * ω = ω * i by ring, pow_mul, ← pow_add]
        congr 2
        ring
    ·
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + K / 2 := ⟨i - K / 2, by omega⟩
      have hi' : i' < K / 2 := by omega
      have h := (fft_getElem N K ω hK2 v ⟨i', hi'⟩).2
      simp only [Fin.getElem_fin] at h
      rw [h, hsub _ i' hi', hsub _ i' hi', mulPow2_eq N _ hN, mul_sum, sub_eq_add_neg,
        ← sum_neg_distrib]
      rw [sum_range_two_mul hK']
      have hω'' : ((2 : ZMod (2^N + 1))^ω)^(K / 2) = -1 := by rw [hhalf]; exact hω
      congr 1
      · refine sum_congr rfl fun j hj => ?_
        rw [vfun_ofFn _ _ (mem_range.mp hj),
          vfun_eq _ _ (by have := mem_range.mp hj; omega), pow_add_half_mul_even _ _ hω'']
      · refine sum_congr rfl fun j hj => ?_
        rw [vfun_ofFn _ _ (mem_range.mp hj),
          vfun_eq _ _ (by have := mem_range.mp hj; omega), pow_add_half_mul_odd _ _ hω'',
          ← mul_assoc, show i' * ω = ω * i' by ring, pow_mul, ← pow_add, neg_mul]
        congr 3
        ring

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

theorem ifft_fft_mul_fft (N k ω : ℕ) (hN : 0 < N) (hk : 1 ≤ k) (hkN : k ≤ 2 * N)
    (he : ω ≤ 2 * N) (hω : ((2 : ZMod (2^N + 1))^ω)^(2^(k - 1)) = -1)
    (va vb : Vector (ZMod (2^N + 1)) (2^k)) (m : ℕ) (hm : m < 2^k) :
    (ifft N k ω (Vector.ofFn fun i => (fft N (2^k) ω va)[i] * (fft N (2^k) ω vb)[i]))[m]
      = ∑ j ∈ range (2^k), ∑ l ∈ range (2^k),
          if (j + l) % 2^k = m then vfun va j * vfun vb l else 0 := by
  have hωω' : (2 : ZMod (2^N + 1))^(2 * N - ω) * 2^ω = 1 := by
    rw [← pow_add, Nat.sub_add_cancel he, two_pow_two_mul_eq_one]
  have hωK : ((2 : ZMod (2^N + 1))^ω)^(2^k) = 1 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hω
    rw [pow_succ, pow_mul, hω]; norm_num
  have hω'm : ((2 : ZMod (2^N + 1))^(2 * N - ω))^m = ((2 : ZMod (2^N + 1))^ω)^(2^k - m) := by
    apply left_inv_eq_right_inv (a := ((2 : ZMod (2^N + 1))^ω)^m)
    · rw [← mul_pow, hωω', one_pow]
    · rw [← pow_add, Nat.add_sub_cancel' hm.le, hωK]
  have hω'' : k = 0 ∨ ((2 : ZMod (2^N + 1))^(2 * N - ω))^(2^(k - 1)) = -1 := by
    right
    have h1 : ((2 : ZMod (2^N + 1))^(2 * N - ω))^(2^(k - 1)) * ((2 : ZMod (2^N + 1))^ω)^(2^(k - 1))
        = 1 := by rw [← mul_pow, hωω', one_pow]
    rw [hω] at h1
    linear_combination -h1
  have hfa : ∀ i (hi : i < 2^k), (fft N (2^k) ω va)[i]
      = ∑ j ∈ range (2^k), ((2 : ZMod (2^N + 1))^ω)^(i * j) * vfun va j :=
    fun i hi => fft_eq N hN k (2^k) ω rfl va i hi (Or.inr hω)
  have hfb : ∀ i (hi : i < 2^k), (fft N (2^k) ω vb)[i]
      = ∑ l ∈ range (2^k), ((2 : ZMod (2^N + 1))^ω)^(i * l) * vfun vb l :=
    fun i hi => fft_eq N hN k (2^k) ω rfl vb i hi (Or.inr hω)
  unfold ifft
  rw [Vector.getElem_ofFn]
  simp only [Fin.getElem_fin]
  rw [mulPow2Inv_eq N _ hN hkN, fft_eq N hN k (2^k) (2 * N - ω) rfl _ m hm hω'']
  rw [sum_congr rfl (fun i hi => by
    rw [vfun_ofFn _ _ (mem_range.mp hi)]
    rw [hfa i (mem_range.mp hi), hfb i (mem_range.mp hi),
      pow_mul ((2 : ZMod (2^N + 1))^(2 * N - ω)) m i, hω'm, ← pow_mul])]
  generalize (2 : ZMod (2^N + 1))^ω = ζ at hω hωK ⊢
  simp_rw [sum_mul_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  calc ∑ i ∈ range (2^k),
          2^(2 * N - k) * (ζ^((2^k - m) * i) * (ζ^(i * j) * vfun va j * (ζ^(i * l) * vfun vb l)))
      = ∑ i ∈ range (2^k),
          (vfun va j * vfun vb l * 2^(2 * N - k)) * ζ^(i * (2^k - m + j + l)) := by
        refine sum_congr rfl fun i _ => ?_
        ring
    _ = (vfun va j * vfun vb l * 2^(2 * N - k))
          * ∑ i ∈ range (2^k), ζ^(i * (2^k - m + j + l)) := by
        rw [mul_sum]
    _ = if (j + l) % 2^k = m then vfun va j * vfun vb l else 0 := by
        rw [sum_pow_mul_eq k ζ (Or.inr hω)]
        simp only [dvd_iff_add_mod_eq (2^k) m j l hm]
        split_ifs
        · push_cast
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hkN, two_pow_two_mul_eq_one, mul_one]
        · rw [mul_zero]

def convPos (K : ℕ) (x y : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ j ∈ range K, ∑ l ∈ range K, if j + l = m then x j * y l else 0

def convNeg (K : ℕ) (x y : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ j ∈ range K, ∑ l ∈ range K, if j + l = m + K then x j * y l else 0

theorem untwist (N k ψ : ℕ) (hN : 0 < N) (hψ : 2^k * ψ = N) (x y : ℕ → ℕ) (m : ℕ)
    (hm : m < 2^k) :
    mulPow2Inv N (m * ψ) (∑ j ∈ range (2^k), ∑ l ∈ range (2^k),
        if (j + l) % 2^k = m then
          mulPow2 N (j * ψ) (x j : ZMod (2^N + 1)) * mulPow2 N (l * ψ) (y l : ZMod (2^N + 1))
        else 0)
      = (convPos (2^k) x y m : ZMod (2^N + 1)) - (convNeg (2^k) x y m : ZMod (2^N + 1)) := by
  have hmψ : m * ψ ≤ 2 * N := by
    calc m * ψ ≤ 2^k * ψ := Nat.mul_le_mul_right _ hm.le
      _ = N := hψ
      _ ≤ 2 * N := by omega
  unfold convPos convNeg
  rw [mulPow2Inv_eq N _ hN hmψ, mul_sum]
  push_cast
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun l hl => ?_
  rw [mulPow2_eq N _ hN, mulPow2_eq N _ hN]
  have hj := mem_range.mp hj
  have hl := mem_range.mp hl
  by_cases h1 : j + l = m
  · have hmod : (j + l) % 2^k = m := by rw [h1, Nat.mod_eq_of_lt hm]
    rw [ite_eq_left hmod, ite_eq_left h1, ite_eq_right (by omega)]
    have : (2 : ZMod (2^N + 1))^(2 * N - m * ψ) * (2^(j * ψ) * 2^(l * ψ)) = 1 := by
      rw [← pow_add, ← pow_add, show 2 * N - m * ψ + (j * ψ + l * ψ) = 2 * N by
        rw [← add_mul, h1]; omega, two_pow_two_mul_eq_one]
    linear_combination ((x j : ZMod (2^N + 1)) * (y l : ZMod (2^N + 1))) * this
  · by_cases h2 : j + l = m + 2^k
    · have hmod : (j + l) % 2^k = m := by rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hm]
      rw [ite_eq_left hmod, ite_eq_right h1, ite_eq_left h2]
      have : (2 : ZMod (2^N + 1))^(2 * N - m * ψ) * (2^(j * ψ) * 2^(l * ψ)) = -1 := by
        rw [← pow_add, ← pow_add, show 2 * N - m * ψ + (j * ψ + l * ψ) = 2 * N + N by
          rw [← add_mul, h2, add_mul, hψ]; omega, pow_add, two_pow_two_mul_eq_one,
          two_pow_eq_neg_one, one_mul]
      linear_combination ((x j : ZMod (2^N + 1)) * (y l : ZMod (2^N + 1))) * this
    · have hmod : (j + l) % 2^k ≠ m := by
        intro hmod
        by_cases hlt : j + l < 2^k
        · rw [Nat.mod_eq_of_lt hlt] at hmod; exact h1 hmod
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; omega
      rw [ite_eq_right hmod, ite_eq_right h1, ite_eq_right h2]
      simp

theorem sum_ite_add_eq {S : Type*} [AddCommMonoid S] (K j m : ℕ) (hm : m < K) (f : ℕ → S) :
    ∑ l ∈ range K, (if j + l = m then f l else 0) = if j ≤ m then f (m - j) else 0 := by
  split_ifs with hj
  · rw [sum_eq_single (m - j)]
    · rw [ite_eq_left (by omega)]
    · intro l _ hl; rw [ite_eq_right (by omega)]
    · intro h; exact absurd (mem_range.mpr (by omega)) h
  · exact sum_eq_zero fun l _ => ite_eq_right (by omega)

theorem sum_ite_add_eq' {S : Type*} [AddCommMonoid S] (K j m : ℕ) (hj : j < K) (f : ℕ → S) :
    ∑ l ∈ range K, (if j + l = m + K then f l else 0) = if m < j then f (m + K - j) else 0 := by
  split_ifs with hj
  · rw [sum_eq_single (m + K - j)]
    · rw [ite_eq_left (by omega)]
    · intro l _ hl; rw [ite_eq_right (by omega)]
    · intro h; exact absurd (mem_range.mpr (by omega)) h
  · exact sum_eq_zero fun l hl => ite_eq_right (by have := mem_range.mp hl; omega)

theorem convPos_lt (K M m : ℕ) (x y : ℕ → ℕ) (hx : ∀ j, x j < 2^M) (hy : ∀ l, y l < 2^M)
    (hm : m < K) : convPos K x y m < (m + 1) * 2^(2 * M) := by
  unfold convPos
  simp_rw [sum_ite_add_eq K _ m hm]
  rw [← sum_filter, show (range K).filter (fun j => j ≤ m) = range (m + 1) by
    ext j; simp only [mem_filter, mem_range]; omega]
  calc ∑ j ∈ range (m + 1), x j * y (m - j)
      < ∑ j ∈ range (m + 1), 2^(2 * M) := by
        apply sum_lt_sum_of_nonempty ⟨0, by simp⟩
        intro j _
        rw [two_mul, pow_add]
        exact Nat.mul_lt_mul'' (hx j) (hy (m - j))
    _ = (m + 1) * 2^(2 * M) := by rw [sum_const, card_range, smul_eq_mul]

theorem convNeg_le (K M m : ℕ) (x y : ℕ → ℕ) (hx : ∀ j, x j < 2^M) (hy : ∀ l, y l < 2^M)
    (hm : m < K) : convNeg K x y m ≤ (K - 1 - m) * 2^(2 * M) := by
  unfold convNeg
  rw [sum_congr rfl fun j hj => sum_ite_add_eq' K j m (mem_range.mp hj) _]
  rw [← sum_filter, show (range K).filter (fun j => m < j) = Ico (m + 1) K by
    ext j; simp only [mem_filter, mem_range, mem_Ico]; omega]
  calc ∑ j ∈ Ico (m + 1) K, x j * y (m + K - j)
      ≤ ∑ j ∈ Ico (m + 1) K, 2^(2 * M) := by
        apply sum_le_sum
        intro j _
        rw [two_mul, pow_add]
        exact (Nat.mul_lt_mul'' (hx j) (hy (m + K - j))).le
    _ = (K - 1 - m) * 2^(2 * M) := by
        rw [sum_const, Nat.card_Ico, smul_eq_mul]; congr 1; omega

theorem unwrap (N K M k m : ℕ) (hK : K = 2^k) (hN : 2 * M + k ≤ N) (hm : m < K) (P Q : ℕ)
    (hP : P < (m + 1) * 2^(2 * M)) (hQ : Q ≤ (K - 1 - m) * 2^(2 * M))
    (x : ZMod (2^N + 1)) (hx : x = (P : ZMod (2^N + 1)) - (Q : ZMod (2^N + 1))) :
    (if x.val ≥ (m + 1) * 2^(2 * M) then (x.val : ℤ) - (2^N + 1) else (x.val : ℤ))
      = (P : ℤ) - (Q : ℤ) := by
  have hKT : K * 2^(2 * M) ≤ 2^N := by
    rw [hK, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : (m + 1) * 2^(2 * M) + (K - 1 - m) * 2^(2 * M) = K * 2^(2 * M) := by
    rw [← add_mul]; congr 1; omega
  have hmod : ((2^N + 1 : ℕ) : ZMod (2^N + 1)) = 0 := ZMod.natCast_self _
  rcases le_or_gt Q P with hQP | hQP
  · have hx' : x = ((P - Q : ℕ) : ZMod (2^N + 1)) := by rw [hx, Nat.cast_sub hQP]
    have hval : x.val = P - Q := by
      rw [hx']; exact ZMod.val_natCast_of_lt (by omega)
    rw [hval, ite_eq_right (by omega), Nat.cast_sub hQP]
  · have hx' : x = ((2^N + 1 - (Q - P) : ℕ) : ZMod (2^N + 1)) := by
      rw [hx, Nat.cast_sub (by omega), hmod, Nat.cast_sub hQP.le]; ring
    have hval : x.val = 2^N + 1 - (Q - P) := by
      rw [hx']; exact ZMod.val_natCast_of_lt (by omega)
    rw [hval, ite_eq_left (by omega), Nat.cast_sub (by omega : Q - P ≤ 2^N + 1),
      Nat.cast_sub hQP.le]
    push_cast
    ring

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

theorem recompose (n K M k : ℕ) (hK : K = 2^k) (hn : n = K * M) (x y : ℕ → ℕ) :
    ((∑ m ∈ range K, ((convPos K x y m : ℤ) - (convNeg K x y m : ℤ)) * 2^(m * M) : ℤ)
        : ZMod (2^n + 1))
      = ((∑ j ∈ range K, x j * 2^(j * M) : ℕ) : ZMod (2^n + 1))
        * ((∑ l ∈ range K, y l * 2^(l * M) : ℕ) : ZMod (2^n + 1)) := by
  have h2n : (2 : ZMod (2^n + 1))^(K * M) = -1 := by rw [← hn]; exact two_pow_eq_neg_one n
  unfold convPos convNeg
  push_cast
  rw [sum_mul_sum]
  simp_rw [sub_mul, sum_mul, ← sum_sub_distrib]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [sum_comm]
  refine sum_congr rfl fun l hl => ?_
  have hj := mem_range.mp hj
  have hl := mem_range.mp hl
  simp_rw [ite_mul, zero_mul]
  rw [sum_sub_distrib, sum_ite_eq]
  by_cases hjl : j + l < K
  · rw [ite_eq_left (mem_range.mpr hjl), sum_eq_zero (fun m _ => ite_eq_right (by omega)),
      sub_zero, add_mul, pow_add]
    ring
  · rw [ite_eq_right (fun h => hjl (mem_range.mp h)), zero_sub]
    simp_rw [show ∀ m, (j + l = m + K) ↔ (j + l - K = m) from fun m => by omega]
    rw [sum_ite_eq, ite_eq_left (mem_range.mpr (by omega))]
    have : (2 : ZMod (2^n + 1))^(j * M) * 2^(l * M) = -(2^((j + l - K) * M)) := by
      rw [← pow_add, ← add_mul, show (j + l) * M = (j + l - K) * M + K * M by
        rw [← add_mul]; congr 1; omega, pow_add, h2n]
      ring
    linear_combination -((x j : ZMod (2^n + 1)) * (y l : ZMod (2^n + 1))) * this

theorem ssf_eq (sel : ∀ n, good_n n → Params n) (n : ℕ) (hn : good_n n) (a b : ZMod (2^n + 1)) :
    ssf sel n hn a b = a * b := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  rw [ssf]
  split_ifs with ha hb h16
  · have : a = -1 := by
      rw [← ZMod.natCast_zmod_val a, ha]; push_cast; exact two_pow_eq_neg_one n
    rw [this]; ring
  · have : b = -1 := by
      rw [← ZMod.natCast_zmod_val b, hb]; push_cast; exact two_pow_eq_neg_one n
    rw [this]; ring
  · rfl
  · obtain ⟨k, M, n', hnKM, hn'⟩ := sel n hn
    dsimp -zeta only
    lift_lets
    extract_lets K av bv ψ ω a' b' A' B' C' c' cv cℤ
    have hMk : 2 * M + k ≤ n' := hn'.1
    have hdvd : 2^k ∣ n' := hn'.2.1
    have hlt : n' < n := hn'.2.2
    have hk : 1 ≤ k := by have := hn'.two_le hnKM; omega
    have hN : 0 < n' := by omega
    have hψ : 2^k * ψ = n' := Nat.mul_div_cancel' hdvd
    have he : ω ≤ 2 * n' := by
      have := Nat.div_le_self n' (2^k)
      simp only [ω, ψ, K]; omega
    have hkN : k ≤ 2 * n' := by omega
    have hω : ((2 : ZMod (2^n' + 1))^ω)^(2^(k - 1)) = -1 := by
      rw [← pow_mul, show ω * 2^(k - 1) = n' by
        simp only [ω]
        rw [mul_comm 2 ψ, mul_assoc, ← pow_succ', Nat.sub_add_cancel hk, mul_comm, hψ]]
      exact two_pow_eq_neg_one n'
    have hA : ∀ j, a.val / 2^(j * M) % 2^M < 2^M := fun j => Nat.mod_lt _ (by positivity)
    have hB : ∀ j, b.val / 2^(j * M) % 2^M < 2^M := fun j => Nat.mod_lt _ (by positivity)
    have ha' : a.val < 2^(2^k * M) := by
      rw [← hnKM]; have := ZMod.val_lt a; omega
    have hb' : b.val < 2^(2^k * M) := by
      rw [← hnKM]; have := ZMod.val_lt b; omega
    have hva' : ∀ j (hj : j < 2^k), vfun a' j
        = mulPow2 n' (j * ψ) ((a.val / 2^(j * M) % 2^M : ℕ) : ZMod (2^n' + 1)) := by
      intro j hj
      simp only [a', av, vfun_ofFn _ _ hj, Vector.getElem_ofFn, Fin.getElem_fin]
    have hvb' : ∀ j (hj : j < 2^k), vfun b' j
        = mulPow2 n' (j * ψ) ((b.val / 2^(j * M) % 2^M : ℕ) : ZMod (2^n' + 1)) := by
      intro j hj
      simp only [b', bv, vfun_ofFn _ _ hj, Vector.getElem_ofFn, Fin.getElem_fin]
    have hC' : C' = Vector.ofFn fun j => A'[j] * B'[j] := by
      simp only [C', IH n' hlt]
    have hcv : ∀ j (hj : j < 2^k), cv[j]
        = (convPos (2^k) (fun j => a.val / 2^(j * M) % 2^M) (fun j => b.val / 2^(j * M) % 2^M) j
            : ZMod (2^n' + 1))
          - (convNeg (2^k) (fun j => a.val / 2^(j * M) % 2^M) (fun j => b.val / 2^(j * M) % 2^M) j
            : ZMod (2^n' + 1)) := by
      intro j hj
      simp only [cv, Vector.getElem_ofFn, Fin.getElem_fin, c', hC', A', B', K]
      have key := ifft_fft_mul_fft n' k ω hN hk hkN he hω a' b' j hj
      simp only [Fin.getElem_fin] at key
      rw [key]
      rw [sum_congr rfl fun j hj => sum_congr rfl fun l hl => by
        rw [hva' j (mem_range.mp hj), hvb' l (mem_range.mp hl)]]
      exact untwist n' k ψ hN hψ _ _ j hj
    have hcℤ : ∀ j (hj : j < 2^k), cℤ[j]
        = (convPos (2^k) (fun j => a.val / 2^(j * M) % 2^M) (fun j => b.val / 2^(j * M) % 2^M) j : ℤ)
          - (convNeg (2^k) (fun j => a.val / 2^(j * M) % 2^M) (fun j => b.val / 2^(j * M) % 2^M) j
            : ℤ) := by
      intro j hj
      simp only [cℤ, Vector.getElem_ofFn, Fin.getElem_fin]
      exact unwrap n' (2^k) M k j rfl hMk hj _ _
        (convPos_lt (2^k) M j _ _ hA hB hj) (convNeg_le (2^k) M j _ _ hA hB hj) _ (hcv j hj)
    rw [Finset.sum_fin_eq_sum_range]
    have hsum : ∀ j ∈ range K,
        (if h : j < K then cℤ[(⟨j, h⟩ : Fin K)] * 2^((⟨j, h⟩ : Fin K).val * M) else 0)
        = ((convPos (2^k) (fun j => a.val / 2^(j * M) % 2^M) (fun j => b.val / 2^(j * M) % 2^M) j : ℤ)
            - (convNeg (2^k) (fun j => a.val / 2^(j * M) % 2^M) (fun j => b.val / 2^(j * M) % 2^M) j
              : ℤ)) * 2^(j * M) := by
      intro j hj
      rw [dite_eq_left (mem_range.mp hj)]
      simp only [Fin.getElem_fin]
      rw [hcℤ j (mem_range.mp hj)]
    rw [sum_congr rfl hsum]
    rw [recompose n (2^k) M k rfl hnKM, ← digits_eq a.val (2^k) M ha',
      ← digits_eq b.val (2^k) M hb', ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem ssf_choose_eq (n : ℕ) (hn : good_n n) (a b : ZMod (2^n + 1)) :
    ssf choose n hn a b = a * b :=
  ssf_eq choose n hn a b

end SSF
