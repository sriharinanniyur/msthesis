-- Co-authored by: Fable 5.1

import Mathlib

theorem karatsuba_bv_coord_lt (D m z : ℕ) (hD : 2 ≤ D) (hDm : D ≤ m) (hz : z ≤ m) :
    z / D < m ∧ z % D < m ∧ z % D + z / D < m := by
  have h1 := Nat.div_add_mod z D
  have h2 := Nat.mod_lt z (by omega : D > 0)
  rcases Nat.eq_zero_or_pos (z / D) with h0 | hpos
  · omega
  · have h3 : 2 * (z / D) ≤ D * (z / D) := Nat.mul_le_mul_right _ hD
    omega

theorem karatsuba_bv_split (w : ℕ) (x y : BitVec w)
    (h : ¬ (Nat.digits 2 (max x.toNat y.toNat)).length ≤ 1) :
    2 ≤ 2^((Nat.digits 2 (max x.toNat y.toNat)).length / 2) ∧
    2^((Nat.digits 2 (max x.toNat y.toNat)).length / 2) ≤ max x.toNat y.toNat := by
  have hm0 : max x.toNat y.toNat ≠ 0 := by
    rintro h0; rw [h0] at h; simp at h
  have hlog := Nat.length_digits 2 _ (by norm_num) hm0
  constructor
  · calc 2 = 2^1 := (pow_one 2).symm
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  · calc _ ≤ 2^Nat.log 2 (max x.toNat y.toNat) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ _ := Nat.pow_log_le_self 2 hm0

theorem toNat_high (w k : ℕ) (x : BitVec w) : (x.extractLsb' k (w - k)).toNat = x.toNat / 2^k := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem toNat_low (w k : ℕ) (x : BitVec w) : (x.extractLsb' 0 k).toNat = x.toNat % 2^k := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

theorem toNat_sum (w k : ℕ) (x : BitVec w) :
    ((x.extractLsb' 0 k).setWidth w + (x.extractLsb' k (w - k)).setWidth w).toNat
      = (x.toNat % 2^k + x.toNat / 2^k) % 2^w := by
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth, toNat_high, toNat_low,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) x.isLt),
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)]

theorem karatsuba_bv_calls_lt (w : ℕ) (x y : BitVec w)
    (h : ¬ (Nat.digits 2 (max x.toNat y.toNat)).length ≤ 1) :
    max (x.extractLsb' ((Nat.digits 2 (max x.toNat y.toNat)).length / 2)
          (w - (Nat.digits 2 (max x.toNat y.toNat)).length / 2)).toNat
        (y.extractLsb' ((Nat.digits 2 (max x.toNat y.toNat)).length / 2)
          (w - (Nat.digits 2 (max x.toNat y.toNat)).length / 2)).toNat
      < max x.toNat y.toNat ∧
    max (x.extractLsb' 0 ((Nat.digits 2 (max x.toNat y.toNat)).length / 2)).toNat
        (y.extractLsb' 0 ((Nat.digits 2 (max x.toNat y.toNat)).length / 2)).toNat
      < max x.toNat y.toNat ∧
    max ((x.extractLsb' 0 ((Nat.digits 2 (max x.toNat y.toNat)).length / 2)).setWidth w
          + (x.extractLsb' ((Nat.digits 2 (max x.toNat y.toNat)).length / 2)
              (w - (Nat.digits 2 (max x.toNat y.toNat)).length / 2)).setWidth w).toNat
        ((y.extractLsb' 0 ((Nat.digits 2 (max x.toNat y.toNat)).length / 2)).setWidth w
          + (y.extractLsb' ((Nat.digits 2 (max x.toNat y.toNat)).length / 2)
              (w - (Nat.digits 2 (max x.toNat y.toNat)).length / 2)).setWidth w).toNat
      < max x.toNat y.toNat := by
  have hs := karatsuba_bv_split w x y h
  set m := max x.toNat y.toNat
  set k := (Nat.digits 2 m).length / 2
  have hx := karatsuba_bv_coord_lt _ _ x.toNat hs.1 hs.2 (le_max_left _ _)
  have hy := karatsuba_bv_coord_lt _ _ y.toNat hs.1 hs.2 (le_max_right _ _)
  have hmw : m < 2^w := max_lt x.isLt y.isLt
  rw [toNat_high, toNat_high, toNat_low, toNat_low, toNat_sum, toNat_sum,
    Nat.mod_eq_of_lt (a := x.toNat % 2^k + x.toNat / 2^k) (by omega),
    Nat.mod_eq_of_lt (a := y.toNat % 2^k + y.toNat / 2^k) (by omega)]
  exact ⟨max_lt hx.1 hy.1, max_lt hx.2.1 hy.2.1, max_lt hx.2.2 hy.2.2⟩

def karatsuba_bv (w : ℕ) (x y : BitVec w) : BitVec (2 * w) :=
  let n := (Nat.digits 2 (max x.toNat y.toNat)).length
  if n ≤ 1 then x.setWidth (2 * w) * y.setWidth (2 * w)
  else
    let k := n / 2
    let x1 := x.extractLsb' k (w - k)
    let x0 := x.extractLsb' 0 k
    let y1 := y.extractLsb' k (w - k)
    let y0 := y.extractLsb' 0 k
    let c1 := karatsuba_bv (w - k) x1 y1
    let c0 := karatsuba_bv k x0 y0
    let c2 := karatsuba_bv
      w
      (x0.setWidth w + x1.setWidth w)
      (y0.setWidth w + y1.setWidth w)
    c1.setWidth (2 * w) <<< (2 * k)
      + (c2 - c1.setWidth (2 * w) - c0.setWidth (2 * w)) <<< k
      + c0.setWidth (2 * w)
termination_by max x.toNat y.toNat
decreasing_by
  all_goals rename_i h
  · exact (karatsuba_bv_calls_lt w x y h).1
  · exact (karatsuba_bv_calls_lt w x y h).2.1
  · exact (karatsuba_bv_calls_lt w x y h).2.2

theorem castNat_toNat_add (w : ℕ) (a b : BitVec w) :
    (((a + b).toNat : ℕ) : ZMod (2^w)) = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, ZMod.natCast_mod]; push_cast; rfl

theorem castNat_toNat_sub (w : ℕ) (a b : BitVec w) :
    (((a - b).toNat : ℕ) : ZMod (2^w)) = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub b.isLt.le,
    ZMod.natCast_self]
  ring

theorem castNat_toNat_shiftLeft (w : ℕ) (a : BitVec w) (s : ℕ) :
    (((a <<< s).toNat : ℕ) : ZMod (2^w)) = a.toNat * 2^s := by
  rw [BitVec.toNat_shiftLeft, ZMod.natCast_mod, Nat.shiftLeft_eq]; push_cast; rfl

theorem castNat_toNat_setWidth (v w : ℕ) (a : BitVec v) :
    (((a.setWidth w).toNat : ℕ) : ZMod (2^w)) = a.toNat := by
  rw [BitVec.toNat_setWidth, ZMod.natCast_mod]

theorem karatsuba_bv_eq (w : ℕ) (x y : BitVec w) :
    (karatsuba_bv w x y).toNat = x.toNat * y.toNat := by
  have hprod : ∀ w (x y : BitVec w), x.toNat * y.toNat < 2^(2 * w) := fun w x y => by
    rw [two_mul, pow_add]; exact Nat.mul_lt_mul'' x.isLt y.isLt
  have hw2 : ∀ w (x : BitVec w), x.toNat < 2^(2 * w) := fun w x =>
    lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine karatsuba_bv.induct (fun w x y => (karatsuba_bv w x y).toNat = x.toNat * y.toNat)
    ?_ ?_ w x y
  · intro w x y n h
    rw [karatsuba_bv, ite_eq_left h, BitVec.toNat_mul, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (hw2 w x), Nat.mod_eq_of_lt (hw2 w y),
      Nat.mod_eq_of_lt (hprod w x y)]
  · intro w x y n h k x1 x0 y1 y0 ih1 ih0 ih2
    rw [karatsuba_bv, ite_eq_right h]
    show ((karatsuba_bv (w - k) x1 y1).setWidth (2 * w) <<< (2 * k)
        + (karatsuba_bv w (x0.setWidth w + x1.setWidth w) (y0.setWidth w + y1.setWidth w)
            - (karatsuba_bv (w - k) x1 y1).setWidth (2 * w)
            - (karatsuba_bv k x0 y0).setWidth (2 * w)) <<< k
        + (karatsuba_bv k x0 y0).setWidth (2 * w)).toNat = x.toNat * y.toNat
    have hs := karatsuba_bv_split w x y h
    have hbx := karatsuba_bv_coord_lt (2^k) _ x.toNat hs.1 hs.2 (le_max_left _ _)
    have hby := karatsuba_bv_coord_lt (2^k) _ y.toNat hs.1 hs.2 (le_max_right _ _)
    have hmw : max x.toNat y.toNat < 2^w := max_lt x.isLt y.isLt
    have hsx : (x0.setWidth w + x1.setWidth w).toNat = x0.toNat + x1.toNat := by
      simp only [x0, x1]
      rw [toNat_sum, toNat_high, toNat_low]
      exact Nat.mod_eq_of_lt (by omega)
    have hsy : (y0.setWidth w + y1.setWidth w).toNat = y0.toNat + y1.toNat := by
      simp only [y0, y1]
      rw [toNat_sum, toNat_high, toNat_low]
      exact Nat.mod_eq_of_lt (by omega)
    have hx : x.toNat = x0.toNat + x1.toNat * 2^k := by
      simp only [x0, x1]
      rw [toNat_high, toNat_low, mul_comm, Nat.mod_add_div]
    have hy : y.toNat = y0.toNat + y1.toNat * 2^k := by
      simp only [y0, y1]
      rw [toNat_high, toNat_low, mul_comm, Nat.mod_add_div]
    have key : ((((karatsuba_bv (w - k) x1 y1).setWidth (2 * w) <<< (2 * k)
        + (karatsuba_bv w (x0.setWidth w + x1.setWidth w) (y0.setWidth w + y1.setWidth w)
            - (karatsuba_bv (w - k) x1 y1).setWidth (2 * w)
            - (karatsuba_bv k x0 y0).setWidth (2 * w)) <<< k
        + (karatsuba_bv k x0 y0).setWidth (2 * w)).toNat : ℕ) : ZMod (2^(2 * w)))
        = ((x.toNat * y.toNat : ℕ) : ZMod (2^(2 * w))) := by
      rw [castNat_toNat_add, castNat_toNat_add, castNat_toNat_shiftLeft, castNat_toNat_shiftLeft,
        castNat_toNat_sub, castNat_toNat_sub, castNat_toNat_setWidth, castNat_toNat_setWidth,
        ih1, ih0, ih2, hsx, hsy, hx, hy]
      push_cast
      ring
    rw [ZMod.natCast_eq_natCast_iff'] at key
    rwa [Nat.mod_eq_of_lt (BitVec.isLt _), Nat.mod_eq_of_lt (hprod w x y)] at key
