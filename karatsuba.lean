-- Co-authored by: Fable 5.1

import Mathlib

theorem karatsuba_coord_lt (D : ℤ) (m : ℕ) (hD : 2 ≤ D) (hDm : D ≤ m) (z : ℤ)
    (hz : z.natAbs ≤ m) :
    (z / D).natAbs < m ∧ (z % D).natAbs < m ∧ (z % D + z / D).natAbs < m := by
  have hD0 : 0 < D := by omega
  have hz' : -(m : ℤ) ≤ z ∧ z ≤ m := by omega
  have hm2 : (2 : ℤ) ≤ m := by omega
  have hzr := Int.emod_add_ediv_mul z D
  have hr0 := Int.emod_nonneg z (by omega : D ≠ 0)
  have hrD := Int.emod_lt_of_pos z hD0
  have hq1 : z / D < m := by
    rw [Int.ediv_lt_iff_lt_mul hD0]; nlinarith
  have hq2 : 1 - m ≤ z / D := by
    rw [Int.le_ediv_iff_mul_le hD0]; nlinarith
  have hq3 : z % D + z / D < m := by
    rcases le_or_gt (z / D) 0 with hq | hq
    · omega
    · have : 0 ≤ (D - 1) * (z / D - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
  omega

theorem karatsuba_calls_lt (β : ℕ) (hβ : 1 < β) (x y : ℤ)
    (h : ¬ (β.digits (max x.natAbs y.natAbs)).length ≤ 1) :
    max (x / ↑(β ^ ((β.digits (max x.natAbs y.natAbs)).length / 2))).natAbs
        (y / ↑(β ^ ((β.digits (max x.natAbs y.natAbs)).length / 2))).natAbs
      < max x.natAbs y.natAbs ∧
    max (x % ↑(β ^ ((β.digits (max x.natAbs y.natAbs)).length / 2))).natAbs
        (y % ↑(β ^ ((β.digits (max x.natAbs y.natAbs)).length / 2))).natAbs
      < max x.natAbs y.natAbs ∧
    max (x % ↑(β ^ ((β.digits (max x.natAbs y.natAbs)).length / 2))
          + x / ↑(β ^ ((β.digits (max x.natAbs y.natAbs)).length / 2))).natAbs
        (y % ↑(β ^ ((β.digits (max x.natAbs y.natAbs)).length / 2))
          + y / ↑(β ^ ((β.digits (max x.natAbs y.natAbs)).length / 2))).natAbs
      < max x.natAbs y.natAbs := by
  have hm0 : max x.natAbs y.natAbs ≠ 0 := by
    rintro h0; rw [h0] at h; simp at h
  have hlog := Nat.length_digits β _ hβ hm0
  have hd1 : (2 : ℤ) ≤ ↑(β ^ ((β.digits (max x.natAbs y.natAbs)).length / 2)) := by
    norm_cast
    calc 2 ≤ β := hβ
      _ = β ^ 1 := (pow_one β).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hdm : (↑(β ^ ((β.digits (max x.natAbs y.natAbs)).length / 2)) : ℤ)
      ≤ max x.natAbs y.natAbs := by
    norm_cast
    calc _ ≤ β ^ Nat.log β (max x.natAbs y.natAbs) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := Nat.pow_log_le_self β hm0
  have hx := karatsuba_coord_lt _ _ hd1 hdm x (le_max_left _ _)
  have hy := karatsuba_coord_lt _ _ hd1 hdm y (le_max_right _ _)
  exact ⟨max_lt hx.1 hy.1, max_lt hx.2.1 hy.2.1, max_lt hx.2.2 hy.2.2⟩

def karatsuba (β : ℕ) (hβ : 1 < β) (x y : ℤ) : ℤ :=
  let n := (β.digits (max x.natAbs y.natAbs)).length
  if n ≤ 1 then x * y
  else
    let k := n / 2
    let β' := β ^ k
    let x1 := x / β'
    let x0 := x % β'
    let y1 := y / β'
    let y0 := y % β'
    let c1 := karatsuba β hβ x1 y1
    let c0 := karatsuba β hβ x0 y0
    let c2 := karatsuba β hβ (x0 + x1) (y0 + y1)
    c1 * (β' ^ 2) + (c2 - c1 - c0) * β' + c0
termination_by max x.natAbs y.natAbs
decreasing_by
  all_goals rename_i h
  · exact (karatsuba_calls_lt β hβ x y h).1
  · exact (karatsuba_calls_lt β hβ x y h).2.1
  · exact (karatsuba_calls_lt β hβ x y h).2.2

theorem karatsuba_eq (β : ℕ) (hβ : 1 < β) (x y : ℤ) : karatsuba β hβ x y = x * y := by
  refine karatsuba.induct β hβ (fun x y => karatsuba β hβ x y = x * y) ?_ ?_ x y
  · intro x y n h
    rw [karatsuba, ite_eq_left h]
  · intro x y n h k β' x1 x0 y1 y0 ih1 ih0 ih2
    rw [karatsuba, ite_eq_right h]
    show karatsuba β hβ x1 y1 * (β' : ℤ) ^ 2
        + (karatsuba β hβ (x0 + x1) (y0 + y1) - karatsuba β hβ x1 y1 - karatsuba β hβ x0 y0)
          * β'
        + karatsuba β hβ x0 y0 = x * y
    have hx : x0 + x1 * β' = x := Int.emod_add_ediv_mul x β'
    have hy : y0 + y1 * β' = y := Int.emod_add_ediv_mul y β'
    rw [ih1, ih0, ih2, ← hx, ← hy]
    ring
