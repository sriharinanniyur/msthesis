-- Co-authored by: Fable 5.1

def ks_improved (β m : Nat) (W : Array Nat) : Array Nat := Id.run do
  let n := W.size - m
  let x := W.extract 0 m
  let mut W := W
  for j in [0:m] do
    W := W.set! j 0
  for i in [0:n] do
    let yi := W[m + i]!
    let mut c := 0
    for j in [0:m] do
      let k := i + j
      let t := x[j]! * yi + W[k]! + c
      W := W.set! k (t % β)
      c := t / β
    W := W.set! (i + m) c
  return W

#eval ks_improved 10 2 #[4, 3, 2, 1]

def ofDigits (β : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + β * ofDigits β ds

@[simp] theorem ofDigits_nil (β : Nat) : ofDigits β [] = 0 := rfl
@[simp] theorem ofDigits_cons (β d : Nat) (ds : List Nat) :
    ofDigits β (d :: ds) = d + β * ofDigits β ds := rfl

theorem ofDigits_append (β : Nat) (l₁ l₂ : List Nat) :
    ofDigits β (l₁ ++ l₂) = ofDigits β l₁ + β ^ l₁.length * ofDigits β l₂ := by
  induction l₁ with
  | nil => simp
  | cons d ds ih =>
    simp [ih, Nat.pow_succ, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc, Nat.mul_left_comm]

def innerStep (β : Nat) (x : Array Nat) (yi i : Nat) (s : Array Nat × Nat) (j : Nat) :
    Array Nat × Nat :=
  let t := x[j]! * yi + s.1[i + j]! + s.2
  (s.1.setIfInBounds (i + j) (t % β), t / β)

def outerStep (β m : Nat) (x : Array Nat) (w : Array Nat) (i : Nat) : Array Nat :=
  let r := List.foldl (innerStep β x (w[m + i]!) i) (w, 0) (List.range' 0 m)
  r.1.setIfInBounds (i + m) r.2

theorem ks_improved_eq (β m : Nat) (W : Array Nat) :
    ks_improved β m W =
      List.foldl (outerStep β m (W.extract 0 m))
        (List.foldl (fun b a => b.setIfInBounds a 0) W (List.range' 0 m))
        (List.range' 0 (W.size - m)) := by
  simp [ks_improved]
  rfl

theorem foldl_range'_inv {α : Type} (P : Nat → α → Prop) (f : α → Nat → α) (n : Nat) (init : α)
    (h0 : P 0 init) (hstep : ∀ i a, i < n → P i a → P (i + 1) (f a i)) :
    P n (List.foldl f init (List.range' 0 n)) := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    exact hstep n _ (by omega) (ih (fun i a hi => hstep i a (by omega)))

theorem carry_lt {β a b d c : Nat} (ha : a < β) (hb : b < β) (hd : d < β) (hc : c < β) :
    (a * b + d + c) / β < β := by
  have hβ : 0 < β := by omega
  rw [Nat.div_lt_iff_lt_mul hβ]
  have h1 : a * b ≤ (β - 1) * (β - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (β - 1) * (β - 1) + (β - 1) + (β - 1) + 1 = β * β := by
    cases β with
    | zero => omega
    | succ b => simp [Nat.succ_mul, Nat.mul_succ]; omega
  omega

section
variable (β m : Nat) (L₀ : List Nat)

def OuterInv (x : Nat) (i : Nat) (w : Array Nat) : Prop :=
  w.toList.length = L₀.length ∧
  (∀ d ∈ w.toList, d < β) ∧
  w.toList.drop (m + i) = L₀.drop (m + i) ∧
  ofDigits β (w.toList.take (m + i)) = x * ofDigits β ((L₀.drop m).take i)

def InnerInv (X : List Nat) (A : Array Nat) (yi i : Nat) (j : Nat) (s : Array Nat × Nat) : Prop :=
  s.1.toList.length = L₀.length ∧
  (∀ d ∈ s.1.toList, d < β) ∧
  s.2 < β ∧
  s.1.toList.drop (i + j) = A.toList.drop (i + j) ∧
  ofDigits β (s.1.toList.take (i + j)) +
      β ^ (i + j) * (s.2 + ofDigits β ((A.toList.drop (i + j)).take (m - j))) =
    ofDigits β (A.toList.take (m + i)) + β ^ i * yi * ofDigits β (X.take j)

end

theorem inner_step (β m : Nat) (L₀ X : List Nat) (x : Array Nat) (A : Array Nat) (yi i : Nat)
    (hβ : 2 ≤ β) (hx : x.toList = X) (hXlen : X.length = m) (hXlt : ∀ d ∈ X, d < β)
    (hyi : yi < β) (hAlen : A.toList.length = L₀.length)
    (hi : i + m < L₀.length)
    (j : Nat) (hj : j < m) (s : Array Nat × Nat)
    (h : InnerInv β m L₀ X A yi i j s) :
    InnerInv β m L₀ X A yi i (j + 1) (innerStep β x yi i s j) := by
  obtain ⟨hlen, hlt, hc, hdrop, hval⟩ := h
  obtain ⟨w, c⟩ := s
  simp only at hlen hlt hc hdrop hval

  have hk : i + j < w.toList.length := by omega
  have hkA : i + j < A.toList.length := by omega
  have hjX : j < X.length := by omega
  have hwk : w[i + j]! = w.toList[i + j] := by
    rw [← Array.getElem!_toList, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  have hxj : x[j]! = X[j] := by
    rw [← Array.getElem!_toList, hx, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hjX]; rfl
  have hwA : w.toList[i + j] = A.toList[i + j] := by
    have h0 : (List.drop (i + j) w.toList)[0]? = (List.drop (i + j) A.toList)[0]? := by rw [hdrop]
    rw [List.getElem?_drop, List.getElem?_drop, Nat.add_zero,
      List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hkA] at h0
    exact Option.some.inj h0
  have hxj_lt : X[j] < β := hXlt _ (List.getElem_mem hjX)
  have hwk_lt : w.toList[i + j] < β := hlt _ (List.getElem_mem hk)
  simp only [innerStep, hwk, hxj]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hlen]
  · intro d hd
    simp only [Array.toList_setIfInBounds] at hd
    rcases List.mem_or_eq_of_mem_set hd with h' | h'
    · exact hlt d h'
    · rw [h']; exact Nat.mod_lt _ (by omega)
  · exact carry_lt hxj_lt hyi hwk_lt hc
  · simp only [Array.toList_setIfInBounds]
    rw [List.drop_set_of_lt (by omega)]
    have := congrArg (List.drop 1) hdrop
    simp only [List.drop_drop] at this
    exact this
  · simp only [Array.toList_setIfInBounds, ← Nat.add_assoc]
    rw [hwA]
    have h3 : (A.toList.drop (i + j)).take (m - j)
        = A.toList[i + j] :: (A.toList.drop (i + j + 1)).take (m - (j + 1)) := by
      rw [List.drop_eq_getElem_cons hkA]
      have : m - j = (m - (j + 1)) + 1 := by omega
      rw [this, List.take_succ_cons]
    rw [h3] at hval
    have h2 : X.take (j + 1) = X.take j ++ [X[j]] := List.take_succ_eq_append_getElem hjX
    have h1 : ∀ v, (w.toList.set (i + j) v).take (i + j + 1) = w.toList.take (i + j) ++ [v] := by
      intro v
      rw [List.take_succ_eq_append_getElem (by simp; omega), List.getElem_set_self,
        List.take_set_of_le (Nat.le_refl _)]
    rw [h1, h2, ofDigits_append, ofDigits_append, List.length_take_of_le (by omega),
      List.length_take_of_le (by omega)]
    simp only [ofDigits_cons, ofDigits_nil, Nat.mul_zero, Nat.add_zero, Nat.pow_succ]
    simp only [ofDigits_cons] at hval
    generalize A.toList[i + j] = a at hval ⊢
    generalize X[j] = xj at hval ⊢
    generalize ofDigits β (List.take (i + j) w.toList) = S at hval ⊢
    generalize ofDigits β (List.take (m - (j + 1)) (List.drop (i + j + 1) A.toList)) = R at hval ⊢
    generalize ofDigits β (List.take (m + i) A.toList) = T at hval ⊢
    generalize ofDigits β (List.take j X) = Q at hval ⊢
    have hdm : β * ((xj * yi + a + c) / β) + (xj * yi + a + c) % β = xj * yi + a + c :=
      Nat.div_add_mod _ _
    have e1 : β ^ (i + j) * β * ((xj * yi + a + c) / β + R)
        = β ^ (i + j) * (β * ((xj * yi + a + c) / β)) + β ^ (i + j) * β * R := by
      rw [Nat.mul_add, Nat.mul_assoc]
    have e2 : β ^ (i + j) * (xj * yi + a + c)
        = β ^ (i + j) * (xj * yi) + β ^ (i + j) * a + β ^ (i + j) * c := by
      rw [Nat.mul_add, Nat.mul_add]
    have e3 : β ^ (i + j) * (c + (a + β * R))
        = β ^ (i + j) * c + β ^ (i + j) * a + β ^ (i + j) * β * R := by
      rw [Nat.mul_add, Nat.mul_add]; ac_rfl
    have e4 : β ^ i * yi * (Q + β ^ j * xj) = β ^ i * yi * Q + β ^ (i + j) * (xj * yi) := by
      rw [Nat.mul_add, Nat.pow_add]; ac_rfl
    have hP : β ^ (i + j) * ((xj * yi + a + c) % β) + β ^ (i + j) * (β * ((xj * yi + a + c) / β))
        = β ^ (i + j) * (xj * yi + a + c) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega

theorem getElem_of_drop_eq {l₁ l₂ : List Nat} {k : Nat} (h : l₁.drop k = l₂.drop k)
    (h₁ : k < l₁.length) (h₂ : k < l₂.length) : l₁[k] = l₂[k] := by
  have h0 : (l₁.drop k)[0]? = (l₂.drop k)[0]? := by rw [h]
  rw [List.getElem?_drop, List.getElem?_drop, Nat.add_zero,
    List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at h0
  exact Option.some.inj h0

theorem outer_step (β m : Nat) (L₀ : List Nat) (x : Array Nat)
    (hβ : 2 ≤ β) (hx : x.toList = L₀.take m) (hm : m ≤ L₀.length)
    (hL : ∀ d ∈ L₀, d < β)
    (i : Nat) (hi : i < L₀.length - m) (A : Array Nat)
    (h : OuterInv β m L₀ (ofDigits β (L₀.take m)) i A) :
    OuterInv β m L₀ (ofDigits β (L₀.take m)) (i + 1) (outerStep β m x A i) := by
  obtain ⟨hlen, hlt, hdrop, hval⟩ := h
  have hmi : m + i < A.toList.length := by omega
  have hmiL : m + i < L₀.length := by omega

  have hyi : A[m + i]! = L₀[m + i] := by
    rw [← Array.getElem!_toList, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hmi,
      getElem_of_drop_eq hdrop hmi hmiL]; rfl
  have hyi_lt : A[m + i]! < β := by rw [hyi]; exact hL _ (List.getElem_mem hmiL)

  have hinner := foldl_range'_inv (InnerInv β m L₀ (L₀.take m) A (A[m + i]!) i)
    (innerStep β x (A[m + i]!) i) m (A, 0)
    (by
      refine ⟨hlen, hlt, by omega, rfl, ?_⟩
      simp only [Nat.add_zero, Nat.sub_zero, List.take_zero, ofDigits_nil, Nat.mul_zero, Nat.zero_add]
      rw [Nat.add_comm m i, List.take_add, ofDigits_append, List.length_take_of_le (by omega)])
    (fun j s hj hs => inner_step β m L₀ (L₀.take m) x A (A[m + i]!) i hβ hx
      (List.length_take_of_le hm) (fun d hd => hL d (List.mem_of_mem_take hd)) hyi_lt hlen
      (by omega) j hj s hs)
  simp only [outerStep]
  generalize List.foldl (innerStep β x (A[m + i]!) i) (A, 0) (List.range' 0 m) = r at hinner
  obtain ⟨w, c⟩ := r
  obtain ⟨hlen', hlt', hc, hdrop', hval'⟩ := hinner
  simp only at hlen' hlt' hc hdrop' hval'
  simp only [Nat.sub_self, List.take_zero, ofDigits_nil, Nat.add_zero, List.take_take,
    Nat.min_self] at hval'
  have hk : i + m < w.toList.length := by omega
  refine ⟨by simp [hlen'], ?_, ?_, ?_⟩
  · intro d hd
    simp only [Array.toList_setIfInBounds] at hd
    rcases List.mem_or_eq_of_mem_set hd with h' | h'
    · exact hlt' d h'
    · rw [h']; exact hc
  · simp only [Array.toList_setIfInBounds]
    rw [show m + (i + 1) = i + m + 1 by omega, List.drop_set_of_lt (by omega),
      ← List.drop_drop, hdrop', List.drop_drop, Nat.add_comm i m]
    have := congrArg (List.drop 1) hdrop
    simpa only [List.drop_drop] using this
  · simp only [Array.toList_setIfInBounds]
    rw [show m + (i + 1) = i + m + 1 by omega,
      List.take_succ_eq_append_getElem (by simp; omega), List.getElem_set_self,
      List.take_set_of_le (Nat.le_refl _), ofDigits_append, List.length_take_of_le (by omega)]
    have hiY : i < (L₀.drop m).length := by simp; omega
    rw [List.take_succ_eq_append_getElem hiY, ofDigits_append, List.length_take_of_le (by omega),
      List.getElem_drop, ← hyi]
    simp only [ofDigits_cons, ofDigits_nil, Nat.mul_zero, Nat.add_zero]
    rw [hval', hval]
    generalize ofDigits β (List.take m L₀) = xv
    generalize ofDigits β (List.take i (List.drop m L₀)) = Q
    generalize A[m + i]! = yi
    have e : xv * (β ^ i * yi) = β ^ i * yi * xv := by ac_rfl
    rw [Nat.mul_add, e]

theorem clear_loop (β m : Nat) (w : Array Nat) (hm : m ≤ w.size) (hw : ∀ d ∈ w.toList, d < β)
    (hβ : 2 ≤ β) :
    OuterInv β m w.toList (ofDigits β (w.toList.take m)) 0
      (List.foldl (fun b a => b.setIfInBounds a 0) w (List.range' 0 m)) := by
  have := foldl_range'_inv
    (fun j (w' : Array Nat) => w'.toList.length = w.toList.length ∧ (∀ d ∈ w'.toList, d < β) ∧
      w'.toList.drop j = w.toList.drop j ∧ ofDigits β (w'.toList.take j) = 0)
    (fun b a => b.setIfInBounds a 0) m w
    ⟨rfl, hw, rfl, by simp⟩
    (by
      intro j w' hj ⟨hlen, hlt, hdrop, hval⟩
      have hj' : j < w'.toList.length := by rw [hlen, Array.length_toList]; omega
      refine ⟨by simp [hlen], ?_, ?_, ?_⟩
      · intro d hd
        simp only [Array.toList_setIfInBounds] at hd
        rcases List.mem_or_eq_of_mem_set hd with h' | h'
        · exact hlt d h'
        · rw [h']; omega
      · simp only [Array.toList_setIfInBounds]
        rw [List.drop_set_of_lt (by omega)]
        have := congrArg (List.drop 1) hdrop
        simpa only [List.drop_drop] using this
      · simp only [Array.toList_setIfInBounds]
        rw [List.take_succ_eq_append_getElem (by simp; omega), List.getElem_set_self,
          List.take_set_of_le (Nat.le_refl _), ofDigits_append, hval]
        simp)
  obtain ⟨hlen, hlt, hdrop, hval⟩ := this
  exact ⟨hlen, hlt, by simpa using hdrop, by simpa using hval⟩

theorem ks_improved_correct (β m : Nat) (W : Array Nat)
    (hβ : 2 ≤ β) (hm : 0 < m ∧ m < W.size) (hw : ∀ d ∈ W.toList, d < β) :
    (ks_improved β m W).size = W.size ∧
    (∀ d ∈ (ks_improved β m W).toList, d < β) ∧
    ofDigits β (ks_improved β m W).toList =
      ofDigits β (W.toList.take m) * ofDigits β (W.toList.drop m) := by
  rw [ks_improved_eq]
  have hfin := foldl_range'_inv (OuterInv β m W.toList (ofDigits β (W.toList.take m)))
    (outerStep β m (W.extract 0 m)) (W.size - m) _
    (clear_loop β m W (Nat.le_of_lt hm.2) hw hβ)
    (fun i A hi hA => outer_step β m W.toList (W.extract 0 m) hβ
      (by simp [List.extract_eq_take_drop])
      (by simpa using (Nat.le_of_lt hm.2)) hw i (by simpa using hi) A hA)
  generalize List.foldl (outerStep β m (W.extract 0 m)) _ (List.range' 0 (W.size - m)) = r at hfin
  obtain ⟨hlen, hlt, -, hval⟩ := hfin
  refine ⟨by simpa using hlen, hlt, ?_⟩
  have hlenW : W.toList.length = W.size := Array.length_toList
  rw [show m + (W.size - m) = r.toList.length by omega, List.take_length,
    show W.size - m = (W.toList.drop m).length by simp, List.take_length] at hval
  exact hval
