-- Co-authored by: Fable 5.1

def ks_improved (β m : Nat) (w : Array Nat) : Array Nat := Id.run do
  let n := w.size - m
  let x := w.extract 0 m
  let mut w := w
  for j in [0:m] do
    w := w.set! j 0
  for i in [0:n] do
    let yi := w[m + i]!
    let mut c := 0
    for j in [0:m] do
      let k := i + j
      let t := x[j]! * yi + w[k]! + c
      w := w.set! k (t % β)
      c := t / β
    w := w.set! (i + m) c
  return w

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

theorem ks_improved_eq (β m : Nat) (w : Array Nat) :
    ks_improved β m w =
      List.foldl (outerStep β m (w.extract 0 m))
        (List.foldl (fun b a => b.setIfInBounds a 0) w (List.range' 0 m))
        (List.range' 0 (w.size - m)) := by
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

theorem ks_improved_correct (β m : Nat) (w : Array Nat)
    (hβ : 2 ≤ β) (hm : m ≤ w.size) (hw : ∀ d ∈ w.toList, d < β) :
    (ks_improved β m w).size = w.size ∧
    (∀ d ∈ (ks_improved β m w).toList, d < β) ∧
    ofDigits β (ks_improved β m w).toList =
      ofDigits β (w.toList.take m) * ofDigits β (w.toList.drop m) := by
  rw [ks_improved_eq]
  have hfin := foldl_range'_inv (OuterInv β m w.toList (ofDigits β (w.toList.take m)))
    (outerStep β m (w.extract 0 m)) (w.size - m) _
    (clear_loop β m w hm hw hβ)
    (fun i A hi hA => outer_step β m w.toList (w.extract 0 m) hβ
      (by simp [List.extract_eq_take_drop])
      (by simpa using hm) hw i (by simpa using hi) A hA)
  generalize List.foldl (outerStep β m (w.extract 0 m)) _ (List.range' 0 (w.size - m)) = r at hfin
  obtain ⟨hlen, hlt, -, hval⟩ := hfin
  refine ⟨by simpa using hlen, hlt, ?_⟩
  have hlenw : w.toList.length = w.size := Array.length_toList
  rw [show m + (w.size - m) = r.toList.length by omega, List.take_length,
    show w.size - m = (w.toList.drop m).length by simp, List.take_length] at hval
  exact hval

theorem getElem!_lt {β : Nat} {a : Array Nat} (ha : ∀ d ∈ a.toList, d < β) (hβ : 0 < β) (i : Nat) :
    a[i]! < β := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  cases h : a[i]? with
  | none => exact hβ
  | some d => exact ha d (by simpa using Array.mem_of_getElem? h)

theorem digits_set {β : Nat} {a : Array Nat} (ha : ∀ d ∈ a.toList, d < β) {i v : Nat} (hv : v < β) :
    ∀ d ∈ (a.set! i v).toList, d < β := by
  intro d hd
  simp only [Array.set!, Array.toList_setIfInBounds] at hd
  rcases List.mem_or_eq_of_mem_set hd with h | h
  · exact ha d h
  · rw [h]; exact hv

def ks_improved_checked (β m : Nat) (hβ : 0 < β) (w : Array Nat) (hw : ∀ d ∈ w.toList, d < β) :
    Array Nat := Id.run do
  let n := w.size - m
  let x := w.extract 0 m
  have hx : ∀ d ∈ x.toList, d < β := fun d hd => hw d (by
    simp only [x, Array.toList_extract, List.extract_eq_take_drop] at hd
    exact List.mem_of_mem_drop (List.mem_of_mem_take hd))
  let mut w : {w : Array Nat // ∀ d ∈ w.toList, d < β} := ⟨w, hw⟩
  for j in [0:m] do
    w := ⟨w.1.set! j 0, digits_set w.2 hβ⟩
  for i in [0:n] do
    let yi := w.1[m + i]!
    have hyi : yi < β := getElem!_lt w.2 hβ _
    let mut c : {c : Nat // c < β} := ⟨0, hβ⟩
    for j in [0:m] do
      let k := i + j
      let t := x[j]! * yi + w.1[k]! + c.1
      have hc : t / β < β := carry_lt (getElem!_lt hx hβ j) hyi (getElem!_lt w.2 hβ k) c.2
      w := ⟨w.1.set! k (t % β), digits_set w.2 (Nat.mod_lt _ hβ)⟩
      c := ⟨t / β, hc⟩
    w := ⟨w.1.set! (i + m) c.1, digits_set w.2 c.2⟩
  return w.1

#eval ks_improved_checked 10 2 (by decide) #[4, 3, 2, 1] (by decide)

abbrev Digits (β : Nat) := {w : Array Nat // ∀ d ∈ w.toList, d < β}

def innerStepC (β : Nat) (hβ : 0 < β) (x : Array Nat) (hx : ∀ d ∈ x.toList, d < β)
    (yi : Nat) (hyi : yi < β) (i : Nat) (s : Digits β × {c : Nat // c < β}) (j : Nat) :
    Digits β × {c : Nat // c < β} :=
  let t := x[j]! * yi + s.1.1[i + j]! + s.2.1
  (⟨s.1.1.set! (i + j) (t % β), digits_set s.1.2 (Nat.mod_lt _ hβ)⟩,
   ⟨t / β, carry_lt (getElem!_lt hx hβ j) hyi (getElem!_lt s.1.2 hβ (i + j)) s.2.2⟩)

def outerStepC (β m : Nat) (hβ : 0 < β) (x : Array Nat) (hx : ∀ d ∈ x.toList, d < β)
    (w : Digits β) (i : Nat) : Digits β :=
  let r := List.foldl (innerStepC β hβ x hx (w.1[m + i]!) (getElem!_lt w.2 hβ _) i)
    (w, ⟨0, hβ⟩) (List.range' 0 m)
  ⟨r.1.1.set! (i + m) r.2.1, digits_set r.1.2 r.2.2⟩

theorem ks_improved_checked_eq (β m : Nat) (hβ : 0 < β) (w : Array Nat)
    (hw : ∀ d ∈ w.toList, d < β) :
    ks_improved_checked β m hβ w hw =
      (List.foldl (outerStepC β m hβ (w.extract 0 m) (fun d hd => hw d (by
            simp only [Array.toList_extract, List.extract_eq_take_drop] at hd
            exact List.mem_of_mem_drop (List.mem_of_mem_take hd))))
        (List.foldl (fun (b : Digits β) a => ⟨b.1.set! a 0, digits_set b.2 hβ⟩) ⟨w, hw⟩
          (List.range' 0 m))
        (List.range' 0 (w.size - m))).1 := by
  simp [ks_improved_checked]
  rfl

theorem innerStepC_val (β : Nat) (hβ : 0 < β) (x : Array Nat) (hx : ∀ d ∈ x.toList, d < β)
    (yi : Nat) (hyi : yi < β) (i : Nat) (s : Digits β × {c : Nat // c < β}) (j : Nat) :
    innerStep β x yi i (s.1.1, s.2.1) j =
      ((innerStepC β hβ x hx yi hyi i s j).1.1, (innerStepC β hβ x hx yi hyi i s j).2.1) := rfl

theorem outerStepC_val (β m : Nat) (hβ : 0 < β) (x : Array Nat) (hx : ∀ d ∈ x.toList, d < β)
    (w : Digits β) (i : Nat) :
    outerStep β m x w.1 i = (outerStepC β m hβ x hx w i).1 := by
  simp only [outerStep, outerStepC, Array.set!]
  rw [List.foldl_hom (fun s : Digits β × {c : Nat // c < β} => (s.1.1, s.2.1))
    (g₁ := innerStepC β hβ x hx (w.1[m + i]!) (getElem!_lt w.2 hβ _) i)
    (g₂ := innerStep β x (w.1[m + i]!) i) (init := (w, ⟨0, hβ⟩))
    (fun s j => innerStepC_val β hβ x hx _ _ i s j)]

theorem ks_improved_checked_val (β m : Nat) (hβ : 0 < β) (w : Array Nat)
    (hw : ∀ d ∈ w.toList, d < β) :
    ks_improved_checked β m hβ w hw = ks_improved β m w := by
  rw [ks_improved_eq, ks_improved_checked_eq]
  rw [← List.foldl_hom Subtype.val (g₂ := outerStep β m (w.extract 0 m))
    (fun A i => outerStepC_val β m hβ _ _ A i)]
  rw [← List.foldl_hom Subtype.val (g₂ := fun b a => b.setIfInBounds a 0) (fun b a => rfl)]

theorem ks_improved_checked_correct (β m : Nat) (w : Array Nat)
    (hβ : 2 ≤ β) (hm : m ≤ w.size) (hw : ∀ d ∈ w.toList, d < β) :
    (ks_improved_checked β m (by omega) w hw).size = w.size ∧
    (∀ d ∈ (ks_improved_checked β m (by omega) w hw).toList, d < β) ∧
    ofDigits β (ks_improved_checked β m (by omega) w hw).toList =
      ofDigits β (w.toList.take m) * ofDigits β (w.toList.drop m) := by
  rw [ks_improved_checked_val]
  exact ks_improved_correct β m w hβ hm hw
