-- LeanBook/NatOrder/StrictOrder.lean
-- 第6章 自然数の順序と、計算を利用する証明
-- 6.3 狭義順序関係を定義する

import LeanBook.NatOrder.OrderDef

-- コード 6.21
def MyNat.lt (m n : MyNat) : Prop := (m + 1) ≤ n

instance : LT MyNat where
  lt := MyNat.lt

-- コード 6.22
example (m n : MyNat) : m < n ↔ (m + 1) ≤ n := by
  dsimp [(· < ·), MyNat.lt]
  rfl

-- コード 6.23
@[simp]
theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

@[simp]
theorem MyNat.zero_neq_one : 0 ≠ 1 := by
  intro h
  injection h

-- コード 6.24
@[simp]
theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
  rw [MyNat.le_iff_add]
  exists n
  simp

/- コード 6.25 -/
theorem MyNat.zero_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    exfalso
    rw [MyNat.le_iff_add] at h
    obtain ⟨k, hk⟩ := h
    simp_all

@[simp]
theorem MyNat.le_zero {n : MyNat} : n ≤ 0 ↔ n = 0 := by
  constructor
  · intro hyp_n_le_zero
    apply MyNat.zero_of_le_zero hyp_n_le_zero
  · intro hyp_n_eq_zero
    simp [hyp_n_eq_zero]

-- コード 6.26
/-- 任意の自然数はゼロか正 -/
theorem MyNat.eq_zero_or_pos (n : MyNat) : n = 0 ∨ 0 < n := by
  induction n with
  | zero => simp
  | succ n' ih =>
    dsimp [(· < ·), MyNat.lt] at *
    cases ih with
    | inl ih => simp_all
    | inr ih => simp_all [MyNat.le_step]

-- コード 6.27
theorem MyNat.eq_or_lt_of_le {m n : MyNat} : n ≤ m → n = m ∨ n < m := by
  intro h
  dsimp [(· < ·), MyNat.lt]
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  induction k with
  | zero => simp_all
  | succ k' _ =>
    have : ∃ k, n + 1 + k = m := by
      exists k'
      rw [← hk]
      ac_rfl
    simp_all

-- コード 6.28
/-- 狭義関係は広義関係よりも「強い」 -/
theorem MyNat.le_of_lt {a b : MyNat} (h : a < b) : a ≤ b := by
  dsimp [(· < ·), MyNat.lt] at h
  have : a ≤ b := calc
    _ ≤ a + 1 := by simp
    _ ≤ b := by assumption
  assumption

theorem MyNat.le_of_eq_or_lt {m n : MyNat} : n = m ∨ n < m → n ≤ m := by
  intro h
  cases h with
  | inl h => rw [h]
  | inr h => apply MyNat.le_of_lt h

-- コード 6.29 -/
/-- 広義順序 ≤ は等号 = と狭義順序 < で書き換えられる -/
theorem MyNat.le_iff_eq_or_lt {m n : MyNat} : n ≤ m ↔ n = m ∨ n < m := by
  constructor
  · apply MyNat.eq_or_lt_of_le
  · apply MyNat.le_of_eq_or_lt

-- コード 6.30
theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
  -- a < b を定義に従い a + 1 ≤ b に書き換える
  dsimp [(· < ·), MyNat.lt]

  induction a with
  | zero =>
      suffices 1 ≤ b ∨ b ≤ 0 from by
        simp_all
      have : b = 0 ∨ 0 < b := MyNat.eq_zero_or_pos b
      dsimp [(· < ·), MyNat.lt] at this
      cases this <;> simp_all
  | succ a' ih =>
    cases ih with
    | inr h =>
      right
      apply le_step h
    | inl h =>
      simp [MyNat.le_iff_eq_or_lt] at h
      cases h with
      | inl h =>
        right
        simp_all
      | inr h =>
        dsimp [(· < ·), MyNat.lt] at h
        left
        assumption

-- コード 6.31
theorem MyNat.lt_of_not_le {a b : MyNat} (h : ¬ a ≤ b) : b < a := by
cases (MyNat.lt_or_ge b a) with
| inl h => assumption
  | inr h => contradiction

theorem MyNat.not_le_of_lt {a b : MyNat} (h : a < b) : ¬ b ≤ a := by
  intro hle

  dsimp [(· < ·), MyNat.lt] at h

  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := hle

  have : a + (k + l + 1) = a := calc
    _ = a + 1 + k + l := by ac_rfl
    _ = b + l := by rw [hk]
    _ = a := by rw [hl]

  simp at this

theorem MyNat.lt_iff_le_not_le (a b : MyNat) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor <;> intro h
  case mp => simp_all [MyNat.not_le_of_lt, MyNat.le_of_lt]
  case mpr => simp_all [MyNat.lt_of_not_le]

-- コード 6.32
theorem MyNat.le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  cases (MyNat.lt_or_ge a b) <;> simp_all [MyNat.le_of_lt]

/-- 6.3.3 練習問題 -/
-- コード 6.33
example (a : MyNat) : a ≠ a + 1 := by
  sorry

example (n : MyNat) : ¬ n + 1 ≤ n := by
  sorry
