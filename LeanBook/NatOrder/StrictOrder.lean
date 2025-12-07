import LeanBook.NatOrder.OrderDef

def MyNat.lt (m n : MyNat) : Prop := (m + 1) ≤ n

instance : LT MyNat where
  lt := MyNat.lt

example (m n : MyNat) : m < n ↔ (m + 1) ≤ n := by
  dsimp [(· < ·), MyNat.lt]
  rfl

@[simp]
theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

@[simp]
theorem MyNat.zero_neq_one : 0 ≠ 1 := by
  intro h
  injection h

@[simp]
theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
  rw [MyNat.le_iff_add]
  exists n
  simp

/- コード 6.25 -/
theorem MyNat.zero_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by

  sorry

@[simp]
theorem MyNat.le_zero {n : MyNat} : n ≤ 0 ↔ n = 0 := by
  constructor
  · intro hyp_n_le_zero
    sorry
  · intro hyp_n_eq_zero
    sorry

-- コード 6.26
/-- 任意の自然数はゼロか正 -/
theorem MyNat.eq_zero_or_pos (n : MyNat) : n = 0 ∨ 0 < n := by
  sorry

-- コード 6.27
theorem MyNat.eq_or_lt_of_le {m n : MyNat} : n ≤ m → n = m ∨ n < m := by
  sorry

-- コード 6.28
/-- 狭義関係は広義関係よりも「強い」 -/
theorem MyNat.le_of_lt {a b : MyNat} (h : a < b) : a ≤ b := by
  sorry

theorem MyNat.le_of_eq_or_lt {m n : MyNat} : n = m ∨ n < m → n ≤ m := by
  sorry

-- コード 6.29 -/
/-- 広義順序 ≤ は等号 = と狭義順序 < で書き換えられる -/
theorem MyNat.le_iff_eq_or_lt {m n : MyNat} : n ≤ m ↔ n = m ∨ n < m := by
  sorry

-- コード 6.30
theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
  -- a < b を定義に従い a + 1 ≤ b に書き換える
  dsimp [(· < ·), MyNat.lt]

  induction a with
  | zero => sorry
  | succ a' ih => sorry

-- コード 6.31
theorem MyNat.lt_of_not_le {a b : MyNat} (h : ¬ a ≤ b) : b < a := by
  sorry

theorem MyNat.not_le_of_lt {a b : MyNat} (h : a < b) : ¬ b ≤ a := by
  sorry
