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
