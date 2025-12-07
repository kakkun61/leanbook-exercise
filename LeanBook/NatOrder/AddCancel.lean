import LeanBook.NatSemiring.Distrib

/- コード 6.1 -/
/-- MyNat の各コンストラクタの像は重ならない -/
example (n : MyNat) : MyNat.succ n ≠ MyNat.zero := by
  intro h
  injection h

/-- MyNat のコンストラクタは単射 -/
example (m n : MyNat) (h : MyNat.succ m = MyNat.succ n) : m = n := by
  injection h

example (m n : MyNat) (h : m + 1 = n + 1) : m = n := by
  injection h

/- コード 6.2 -/
/-- 右から足す演算 (· + m) は単射 -/
theorem MyNat.add_right_cancel {l m n : MyNat} (h : l + m = n + m) : l = n := by
  induction m with
  | zero => simp_all
  | succ m' ih =>
      have h : (l + m') + 1 = (n + m') + 1 := calc
        _ = l + (m' + 1) := by ac_rfl
        _ = n + (m' + 1) := by rw [h]
        _ = (n + m') + 1 := by ac_rfl

      have : l + m' = n + m' := by
        injection h

      exact ih this

/-- 左から足す演算 (l + ·) は単射 -/
theorem MyNat.add_left_cancel {l m n : MyNat} (h : l + m = l + n) : m = n := by
  rw [MyNat.add_comm l m, MyNat.add_comm l n] at h
  apply MyNat.add_right_cancel h

/- コード 6.4 -/
/-- 右からの足し算のキャンセル -/
@[simp ↓]
theorem MyNat.add_right_cancel_iff {l m n : MyNat} : l + m = n + m ↔ l = n := by
  constructor
  · apply MyNat.add_right_cancel
  · intro h
    rw [h]

/-- 左からの足し算のキャンセル -/
@[simp ↓ ]
theorem MyNat.add_left_cancel_iff {l m n : MyNat} : l + m = l + n ↔ m = n := by
  -- 同値性の両方の方向を示す
  constructor
  · apply MyNat.add_left_cancel
  · intro h
    rw [h]

example {l m n : MyNat} : l + m = l + n → m = n := by
  -- simp で示せるようになった
  simp

/- コード 6.5 -/
@[simp]
theorem MyNat.add_right_eq_self {m n : MyNat} : m + n = m ↔ n = 0 := by
  constructor
  case mp =>
    intro hyp_m_plus_n_eq_m
    have : m + n = m + 0 := by
      rw [hyp_m_plus_n_eq_m]
      simp
    simp_all
  case mpr =>
    simp_all

@[simp]
theorem MyNat.add_left_eq_self : n + m = m ↔ n = 0 := by
  rw [MyNat.add_comm n m, MyNat.add_right_eq_self] -- 可換性から従う

@[simp]
theorem MyNat.self_eq_add_right : m = m + n ↔ n = 0 := by
  rw [show (m = m + n) ↔ (m + n = m) from by exact eq_comm]
  exact add_right_eq_self

@[simp]
theorem MyNat.self_eq_add_left : m = n + m ↔ n = 0 := by
  rw [MyNat.add_comm n m, MyNat.self_eq_add_right] -- 可換性から従う

/- コード 6.6 -/
theorem MyNat.eq_zero_of_add_eq_zero { m n : MyNat } : m + n = n → m = 0 ∧ n = 0 := by
  intro hyp_m_plus_n_eq_n
  induction n with
  | zero => simp_all
  | succ n' ih =>
      sorry

theorem MyNat.add_eq_zero_of_eq_zero { m n : MyNat } : m = 0 ∧ n = 0 → m + n = 0 := by
  intro h
  simp_all

/-- 和がゼロであることと両方がゼロであることは同値 -/
@[simp]
theorem MyNat.add_eq_zero_iff_eq_zero { m n : MyNat } : m + n = 0 ↔ m = 0 ∧ n = 0 := by
  sorry
  -- exact ⟨MyNat.eq_zero_of_add_eq_zero, MyNat.add_eq_zero_of_eq_zero⟩

/- 6.1.5 練習問題 -/
example (n m : MyNat) : n + (1 + m) = n + 2 → m = 1 := by
  intro hyp_n_plus_1_plus_m_eq_n_plus_2
  have h : 1 + m = 2 := by
    simp_all
  have : 2 = 1 + 1 := by rfl
  have : 1 + m = 1 + 1 := by
    rw [this] at h
    exact h
  simp_all
