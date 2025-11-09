import LeanBook.NatOrder.AddCancel

/-- 自然数上の広義の順序関係 -/
inductive MyNat.le (n : MyNat) :MyNat → Prop
  /-- ∀ n, n ≤ n -/
  | refl : MyNat.le n n
  /-- n ≤ m ならば n ≤ m + 1 -/
  | step {m : MyNat} : MyNat.le n m → MyNat.le n (m + 1)

/-- MyNat.le を ≤ で表せるようにする -/
instance : LE MyNat where
  le := MyNat.le

example (m n : MyNat) (P : MyNat → MyNat → Prop) (h : m ≤ n) : P m n := by
  induction h with
  | refl => sorry
  | @step n' h ih => sorry

@[induction_eliminator]
def MyNat.le.recAux {n b : MyNat}
  {motive : (a : MyNat) → n ≤ a → Prop}
  (refl : motive n MyNat.le.refl)
  (step : ∀ {m : MyNat} (a: n ≤ m), motive m a → motive (m + 1) (MyNat.le.step a))
  (t : n ≤ b) :
  motive b t := by
  induction t with
  | refl => exact refl
  | @step c h ih => exact step (a := h) ih

/- コード 6.12 -/
/-- 反射律 -/
theorem MyNat.le_refl (n : MyNat) : n ≤ n := by
  exact MyNat.le.refl

theorem MyNat.le_step {m n : MyNat} (h : n ≤ m) : n ≤ m + 1 := by
  apply MyNat.le.step
  exact h

/-- 推移律 -/
theorem MyNat.le_trans {l m n : MyNat} (hlm : l ≤ m) (hmn : m ≤ n) : l ≤ n := by
  induction hmn with
  | refl => exact hlm
  | @step k h ih =>
      exact MyNat.le_step ih

attribute [refl] MyNat.le_refl

theorem MyNat.le_add_one_right (n : MyNat) : n ≤ n + 1 := by
  apply MyNat.le_step
  rfl

instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· ≤ ·) (· ≤ ·) where
  trans := MyNat.le_trans

theorem MyNat.le_add_one_left (n : MyNat) : n ≤ 1 + n := calc
  _ ≤ n + 1 := by apply le_add_one_right
  _ = 1 + n := by ac_rfl

attribute [simp] MyNat.le_refl MyNat.le_add_one_right MyNat.le_add_one_left

theorem MyNat.le.dest {n m : MyNat} (h : n ≤ m) : ∃ k, n + k = m := by
  induction h with
  | refl => exists 0
  | @step m' h' ih =>
      obtain ⟨k, ih'⟩ := ih
      exists k + 1
      rw [← ih']
      ac_rfl

theorem MyNat.le_add_right (n m : MyNat) : n ≤ n + m := by
  induction m with
  | zero => rfl
  | succ m' ih =>
      rw [show n + (m' + 1) = (n + m') + 1 from by ac_rfl]
      exact MyNat.le_step ih

theorem MyNat.le.intro {n m k : MyNat} (h : n + k = m) : n ≤ m := by
  rw [← h]
  apply MyNat.le_add_right

/-- 順序関係 n ≤ m を足し算で書き換える -/
theorem MyNat.le_iff_add {n m : MyNat} : n ≤ m ↔ ∃ k, n + k = m := by
  constructor <;> intro h
  · exact MyNat.le.dest h
  · obtain ⟨k, hk⟩ := h
    exact MyNat.le.intro hk

/-- 6.2.5 練習問題 -/
example : 1 ≤ 4 := by
  exact MyNat.le_add_right 1 3
