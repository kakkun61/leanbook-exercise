import LeanBook.NatOrder.PartialOrder

deriving instance DecidableEq for MyNat

#eval 1 ≠ 2

/- コード 6.59 -/
def MyNat.ble (a b : MyNat) : Bool :=
  match a, b with
  | 0, _ => true
  | _, 0 => false
  | a' + 1, b' + 1 => MyNat.ble a' b'

#eval MyNat.ble 0 1

#eval MyNat.ble 3 2

instance (a b : MyNat) : Decidable (a ≤ b) := by
  apply decidable_of_iff (MyNat.ble a b = true)
  sorry

#check MyNat.ble.induct

@[simp]
theorem MyNat.ble_zero_left (n : MyNat) : MyNat.ble 0 n = true := by
  rfl

@[simp]
theorem MyNat.ble_zero_right (n : MyNat) : MyNat.ble (n + 1) 0 = false := by
  rfl

@[simp]
theorem MyNat.ble_succ (m n : MyNat) : MyNat.ble (m + 1) (n + 1) = MyNat.ble m n := by
  rfl

def MyNat.ble.inductAux (motive : MyNat → MyNat → Prop)
    (case1 : ∀ (n : MyNat), motive 0 n)
    (case2 : ∀ (n : MyNat), motive (n + 1) 0)
    (case3 : ∀ (m n : MyNat), motive m n → motive (m + 1) (n + 1))
    (m n : MyNat) : motive m n := by
  induction m, n using MyNat.ble.induct with
  | case1 n => apply case1
  | case2 n => apply case2
  | case3 m n h => apply case3; assumption

theorem MyNat.le_impl (m n : MyNat) : MyNat.ble m n = true ↔ m ≤ n := by
  induction m, n using MyNat.ble.inductAux with
  | case1 n => simp
  | case2 n => simp
  | case3 m n ih => simp_all

/- コード 6.68 -/
instance : DecidableLE MyNat := fun n m =>
  decidable_of_iff (MyNat.ble n m = true) (MyNat.le_impl n m)

#eval 1 ≤ 2

/- コード 6.70 -/
theorem MyNat.lt_impl (m n : MyNat) : MyNat.ble (m + 1) n ↔ m < n := by
  rw [MyNat.le_impl]
  rfl

/-- 狭義の順序関係を決定可能にする -/
instance : DecidableLT MyNat := fun n m =>
  decidable_of_iff (MyNat.ble (n + 1) m = true) (MyNat.lt_impl n m)

/- 6.7.6 練習問題 -/
example : 23 < 32 ∧ 12 ≤ 24 := by
  decide
