/-- 1 + 1 = 2 という命題の証明 -/
theorem one_add_one_eq_two : 1 + 1 = 2 := by
  rfl

#check one_add_one_eq_two

#check (by rfl : 1 + 1 = 2)

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  sorry

def idOnNat : Nat → Nat := by
  intro x
  exact x

def idOnNat' : Nat → Nat := by?
  intro x
  exact x

-- 3.6.4 練習問題
example (P Q : Prop) (hp : P) : Q → P := fun _ => hp
