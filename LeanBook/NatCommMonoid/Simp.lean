import LeanBook.NatCommMonoid.Induction

example (n : MyNat) : 0 + (n + 0) = n := by
  fail_if_success simp
  rw [MyNat.add_zero]
  rw [MyNat.zero_add]

attribute [simp] MyNat.add_zero MyNat.zero_add

example (n : MyNat) : 0 + (n + 0) = n := by
  simp

theorem MyNat.ctor_eq_zero : MyNat.zero = 0 := rfl

example : MyNat.zero = 0 := by
  simp [MyNat.ctor_eq_zero]

attribute [simp] MyNat.add_succ

example (m n : MyNat) (h : m + n + 0 = n + m) : m + n = n + m := by
  simp at h
  rw [h]

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp at *
  rw [h]

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp_all?

/-- 左のオペランドに付いた .succ は外側に出せる -/
@[simp] theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
 induction n with
  | zero => rfl
  | succ n' ih =>
  simp [ih]

-- 4.3.7 練習問題
example (n : MyNat) : 2 + n = n + 2 := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [MyNat.add_succ]
    rw [ih]
    rfl
