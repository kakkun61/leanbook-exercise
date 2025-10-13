import LeanBook.NatCommMonoid.TypeClass

theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [MyNat.add_zero]

/-- add_zero の等式の順序が逆のバージョン -/
theorem MyNat.add_zero_rev (n : MyNat) : n = n + 0 := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [← MyNat.add_zero_rev]

example (m n : MyNat) (h : m + 0 = n) : n + m = m + n := by
  -- 仮定の h を簡略化して m = n を得る
  rw [MyNat.add_zero] at h
  rw [h]

/-- 右のオペランドに付いた .succ は外側に出せる -/
theorem MyNat.add_succ (m n : MyNat) : m + .succ n = .succ (m + n) := by
  rfl

example (n : MyNat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [MyNat.add_succ]
    rw [ih]

-- 4.2.6 練習問題
example (n : MyNat) : 1 + n = .succ n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [MyNat.add_succ]
    rw [ih]
