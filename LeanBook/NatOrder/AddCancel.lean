import LeanBook.NatSemiring.Distrib

/-- MyNat の各コンストラクタの像は重ならない -/
example (n : MyNat) : MyNat.succ n ≠ MyNat.zero := by
  intro h
  injection h

/-- MyNat のコンストラクタは単射 -/
example (m n : MyNat) (h : MyNat.succ m = MyNat.succ n) : m = n := by
  injection h

example (m n : MyNat) (h : m + 1 = n + 1) : m = n := by
  injection h
