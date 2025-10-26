import LeanBook.NatCommMonoid.AcRfl

#check MyNat.rec

def MyNat.recAux.{u} {motive : MyNat → Sort u}
  (zero : motive 0)
  (succ : (n : MyNat) → motive n → motive (n + 1))
  (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

attribute [induction_eliminator] MyNat.recAux

example (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero => simp
  | succ n' ih => ac_rfl

-- 4.5.4 練習問題
/-- 「1 つ前」の自然数を返す関数。ゼロに対してはゼロを返すことに注意 -/
private def MyNat.pred (n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => n

example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  rfl
-- 4.5.4 練習問題 ここまで

-- 4.5.4 練習問題 改案
/-- 再帰的に定義された、自然数を2倍にする関数 -/
private def MyNat.double (n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => (MyNat.double n) + 2

example (n : MyNat) : MyNat.double (MyNat.double n) = n + n + n + n := by
  induction n with
  | zero => rfl
  | succ n' ih => calc
      _ = MyNat.double (MyNat.double (n' + 1)) := by rfl
      _ = MyNat.double (MyNat.double n' + 2) := by rfl
      _ = MyNat.double (MyNat.double n') + 2 + 2 := by rfl
      _ = n' + n' + n' + n' + 2 + 2 := by rw [ih]
      _ = n' + n' + n' + n' + 1 + 1 + 1 + 1 := by rfl
      _ = (n' + 1) + (n' + 1) + (n' + 1) + (n' + 1) := by ac_rfl
-- 4.5.4 練習問題 改案 ここまで
