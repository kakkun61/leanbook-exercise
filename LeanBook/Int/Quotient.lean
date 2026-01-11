-- LeanBook/Int/Quotient.lean
-- 第7章 同値関係で割って整数を作る
-- 7.2 商とQuotient

/- 7.2.6 練習問題 -/
/--
 - β 上の二項関係 r : β → β → Prop と関数 f : α → β があるとき、
 - α 上の二項関係を fun x y => r (f x) (f y) で定義できる
 -/
private def Rel.comap {α β : Type} (f : α → β) (r : β → β → Prop) : α → α → Prop :=
  fun x y => r (f x) (f y)

/--
 - β 上の同値関係 sr : Setoid β と関数 f : α → β があるとき、
 - Rel.comap f (· ≈ ·) も同値関係になる
 -/
private def Setoid.comap {α β : Type} (f : α → β) (sr : Setoid β) : Setoid α where
  r := Rel.comap f (· ≈ ·)
  iseqv := by
    constructor

    case refl =>
      intro x
      unfold Rel.comap
      simp
      apply sr.iseqv.refl

    case symm =>
      intro x y
      unfold Rel.comap
      simp
      apply sr.iseqv.symm

    case trans =>
      intro x y z
      unfold Rel.comap
      simp
      apply sr.iseqv.trans
