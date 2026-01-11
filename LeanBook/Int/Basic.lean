-- LeanBook/Int/Basic.lean
-- 第7章 同値関係で割って整数を作る
-- 7.3 整数を作る

import LeanBook.NatOrder.DecidableOrd

-- コード 7.21
/-- 自然数ふたつペアにしたもの -/
abbrev PreInt := MyNat × MyNat

-- コード 7.22
def PreInt.r (m n : PreInt) : Prop :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => m₁ + n₂ = m₂ + n₁

-- コード 7.23
/-- 反射律 -/
theorem PreInt.r.refl : ∀ (m : PreInt), r m m := by
  intro (m₁, m₂)
  dsimp [r]
  ac_rfl

/-- 対称律 -/
theorem PreInt.r.symm : ∀ {m n : PreInt}, r m n → r n m := by
  sorry

/-- 推移律 -/
theorem PreInt.r.trans : ∀ {l m n : PreInt}, r l m → r m n → r l n := by
  sorry

/- PreInt.r は同値関係 -/
theorem PreInt.r.equiv : Equivalence r :=
  { refl := r.refl, symm := r.symm, trans := r.trans }

-- コード 7.24
/-- PreInt 上の同値関係 -/
@[instance]
def PreInt.sr : Setoid PreInt := ⟨ r, r.equiv ⟩

/-- MyNat ⨯ MyNat を同値関係で割ることで構成した整数 -/
abbrev MyInt := Quotient PreInt.sr

-- TODO 続き
