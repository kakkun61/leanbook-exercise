-- LeanBook/NatOrder/OrdMonoid.lean
-- 第6章 自然数の順序と、計算を利用する証明
-- 6.5 足し算が順序を保つことを示す

import LeanBook.NatOrder.NotationSimp
import LeanBook.NatOrder.CompatibleTag

/- コード 6.40 -/
variable {a b m n : MyNat}

/-- 足し算 (l + ·) は順序関係を保つ -/
theorem MyNat.add_le_add_left (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  exists k
  rw [← hk]
  ac_rfl

/-- 足し算 (· + l) は順序関係を保つ -/
theorem MyNat.add_le_add_right (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := calc
  _ = l + m := by ac_rfl
  _ ≤ l + n := by apply MyNat.add_le_add_left h l
  _ = n + l := by ac_rfl

theorem MyNat.add_le_add (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := calc
  _ ≤ m + b := by exact add_le_add_left h2 m
  _ ≤ n + b := by exact add_le_add_right h1 b

/- コード 6.42 -/
example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  apply MyNat.add_le_add_left <;> assumption

/- コード 6.43 -/
/-- 関係 a ∼ b が成り立つなら f a ∼ f b が成り立つ、というタイプの推論を行う -/
syntax "compatible" : tactic

/- コード 6.44 -/
section

  local macro_rules
  | `(tactic| compatible) =>
    `(tactic| apply MyNat.add_le_add_left <;> assumption)

  local macro_rules
  | `(tactic| compatible) =>
    `(tactic| apply MyNat.add_le_add_right <;> assumption)

  local macro_rules
  | `(tactic| compatible) =>
    `(tactic| apply MyNat.add_le_add <;> assumption)

  example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
    compatible

  example (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
    compatible

  example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
    compatible

end

/- コード 6.45 は CompatibleTag.lean -/


/- コード 6.46 -/
open Lean Elab Tactic in

/-- 関係 a ∼ b が成り立つなら f a ∼ f b が成り立つ、というタイプの推論を行う -/
elab "compatible" : tactic => do
  -- [compatible] 属性が付与された定理をリストアップする
  let taggedDecls ← labelled `compatible
  if taggedDecls.isEmpty then
    throwError "`[compatible]`が付与された定理はありません。"
  for decl in taggedDecls do
    let declStx := mkIdent decl
    try
      -- [compatible] 属性が付与された定理 thm に対して apply thm <;> assumption を試す
      evalTactic <| ← `(tactic| apply $declStx <;> assumption)
      -- 成功したら終了する
      return ()
    catch _ =>
      -- 失敗したら単に次の候補に進む
      pure ()
  throwError "ゴールを閉じることができませんでした。"

/- コード 6.47 -/
attribute [compatible]
  MyNat.add_le_add_left
  MyNat.add_le_add_right
  MyNat.add_le_add

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  compatible

example (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  compatible

example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
  compatible

/- コード 6.48 -/
@[compatible]
theorem MyNat.add_lt_add_left {m n : MyNat} (h : m < n) (k : MyNat) : k + m < k + n := by
  notation_simp at *
  have : k + m + 1 ≤ k + n := calc
    _ = k + (m + 1) := by ac_rfl
    _ ≤ k + n := by compatible
  assumption

@[compatible]
theorem MyNat.add_lt_add_right {m n : MyNat} (h : m < n) (k : MyNat) : m + k < n + k := calc
  _ = k + m := by ac_rfl
  _ < k + n := by compatible
  _ = n + k := by ac_rfl

/- コード 6.49 -/
section

  variable (m n k : MyNat)

  theorem MyNat.le_of_add_le_add_left : k + m ≤ k + n → m ≤ n := by
    intro h
    rw [MyNat.le_iff_add] at *
    obtain ⟨d, hd⟩ := h
    exists d
    have : m + d + k = n + k := calc
      _ = k + m + d := by ac_rfl
      _ = k + n := by rw [hd]
      _ = n + k := by ac_rfl
    simp_all

  theorem MyNat.le_of_add_le_add_right : m + k ≤ n + k → m ≤ n := by
    rw [MyNat.add_comm m k, MyNat.add_comm n k]
    apply MyNat.le_of_add_le_add_left

  @[simp]
  theorem MyNat.add_le_add_iff_left : k + m ≤ k + n ↔ m ≤ n := by
    constructor
    · apply MyNat.le_of_add_le_add_left
    · intro h
      compatible

  @[simp]
  theorem MyNat.add_le_add_iff_right : m + k ≤ n + k ↔ m ≤ n := by
    constructor
    · apply MyNat.le_of_add_le_add_right
    · intro h
      compatible

end

-- 6.5.5 練習問題
variable (l₁ l₂ m₁ m₂ n₁ n₂ : MyNat)

example (h₁ : l₁ ≤ l₂) (h₂ : n₁ ≤ n₂) (h₃ : m₁ ≤ m₂)
  : l₁ + m₁ + n₁ ≤ l₂ + n₂ + m₂ := calc
  l₁ + m₁ + n₁ = l₁ + n₁ + m₁ := by ac_rfl
  _ ≤ l₁ + n₁ + m₂ := by compatible
  _ ≤ l₁ + n₂ + m₂ := by sorry
  _ ≤ l₂ + n₂ + m₂ := by sorry
