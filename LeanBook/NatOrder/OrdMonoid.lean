-- 6.5 足し算が順序を保つことを示す

import LeanBook.NatOrder.NotationSimp
import LeanBook.NatOrder.CompatibleTag

variable {a b m n : MyNat}

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  apply MyNat.add_le_add_left <;> assumption

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
  throwError " ゴールを閉じることができませんでした。"

attribute [compatible] MyNat.add_le_add_left
  MyNat.add_le_add_right MyNat.add_le_add

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  compatible

example (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  compatible

example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
  compatible

-- コード 6.48
@[compatible]
theorem MyNat.add_lt_add_left {m n : MyNat} (h : m < n) (k : MyNat) : k + m < k + n := by
  notation_simp at *
  have : k + m + 1 ≤ k + n := calc
  _ = k + (m + 1) := by ac_rfl
  _ ≤ k + n := by compatible
  assumption

@[compatible]
theorem MyNat.add_lt_add_right {m n : MyNat} (h : m < n) (k : MyNat)
    : m + k < n + k := calc
  _ = k + m := by ac_rfl
  _ < k + n := by compatible
  _ = n + k := by ac_rfl

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
variable (m1 m2 n1 n2 l1 l2 : MyNat)
example (h1 : m1 ≤ m2) (h2 : n1 ≤ n2) (h3 : l1 ≤ l2)
  : l1 + m1 + n1 ≤ l2 + n2 + m2 := calc
  l1 + m1 + n1 = l1 + n1 + m1 := by ac_rfl
  _ ≤ l2 + n1 + m1 := by compatible
  _ ≤ l2 + n2 + m2 := by sorry
