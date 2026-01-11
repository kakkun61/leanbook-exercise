-- LeanBook/NatOrder/NotationSimp.lean
-- 第6章 自然数の順序と、計算を利用する証明
-- 6.4 記法の展開を楽にする

import LeanBook.NatOrder.StrictOrder
import LeanBook.NatOrder.NotationSimpTag

/- コード 6.34 -/
theorem MyNat.lt_def (m n : MyNat) : m < n ↔ m + 1 ≤ n := by
  rfl

/- コード 6.36 -/
section

  open Lean Parser Tactic

  syntax "notation_simp" (simpArgs)? (location)? : tactic

  macro_rules
  | `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) =>
    let args := simpArgs.map (·.getElems) |>.getD #[]
    `(tactic| simp only [notation_simp, $args,*] $[at $location]?)

  attribute [notation_simp] MyNat.lt_def

  syntax "notation_simp?" (simpArgs)? (location)? : tactic
  macro_rules
  | `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) =>
    let args := simpArgs.map (·.getElems) |>.getD #[]
    `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)

end

/- 6.4.4 練習問題 -/
/- コード 6.39 -/
example (a b: MyNat) (h₁: a < b) (h₂: b < a): False := by
  sorry
