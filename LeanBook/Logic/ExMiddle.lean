/-- 二重否定の除去 -/
example (P : Prop) : ¬¬ P → P := by
  -- ¬¬ P だと仮定する
  intro hn2p
  -- 排中律より、P ∨ ¬ P が成り立つ
  by_cases h : P
  -- P が成り立つ場合は即座に証明が終了する
  · exact h
  -- P が成り立たない場合、¬¬ P という仮定と矛盾する
  · contradiction

-- 3.4.3 練習問題 (1)
/-- 含意は「または」と否定で表せる -/
example (P Q : Prop) : (P → Q) ↔ (¬ P ∨ Q) := by
  constructor
  · intro hyp_p_to_q
    by_cases hyp : P
    · right
      exact hyp_p_to_q hyp
    · left
      exact hyp
  · intro hyp_not_p_or_q
    intro hyp_p
    cases hyp_not_p_or_q with
    | inl hyp_not_p => contradiction
    | inr hyp_q => exact hyp_q

-- 3.4.3 練習問題 (2)
/-- ドモルガンの法則 -/
example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  · intro hyp_not_p_and_q
    by_cases hyp : P
    · by_cases hyp' : Q
      · exfalso
        exact hyp_not_p_and_q ⟨hyp, hyp'⟩
      · right
        exact hyp'
    · left
      exact hyp
  · intro hyp_not_p_or_not_q
    intro hyp_p_and_q
    cases hyp_not_p_or_not_q with
    | inl hyp_not_p => exact hyp_not_p hyp_p_and_q.left
    | inr hyp_not_q => exact hyp_not_q hyp_p_and_q.right

-- 3.4.3 練習問題 (3)
/-- 対偶が元の命題と同値であること -/
example (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor
  · intro hyp_p_to_q
    intro hyp_not_q
    intro hyp_p
    exact hyp_not_q (hyp_p_to_q hyp_p)
  · intro hyp_not_q_to_not_p
    intro hyp_p
    by_cases hyp : Q
    · exact hyp
    · have : ¬ P := by
        exact hyp_not_q_to_not_p hyp
      contradiction
