-- 3.2.5 練習問題
example (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro hyp_p_eq_not_p
  have hyp_p_to_p : P → P := by
    intro hyp_p
    exact hyp_p
  have hyp_p_to_not_p : P → ¬ P := by
    rw [← hyp_p_eq_not_p]
    exact hyp_p_to_p
  have hyp_not_p_to_p: ¬ P → P := by
    rw [← hyp_p_eq_not_p]
    exact hyp_p_to_p
  have hyp_not_p : ¬ P := by
    intro hyp_p
    exact hyp_p_to_not_p hyp_p hyp_p
  have hyp_p : P := by
    exact hyp_not_p_to_p hyp_not_p
  contradiction

-- 3.2.5 練習問題 別解
example (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro hyp_p_eq_not_p
  -- 矛盾を言いたいので、P と ¬ P の両方を証明する
  have hyp_not_p : ¬ P := by
    intro hyp_p
    have hyp_not_p' : ¬ P := by
      rw [← hyp_p_eq_not_p]
      exact hyp_p
    contradiction
  have hyp_p : P := by
    rw [hyp_p_eq_not_p]
    exact hyp_not_p
  contradiction
