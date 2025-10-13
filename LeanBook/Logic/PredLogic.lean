/-- 人間たちの集合 -/
opaque Human : Type

/-- 愛の関係 -/
opaque Love : Human → Human → Prop

@[inherit_doc]
infix:50 "-♥→" => Love

/-- すべての人に愛されているアイドルが存在する -/
def IdolExists :=
  ∃ idol : Human, ∀ h : Human, h -♥→ idol

/-- 誰にでも好きな人の 1 人くらいいる -/
def EveryoneLovesSomeone :=
  ∀ h : Human, ∃ tgt : Human, h -♥→ tgt

/-- すべての人を愛している博愛主義者（philanthropist）が存在する -/
def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -♥→ h

def EveryoneLoved : Prop := ∀ h : Human, ∃ lover : Human, lover -♥→ h

example : PhilanExists → EveryoneLoved := by
  intro hyp_philan_exists
  obtain ⟨philan', hyp_philan'_exists⟩ := hyp_philan_exists
  intro human
  exists philan'
  exact hyp_philan'_exists human

/- 練習問題 3.3.4 -/
example : IdolExists → EveryoneLovesSomeone := by
  intro hyp_idol_exists
  intro human
  obtain ⟨idol, hyp_the_idol_exists⟩ := hyp_idol_exists
  have hyp_human_loves_idol : human -♥→ idol := by
    exact hyp_the_idol_exists human
  exists idol

example
  (α : Type) (P : α → Prop) :
  (∀ x, P x) → (∃ x, P x) ∨ (∀ x, ¬ P x) := by
  intro hyp_forall_x_px
  -- ある α 型の値を a とする
  let a : α := sorry
  left
  exists a
  exact hyp_forall_x_px a

example
  (α : Type) (P Q : α → Prop) :
  (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
  intro hyp_forall_x_px_to_qx
  intro hyp_forall_x_px
  intro x
  exact hyp_forall_x_px_to_qx x (hyp_forall_x_px x)

example
  (α : Type) (P Q : α → Prop) :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  intro hyp_exists_x_px_and_qx
  obtain ⟨x, hyp_px_and_qx⟩ := hyp_exists_x_px_and_qx
  constructor
  · exists x
    exact hyp_px_and_qx.left
  · exists x
    exact hyp_px_and_qx.right

example
  (α : Type) (P Q : α → Prop) :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∃ x, Q x) := by
  sorry

example
  (α : Type) (P Q : α → Prop) :
  (∀ x, P x → Q x) → (∃ x, P x) → (∃ x, Q x) := by
  sorry
