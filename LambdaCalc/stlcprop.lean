import LambdaCalc.typing
import LambdaCalc.semantics
import LambdaCalc.syntax
import LambdaCalc.maps
import Mathlib
-- Canonical Forms

lemma canonical_form_bool : ∀ t : tm,
  empty |- t ∈ Bool →
  value t →
  ((t = <{true}>) ∨ (t = <{false}>)) := by
  intros t HT HVal
  cases HT
  case T_True
  · left
    rfl
  case T_False
  · right
    rfl
  all_goals {contradiction}

lemma canonical_form_fun : ∀ t T1 T2,
  empty |- t ∈ (T1 -> T2) →
  value t →
  ∃ x, ∃ u, t = <{λx:T1, u}> := by
  intros t T1 T2 HT HVal
  cases HT
  case T_Abs x t1 a
  · use x
    use t1
  all_goals {contradiction}

-- Progress - any well-typed term is either a value or can step

theorem progress : ∀ t T,
  empty |- t ∈ T →
  (value t) ∨ (∃ t', t ==> t') := by
  intros t T HT
  revert T
  induction' t with x a1 a2 ih ih2 x T1 t1 ih a1 a2 a3 ih1 ih2 ih3
  <;> intros T HT
  <;> try contradiction
  case tm_true
  · left
    apply value.v_true
  case tm_false
  · left
    apply value.v_false
  case tm_abs
  · left
    apply value.v_abs
  case tm_app
  · right
    cases' HT
    · case tm_app.h.T_App T2 H3 H4
      have HA3 : value a1 ∨ ∃ t', a1==>t' := by
        {apply ih; apply H4}
      have HA4 : value a2 ∨ ∃ t', a2 ==> t' := by
        {apply ih2; apply H3}    
      cases' HA3 with h h'
      · cases' HA4 with h1 h2
        have tAbs : ∃ x, ∃ u, a1 = <{λx:T2, u}> := by
          { apply canonical_form_fun; apply H4; exact h }
        cases' tAbs with x H
        cases' H with u H'
        rw [H']
        use <{[x := a2] u}>
        apply step.ST_AppAbs
        exact h1
        cases' h2 with t' Ht'
        use (a1 ∘ t')
        apply step.ST_App2
        exact h
        exact Ht'
      cases' h' with t Ht
      use (t ∘ a2)
      apply step.ST_App1
      exact Ht
  cases' HT
  case tm_if H1 H2 H3
  have Ha1 : value a1 ∨ ∃ t', a1==>t' := by
    { apply ih1; apply H1; }
  right
  cases' Ha1 with h1 h2
  have a1B : ((a1 = <{true}>) ∨ (a1 = <{false}>)) := by
    { apply canonical_form_bool; exact H1; exact h1 }
  cases' a1B with a1true a1false
  use a2
  rw [a1true]
  apply step.ST_IfTrue
  use a3
  rw [a1false]
  apply step.ST_IfFalse
  cases' h2 with t' Ht'
  use <{if t' then a2 else a3}>
  apply step.ST_If
  exact Ht'

-- Preservation - Reduction preserves types

---- We begin with the weakening lemma - since ST_AppAbs involves substitution, we need to show
---- that types are preserved under substitution, but to show this we need to show that
---- if s is of type S in the empty context then s is of type S in any context, which
---- is what the weakening lemma provides

-- lemma weakening : ∀ Γ Γ' t T,
--   includedin Γ Γ' →
--   Γ |- t ∈ T →
--   Γ' |- t ∈ T := by
--   intros Γ Γ' t T
--   intros HInc Ht
--   induction' Ht with Γ1 x T1 HΓ x T1 T2 t1 Γ1 HA IH T1 T2 Γ1 t1 t2 H H1 IH IH' Γ1 Γ1 Γ1 t1 t2 t3 T1 H H' H'' IH1 IH2 IH3
--   · apply has_type.T_Var
--     unfold includedin at HInc
--     apply HInc
--     exact HΓ
--   · apply has_type.T_Abs
--     unfold includedin at HInc
