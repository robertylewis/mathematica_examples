/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Show that "bounded" quantifiers: (∃x, x < n ∧ P x) and (∀x, x < n → P x)
are decidable when P is decidable.

This module allow us to write if-then-else expressions such as
  if (∀ x : nat, x < n → ∃ y : nat, y < n ∧ y * y = x) then t else s
without assuming classical axioms.

More importantly, they can be reduced inside of the Lean kernel.
-/

section
  open subtype nat

  attribute [reducible]
  definition bex (n : nat) (P : nat → Prop) : Prop :=
  ∃ x, x < n ∧ P x

  attribute [reducible]
  definition bsub (n : nat) (P : nat → Prop) : Type :=
  {x // x < n ∧ P x}

  attribute [reducible]
  definition ball (n : nat) (P : nat → Prop) : Prop :=
  ∀ x, x < n → P x

  lemma bex_of_bsub {n : nat} {P : nat → Prop} : bsub n P → bex n P :=
  assume h, exists_of_subtype h

  theorem not_bex_zero (P : nat → Prop) : ¬ bex 0 P :=
  λ ⟨w, Hw⟩, and.rec_on Hw (λ h₁ h₂, absurd h₁ (not_lt_zero w))
  

  theorem not_bsub_zero (P : nat → Prop) : bsub 0 P → false :=
  λ H, absurd (bex_of_bsub H) (not_bex_zero P)

  definition bsub_succ {P : nat → Prop} {n : nat} (H : bsub n P) : bsub (succ n) P :=
  subtype.rec_on H (λ w Hw, mk w (and.rec_on Hw (λ hlt hp, and.intro (lt.step hlt) hp)))

  theorem bex_succ {P : nat → Prop} {n : nat} : bex n P → bex (succ n) P :=
  λ ⟨w, Hw⟩, and.rec_on Hw (λ hlt hp, exists.intro w (and.intro (lt.step hlt) hp))

  definition bsub_succ_of_pred {P : nat → Prop} {a : nat} (H : P a) : bsub (succ a) P :=
  mk a (and.intro (lt.base a) H)

  theorem bex_succ_of_pred {P : nat → Prop} {a : nat} (H : P a) : bex (succ a) P :=
  bex_of_bsub (bsub_succ_of_pred H)

  theorem not_bex_succ {P : nat → Prop} {n : nat} (H₁ : ¬ bex n P) (H₂ : ¬ P n) : ¬ bex (succ n) P :=
  begin
   intro, cases a with w Hw, cases Hw with hltsn hp, 
   cases (nat.eq_or_lt_of_le (le_of_succ_le_succ hltsn)) with heq hltn,
   {apply H₂, simp * at *} ,
   {apply H₁, fapply exists.intro, apply w, split, repeat {assumption}}
  end
  
  theorem not_bsub_succ {P : nat → Prop} {n : nat} (H₁ : ¬ bex n P) (H₂ : ¬ P n) : bsub (succ n) P → false :=
  λ H, absurd (bex_of_bsub H) (not_bex_succ H₁ H₂)

  theorem ball_zero (P : nat → Prop) : ball 0 P :=
  λ x Hlt, absurd Hlt (not_lt_zero x)

  theorem ball_of_ball_succ {n : nat} {P : nat → Prop} (H : ball (succ n) P) : ball n P  :=
  λ x Hlt, H x (lt.step Hlt)

  theorem ball_succ_of_ball {n : nat} {P : nat → Prop} (H₁ : ball n P) (H₂ : P n) : ball (succ n) P :=
  λ (x : nat) (Hlt : x < succ n), or.elim (nat.eq_or_lt_of_le (le_of_succ_le_succ Hlt))
    (λ heq : x = n, by rw heq; apply H₂)
    (λ hlt : x < n, H₁ x hlt)

  theorem not_ball_of_not {n : nat} {P : nat → Prop} (H₁ : ¬ P n) : ¬ ball (succ n) P :=
  λ (H : ball (succ n) P), absurd (H n (lt.base n)) H₁

  theorem not_ball_succ_of_not_ball {n : nat} {P : nat → Prop} (H₁ : ¬ ball n P) : ¬ ball (succ n) P :=
  λ (H : ball (succ n) P), absurd (ball_of_ball_succ H) H₁

section
  open nat decidable

  instance decidable_bex (n : nat) (P : nat → Prop) [H : decidable_pred P] : decidable (bex n P) :=
  nat.rec_on n
    (is_false (not_bex_zero P))
    (λ a ih, decidable.rec_on ih
      (λ hneg : ¬ bex a P, decidable.rec_on (H a)
         (λ hna : ¬ P a, is_false (not_bex_succ hneg hna))
         (λ hpa : P a, is_true (bex_succ_of_pred hpa)))
      (λ hpos : bex a P, is_true (bex_succ hpos)))

  instance decidable_ball (n : nat) (P : nat → Prop) [H : decidable_pred P] : decidable (ball n P) :=
  nat.rec_on n
    (is_true (ball_zero P))
    (λ n₁ ih, decidable.rec_on ih
      (λ ih_neg, is_false (not_ball_succ_of_not_ball ih_neg))
      (λ ih_pos, decidable.rec_on (H n₁)
         (λ p_neg, is_false (not_ball_of_not p_neg))
         (λ p_pos, is_true (ball_succ_of_ball ih_pos p_pos))))

theorem lt_succ_iff_le (a b : ℕ) : a < (succ b) ↔ a ≤ b := 
⟨le_of_lt_succ, λ h, lt_of_le_of_lt h (lt_succ_self _)⟩

  instance decidable_bex_le (n : nat) (P : nat → Prop) [decidable_pred P]
    : decidable (∃ x, x ≤ n ∧ P x) :=
  decidable_of_decidable_of_iff
    (decidable_bex (succ n) P)
    (exists_congr (λn', and_congr (lt_succ_iff_le n' n) (iff.refl (P n'))))

 instance  decidable_ball_le (n : nat) (P : nat → Prop) [decidable_pred P]
    : decidable (∀ x, x ≤ n → P x) :=
  decidable_of_decidable_of_iff
    (decidable_ball (succ n) P)
    (forall_congr (λ n', imp_congr (lt_succ_iff_le n' n) (iff.refl (P n'))))
end

end
