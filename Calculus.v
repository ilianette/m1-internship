From Stdlib Require Import Lists.List Sorting.Permutation.
Require Import Form.

Inductive form : Type :=
| var : nat -> form
| bot : form
| conj : form -> form -> form
| disj : form -> form -> form
| impl : form -> form -> form.


Notation "⊥" := bot.
Notation "¬ ϕ" := (impl ϕ ⊥) (at level 94, right associativity).
Infix "∧" := conj (right associativity, at level 95).
Infix "∨" := disj (left associativity, at level 96).
Infix "⊃" := impl (right associativity, at level 97).

Definition theory := form -> Prop.
Implicit Type Γ Δ : list form.
Implicit Type T U: theory.
Implicit Types ϕ ψ: form.
Definition subset T U := forall ϕ, T ϕ -> U ϕ.
Notation "A ⊆ B" := (subset A B) (at level 10).


Reserved Notation "Γ ⊢ ϕ" (at level 98).
Reserved Notation "Γ |- ϕ" (at level 98).
Inductive proves : list form -> form -> Prop :=
| axiom  : forall Γ ϕ, In ϕ Γ -> Γ ⊢ ϕ
| expl   : forall Γ ϕ, Γ ⊢ ⊥ -> Γ ⊢ ϕ

| impI   : forall Γ ϕ ψ, ϕ :: Γ ⊢ ψ -> Γ ⊢ ϕ ⊃ ψ
| impE   : forall Γ ϕ ψ, Γ ⊢ ϕ ⊃ ψ -> Γ ⊢ ϕ -> Γ ⊢ ψ
| disjI1 : forall Γ ϕ ψ, Γ ⊢ ϕ -> Γ ⊢ ϕ ∨ ψ
| disjI2 : forall Γ ϕ ψ, Γ ⊢ ψ -> Γ ⊢ ϕ ∨ ψ
| disjE  : forall Γ ϕ ψ γ, Γ ⊢ ϕ ∨ ψ -> Γ ⊢ ϕ ⊃ γ -> Γ ⊢ ψ ⊃ γ -> Γ ⊢ γ
| conjI  : forall Γ ϕ ψ, Γ ⊢ ϕ -> Γ ⊢ ψ -> Γ ⊢ ϕ ∧ ψ
| conjE1 : forall Γ ϕ ψ, Γ ⊢ ϕ ∧ ψ -> Γ ⊢ ϕ
| conjE2 : forall Γ ϕ ψ, Γ ⊢ ϕ ∧ ψ -> Γ ⊢ ψ

where "Γ ⊢ ϕ" := (proves Γ ϕ).

Definition list_theory (Γ : list form) : theory :=
  fun φ => In φ Γ.

Coercion list_theory : list >-> theory.

Definition mem T ϕ := T ϕ.
Definition provesP T ϕ :=
  exists (L : list form) , (forall ψ, mem L ψ -> T ψ) /\ proves L ϕ.


Notation "Γ ⊢P ϕ" := (provesP Γ ϕ) (at level 98).
Global Hint Constructors proves : core export.

(* Lemma weakeningP ϕ Γ Δ : *)
(*   Γ ⊢P ϕ -> Γ ⊆ Δ -> Δ ⊢P ϕ. *)
(* Proof. *)
(*   intros. *)
(*   destruct H as [L [H1 H2]]. *)
(*   exists L. *)
(*   auto. *)
(* Qed. *)



(* should not prove this by hand *)
Lemma weakening ϕ Γ Δ :
  Γ ⊢ ϕ -> Γ ⊆ Δ -> Δ ⊢ ϕ.
  intro H. revert Δ. induction H; intros Δ Hin; unfold list_theory in Hin; eauto.
  - apply impI.
    apply IHproves.
    intros τ H1. inversion H1; unfold list_theory; [left | right]; auto.
Qed.

Lemma reorder ϕ Γ Δ:
  Γ ⊢ ϕ -> Permutation Γ Δ -> Δ ⊢ ϕ.
Proof.
  intro H. revert Δ. induction H; eauto 5.
  - intros Δ Hperm.
    apply axiom.
    eapply Permutation_in. apply Hperm. apply H.
Qed.

Lemma weak ϕ Γ Δ :
  Γ ⊢ ϕ -> (forall τ, In τ Γ -> In τ Δ) -> Δ ⊢ ϕ.
Proof.
  intro H. revert Δ. induction H; eauto.
  - intros.
    apply impI.
    apply IHproves.
    intros τ H1. inversion H1; [left | right]; auto.
Qed.
