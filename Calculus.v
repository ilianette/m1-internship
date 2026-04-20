From Stdlib Require Import Lists.List.


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
(*| disjE*)



where "Γ ⊢ ϕ" := (proves Γ ϕ).

Definition list_theory (Γ : list form) : theory :=
  fun φ => In φ Γ.

Coercion list_theory : list >-> theory.

Global Hint Constructors proves : core export.

(* should not prove this by hand *)
Lemma weakening ϕ Γ Δ :
  Γ ⊢ ϕ -> Γ ⊆ Δ -> Δ ⊢ ϕ.
  intro H. revert Δ.
  induction H; intros Δ Hin; eauto.
  - apply axiom.
    specialize (Hin ϕ).
    apply Hin, H.
  - apply impI.
    apply IHproves.
    unfold list_theory.
    intros τ H1. inversion H1.
    + left. apply H0.
    + right.
      apply Hin.
      apply H0.
Qed.
