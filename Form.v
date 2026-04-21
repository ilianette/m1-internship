Inductive form : Type :=
| var : nat -> form
| bot : form
| conj : form -> form -> form
| disj : form -> form -> form
| impl : form -> form -> form.
(* | excl : form -> form -> form. *)

Notation "⊥" := bot.
Notation "¬ ϕ" := (impl ϕ ⊥) (at level 94, right associativity).
Infix "∧" := conj (right associativity, at level 95).
Infix "∨" := disj (left associativity, at level 96).
Infix "⊃" := impl (right associativity, at level 97). 
