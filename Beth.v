Require Import Form.
Require Import Calculus.

Class BM : Type :=
{
  worlds : Type;
  acc : worlds -> worlds -> Prop;

  acc_refl : forall w, acc w w;
  acc_tran : forall w1 w2 w3, acc w1 w2 -> acc w2 w3 -> acc w1 w3;

  val : nat -> worlds -> Prop;
  val_mono : forall x w w', acc w w' -> val x w -> val x w';

  cov : worlds -> (worlds -> Prop) -> Prop;
  cov_future : forall C w w', cov w C -> C w' -> acc w w';
  cov_sing : forall w, cov w (eq w);
  (* covers are set*)
  cov_ext : forall C C', (forall w, C w <-> C' w) -> forall w, cov w C -> cov w C';

  res : worlds -> (worlds -> Prop) -> (worlds -> Prop);
  res_mono : forall C w0 w1, cov w0 C -> acc w0 w1 -> cov w1 (res w1 C);
  res_ext : forall C w1 w2, res w1 C w2 -> exists w3, C w3 /\ acc w3 w2;

  (* cov_union : forall C w, forall D : worlds -> worlds -> Prop, *)

  (*   cov w C -> *)
  (*   (forall wi, C wi -> cov wi (D wi)) *)
  (*   -> cov w (fun w' => exists wi, C wi /\ D wi w'); *)

  (* if C |> w and for every w' in C has a cover verifying property P, then the union-cover of w verifies P *)
  cov_union : forall w (P : worlds -> Prop) C,
    cov w C ->
    (forall w' : worlds, C w' -> exists Dw', cov w' Dw' /\ forall wi, Dw' wi -> P wi) ->
    exists U, cov w U /\ (forall w', U w' -> P w');
  cov_paste : forall C w x, cov w C -> (forall w', C w' -> val x w') -> val x w;
}.



Fixpoint bsat {M : BM} (w : worlds) (phi : form) :=
  match phi with
  | var x => val x w
  | bot => cov w (fun _ => False)
  | conj phi psi => bsat w phi /\ bsat w psi
  | disj phi psi => exists C, cov w C /\ forall w', C w' -> (bsat w' phi \/ bsat w' psi)
  | impl phi psi => forall w', acc w w' -> bsat w' phi -> bsat w' psi
  (* | excl phi psi => exists C w', cov w' C /\ C w /\ acc w' w /\ bsat w' phi /\ ~ bsat w' psi *)
  end.

Notation "w ⊩ ϕ" := (bsat w ϕ) (at level 98).

Lemma mono {M : BM} w w' phi :
  acc w w' -> bsat w phi -> bsat w' phi.
Proof.
  induction phi in w, w' |-*; cbn.
   - apply val_mono.
    - intros H1 H2.  eapply cov_ext; try eapply res_mono; eauto.
      intuition. apply res_ext in H. firstorder.
  - intuition eauto.
  - intros H (C & H1 & H2). exists (res w' C). split.
    + eapply res_mono; eauto.
    + intros w1 (w2 & H3 & H4) % res_ext. apply H2 in H3. intuition eauto.
  - clear IHphi1 IHphi2. intros. apply H0; try eapply acc_tran; eauto.
  (* - intros H (C & w1 & H1 & H2 & H3 & H4 & H5).
    exists C, w1. repeat split; trivial. *)
Qed.

Lemma paste {M : BM} w phi C :
  cov w C -> (forall w', C w' -> bsat w' phi) -> bsat w phi.
Proof.
  induction phi in w, C |-*; cbn.
  - apply cov_paste.
  - intros H H'.
    assert (exists U, cov w U /\ forall w', U w' -> False) as [U [HU1 HU2]].
    { eapply cov_union.
      + eassumption.
      + intros. exists (fun _ => False). auto.
    }
    apply cov_ext with (C := U); intuition; firstorder.
  - intros H1 H2. split.
    + eapply IHphi1; firstorder eauto.
    + eapply IHphi2; firstorder eauto.
  - intros H1 H2.
    eapply cov_union. apply H1.
    intros w' Cw'.
    specialize (H2 w' Cw') as [Dw' [H3 H4]].
    eauto.
  - intros. eapply IHphi2.  apply res_mono with (w0 := w). apply H. apply H1.
    intros v' Hv'.
    pose proof Hv' as Hv'2.
    apply res_ext in Hv' as (v & Hv &  Hvv').
    eapply H0; eauto.
    apply mono with (w:=w').
      + eapply cov_future; try eapply res_mono; eauto.
      + assumption.
Qed.

Definition tsat {M : BM} Γ w := forall ϕ, List.In ϕ Γ -> w ⊩ ϕ.


Notation "w ⊩' Γ" := (tsat Γ w) (at level 98).
Theorem soundess Γ ϕ :
  Γ ⊢ ϕ -> forall (M : BM)  w, w ⊩' Γ -> w ⊩ ϕ.
Proof.
Admitted.

(* Lemma excl_check1 {M : BM} w A B :
  bsat w (impl A (disj B (excl A B))).
Proof.
  intros w' H H'. exists (eq w'). split.
  - apply cov_sing.
  - intros w'' <-. admit.
Admitted.

Lemma excl_check2 {M : BM} A B C :
  (forall w, bsat w (impl A (disj B C))) -> forall w, bsat w (impl (excl A B) C).
Proof.
  intros H w1 w2 H1 (P & w3 & H2 & H3 & H4 & H5 & H6).
  apply (H w3) in H5 as (Q & H7 & H8); fold bsat in *.
Admitted. *)
