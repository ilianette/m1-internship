Require Import Form.
Require Import Calculus.
Set Implicit Arguments.
Unset Strict Implicit.

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

  res : forall C w w', cov w C -> acc w w' -> exists Cw', cov w' Cw' /\ forall w1, Cw' w1 -> exists w2, C w2 /\ acc w2 w1;
  (* res : forall w C, cov w C -> (worlds -> Prop); *)
  (* res_mono : forall C w0 w1, (p : cov w0 C) -> acc w0 w1 -> cov w1 (res w1 C p); *)
  (* res_ext : forall C w1 w2, (p : cov w0 C)  -> res w1 C w2 p -> exists w3, C w3 /\ acc w3 w2; *)

  (* cov_union : forall C w, forall D : worlds -> worlds -> Prop, *)

  (*   cov w C -> *)
  (*   (forall wi, C wi -> cov wi (D wi)) *)
  (*   -> cov w (fun w' => exists wi, C wi /\ D wi w'); *)

  (* if C |> w and for every w' in C has a cover verifying property P, then the union-cover of w verifies P *)
  cov_union : forall w (P : worlds -> Prop) C,
    cov w C ->
    (forall w' : worlds, C w' -> exists Dw', cov w' Dw' /\ forall wi, Dw' wi -> P wi) ->
    exists U, cov w U /\ (forall w', U w' -> P w');
  cov_past2 : forall w x, (exists C, cov w C /\ forall w', C w' -> val x w') -> val x w;
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
  - intros H1 H2.
    destruct (res H2 H1) as [Cw' [Hcov Habs]]. eapply cov_ext.
    + intuition.
        specialize (Habs w0 H) as [_ [abs _]]. apply abs.
    + apply Hcov.
  - intuition eauto.
  - intros H (C & H1 & H2).
    destruct (res H1 H) as [Cw' [res_mono res_ext]].
    exists Cw'. split.
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
  - intros.
    destruct (res H H1) as [Cw' [res_mono res_ext]].
    eapply IHphi2.
    apply res_mono.
    intros v' Hv'.
    pose proof Hv' as Hv'2.
    apply res_ext in Hv' as (v & Hv &  Hvv').
    eapply H0; eauto.
    apply mono with (w:=w').
      + eapply cov_future; try eapply res_mono; eauto.
      + assumption.
Qed.

Definition tsat {M : BM} Γ w := forall ϕ, List.In ϕ Γ -> w ⊩ ϕ.

Lemma sem_expl {M : BM} : forall w ϕ,  w ⊩ ⊥ -> w ⊩ ϕ.
Proof.
  intros w ϕ Hbot.
  apply paste with (C := (fun _ => False)).
  apply Hbot.
  intros w' contra. exfalso. exact contra.
Qed.

Notation "w ⊩' Γ" := (tsat Γ w) (at level 98).


Lemma tsat_cons {M : BM} : forall w Γ ϕ, w ⊩' Γ -> w ⊩ ϕ -> w ⊩' ϕ :: Γ.
  intros w Γ ϕ HΓ Hϕ τ Hτ.
  destruct Hτ. rewrite <- H. apply Hϕ.
  apply HΓ. apply H.
Qed.


Theorem soundess Γ ϕ :
  Γ ⊢ ϕ -> forall (M : BM)  w, w ⊩' Γ -> w ⊩ ϕ.
Proof.
  intros Hϕ.
  induction Hϕ; intros M w Hw.
  - apply Hw, H.
  - apply IHHϕ in Hw.
    apply paste with (C := (fun _ => False)).
    apply Hw.
    intros w' contra. exfalso. exact contra.
  - intros w' Hacc Hw'.
    apply IHHϕ.
    apply tsat_cons.
    intros ι Hι.
    eapply mono; eauto.
    apply Hw'.
  - pose proof Hw as Hw2.
    apply IHHϕ1 in Hw.
    apply IHHϕ2 in Hw2.
    apply Hw.
    apply acc_refl.
    apply Hw2.
  - exists (eq w).
    split. apply cov_sing.
    intros w' H. rewrite <- H.
    left.
    apply IHHϕ. apply Hw.
  - exists (eq w).
    split. apply cov_sing.
    intros w' H. rewrite <- H.
    right.
    apply IHHϕ. apply Hw.
  - specialize (IHHϕ1 _ _ Hw) as [C [HCw HC]].
    eapply paste.
    apply HCw.
    intros w' H.
    pose proof H as HCw'.
    apply HC in H.
    destruct H as [Hwϕ | Hwψ].
    + apply IHHϕ2 with (w:=w'); auto.
      intros ι Hι.
      eapply mono; eauto.
      eapply cov_future; eauto.
      apply acc_refl.
    + eapply IHHϕ3; auto.
      intros ι Hι.
      eapply mono; eauto.
      eapply cov_future; eauto.
      apply acc_refl.
  - split;auto.
  - apply IHHϕ in Hw; destruct Hw; auto.
  - apply IHHϕ in Hw; destruct Hw; auto.
Qed.

Section UniversalModel.
  Inductive covers : (list form -> Prop) -> list form -> Prop :=
  | Triv : forall Γ C, (forall Γ', C Γ' <-> Γ' = Γ) -> covers C Γ
  | Empty : forall Γ C, Γ ⊢ ⊥ -> (forall Γ', C Γ' <-> False) -> covers C Γ
  | Union : forall C D E Γ ϕ ψ, Γ ⊢ ϕ ∨ ψ -> covers C (ϕ :: Γ) -> covers D (ψ :: Γ) -> (forall Δ, E Δ <-> C Δ \/ D Δ) -> covers E Γ.
Notation "C ▷ Γ" := (covers C Γ)(at level 98).

From Stdlib Require Import Program.Basics.

Program Instance universalModel : BM :=
  {
    worlds := list form;
    acc    := @List.incl form;
    val    := fun n => List.In (var n);
    cov    := flip covers;
  }.

Next Obligation.
Proof. apply List.incl_refl. Qed.

 Next Obligation.
Proof. eapply List.incl_tran. apply H. apply H0. Qed.

(*cov_future*)
Next Obligation.
Proof.
  rename w into Γ, w' into Γ', H into Hcov, H0 into H.
  induction Hcov.
  - rewrite (proj1 (H0 Γ') H). apply List.incl_refl.
  - specialize (H1 Γ'). exfalso. intuition.
  - apply (H1 Γ') in H.
    destruct H;
    [ specialize (IHHcov1 H) as H2 | specialize (IHHcov2 H) as H2];
      destruct (List.incl_cons_inv H2) as [_ goal]; assumption.
Qed.

Next Obligation.
Proof. constructor. intuition. Qed.

Next Obligation.
  cbv. cbv in H0.
  destruct H0.
  - apply Triv.
    intro Γ'.
    eapply iff_trans.
    apply iff_sym, (H Γ').
    apply H0.
  -
    apply Empty.
    apply H0.
    intro Γ'.
    eapply iff_trans.
    apply iff_sym, (H Γ').
    apply H1.
  - apply Union with (ϕ:=ϕ) (ψ:=ψ) (C := C) (D := D) .
    apply H0.
    apply H0_.
    apply H0_0.
    intro  Δ.
    eapply iff_trans.
    apply iff_sym, (H Δ).
    apply H1.
Qed.

Lemma incl_cons_cons : forall A l l' (x : A), List.incl l l' -> List.incl (x :: l) (x :: l').
Proof.
  intros.
  apply List.incl_cons. apply List.in_eq.
  apply List.incl_tl.
  apply H.
Qed.
Next Obligation.
Proof.
  rename w into Γ, w' into Γ', H into Hcov, H0 into Hincl.
  revert Γ' Hincl.
  induction Hcov; intros Γ' Hincl.
  - exists (eq Γ').
    split.
    + apply Triv. intuition.
    + intros; subst w1.
      exists Γ. split. specialize (H Γ). intuition. assumption.
  - exists (fun _ => False).
    split.
    + apply Empty. eapply weak. apply H. apply Hincl. intuition.
    + intros w1 abs. exfalso. apply abs.
  -  destruct (IHHcov1 (cons ϕ Γ') (incl_cons_cons Hincl)) as [G HG].
     destruct (IHHcov2 (cons ψ Γ') (incl_cons_cons Hincl)) as [F HF].
     exists (fun Δ => G Δ \/ F Δ).
     split.
     + apply Union with (C := G) (D := F) (ϕ:=ϕ) (ψ:=ψ).
       * eapply weak. apply H. apply Hincl.
       * apply HG.
       * apply HF.
       * intuition.
     + intros Δ HΔ.
       destruct HG as [_ HG], HF as [_ HF].
       destruct HΔ.
       * destruct (HG Δ H1) as [w2 Hw2].
          exists w2.
         split. apply H0. left. apply Hw2. apply Hw2.
       * destruct (HF Δ H1) as [w2 Hw2].
         exists w2.
         split. apply H0. right. apply Hw2. apply Hw2.
Qed.

From Stdlib Require Import Program.Equality.

Next Obligation.
Proof.
  induction H.
  - destruct (H0 Γ) as [DΓ HDΓ].
    { apply H. reflexivity. }
    exists DΓ. apply HDΓ.
  - exists (fun _ => False).
    split.
    + apply Empty. apply H. intuition.
    + intuition.
  - edestruct (IHcovers1) as [F HF].
    { intros Δ HΔ. apply H0. apply H3. left. apply HΔ. }
    edestruct (IHcovers2) as [G HG].
    { intros Δ HΔ. apply H0. apply H3. right. apply HΔ. }
    exists (fun Δ => F Δ \/ G Δ).
    split.
    + eapply Union with (C:=F) (D:=G).
      apply H. apply HF. apply HG. intros; apply iff_refl.
    + intros. destruct H4. apply HF. apply H4. apply HG. apply H4.
Qed.

Next Obligation.
Proof.
  induction H.
  - specialize (H Γ). apply H0. apply H. trivial.
  - assert ( Γ ⊢ var x ).
    { apply expl. apply H. }
    Admitted.
Section End.


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
