Inductive form : Type :=
| var : nat -> form
| bot : form
| conj : form -> form -> form
| disj : form -> form -> form
| impl : form -> form -> form.
(* | excl : form -> form -> form. *)
Inductive Empty : Type :=.

Class BM : Type :=
{
  worlds : Type;
  acc : worlds -> worlds -> Prop;

  acc_refl : forall w, acc w w;
  acc_tran : forall w1 w2 w3, acc w1 w2 -> acc w2 w3 -> acc w1 w3;

  val : nat -> worlds -> Prop;
  val_mono : forall x w w', acc w w' -> val x w -> val x w';

  cov : worlds -> (worlds -> Type) -> Prop;
  cov_future : forall C w w', cov w C -> C w' -> acc w w';
  cov_sing : forall w, cov w (eq w);
  (* covers are set*)
  cov_ext : forall C C', (forall w, C w -> C' w * C' w -> C w) -> forall w, cov w C -> cov w C';

  cov_dec : forall (C : worlds -> Type) (w : worlds), C w + (C w -> Empty);

  res : worlds -> (worlds -> Type) -> (worlds -> Prop);
  res_mono : forall C w0 w1, cov w0 C -> acc w0 w1 -> cov w1 (res w1 C);
  res_ext : forall C w1 w2, res w1 C w2 -> {w3 : worlds & {_ : C w3 | acc w3 w2} };


  cov_union : forall C w, forall D : worlds -> worlds -> Type,
    (forall wi, C wi -> cov wi (D wi))
    -> cov w (fun w' => { wi : worlds & prod (C wi) ( D wi w')}) ;

  cov_paste : forall C w x, cov w C -> (forall w', C w' -> val x w') -> val x w;
}.

Fixpoint bsat {M : BM} (w : worlds) (phi : form) : Type :=
  match phi with
  | var x => val x w
  | bot => cov w (fun _ => False)
  | conj phi psi => bsat w phi * bsat w psi
  | disj phi psi => sigT (fun C : worlds -> Type => prod (cov w C) (forall w', C w' -> (bsat w' phi + bsat w' psi)))
  | impl phi psi => forall w', acc w w' -> bsat w' phi -> bsat w' psi
  (* | excl phi psi => exists C w', cov w' C /\ C w /\ acc w' w /\ bsat w' phi /\ ~ bsat w' psi *)
  end.

(* Lemma test {M : BM} ψ ϕ C : (forall w', C w' -> bsat w' ψ + bsat w' ϕ) -> (exists w', C w') -> exists w',  prod (C w') (bsat w' ψ). *)

Lemma mono {M : BM} w w' phi :
  acc w w' -> bsat w phi -> bsat w' phi.
Proof.
  induction phi in w, w' |-*; cbn.
   - apply val_mono.
    - intros H1 H2.  eapply cov_ext; try eapply res_mono; eauto.
      (* intuition. apply res_ext in H. firstorder. *)
  - intuition eauto.
  - intros H (C & H1 & H2). exists (res w' C). split.
    + eapply res_mono; eauto.
    + intros w1 (w2 & H3 & H4) % res_ext. apply H2 in H3. intuition eauto.
  - clear IHphi1 IHphi2. intros . apply X; try eapply acc_tran; eauto.
  (* - intros H (C & w1 & H1 & H2 & H3 & H4 & H5).
    exists C, w1. repeat split; trivial. *)
Qed.



Lemma paste {M : BM} w phi C :
  cov w C -> (forall w', C w' -> bsat w' phi) -> bsat w phi.
Proof.
  induction phi in w, C |-*; cbn.
  - apply cov_paste.
  - intros H H'.
    eapply cov_union in H'.
    eapply (cov_ext (fun _ => { wi & C wi * False})); intuition; firstorder; eassumption.
  - intros H1 H2. split.
    + eapply IHphi1; firstorder eauto.
    + eapply IHphi2; firstorder eauto.
  - intros H1 H2.
    assert ({D : worlds -> worlds -> Type &
                (forall w', C w' -> cov w' (D w')) *
                (forall w', C w' -> forall w'0, (D w' w'0) ->
                                     bsat w'0 phi1 + bsat w'0 phi2)
           }).
    {
    exists (fun w => match cov_dec C w with
             | inl proof =>
                 match (H2 w proof) with
                 | existT _ Pw (p1 , p2) => Pw
                 end
             | inr nCw => fun _ => False
                    (* | inr nCw => (fun w' Cw => principle-of-explosion (nCw cw)) *)
             end).
    split;     intro w';     destruct (cov_dec C w') as [HwC | HnC].
    * destruct (H2 w' HwC).
      destruct p as [p1 _]. intros _; apply p1.
    * intro abs. apply HnC in abs. contradiction.
    * destruct (H2 w'). destruct p as [_ p2]. intro c . apply p2.
    * intros; contradiction.
    }
    destruct X as [D [HD1 HD2]].
    eexists.
    split.
    +
      eapply cov_union with (C := C) (D:=D).
      intros w' Hw'.
      apply HD1. apply Hw'.
    + intros w' [wi [H4 H5]]. apply HD2 with (w':=wi). apply H4. apply H5.
(*       destruct (H2 w' Hw') as [Dw' [HDw' Hϕ]]. *)
      
(*       { admit. }  *)
(*       rewrite <- H. *)
(*       apply HDw'. *)
(*     + intros w' H. *)
(*       destruct H as [wi [ Cwi H3]]. *)

      
(*   exact H3. *)
(*       * destruct (H2 wi Hcov) as [C' [Hcov' Hdec]]; simpl in H3. *)
(*         unfold D in H3. *)
(*         cbn in H3. *)
(*         apply Hdec in H3. *)
(*       destruct (cov_dec C wi) as [Hcov | Hnocov]. *)
(*       * *)
(*       destruct (H2 wi Hcov) as [C' [Hcov' Hdec]]. *)
(*       simpl in H3. *)
(*       apply Hdec. *)
(*       assumption. *)
(* - exfalso. *)
(*   apply Hnocov. *)
(*   exact Cwi. *)

 
(*     split. *)
(*     +  *)
(*       eapply cov_union. intros w' Hw'. admit. (* specialize (H2 w' Hw'). destruct H2 as [Pw' [HPw' Hphi]]. admit. *) *)
(*     +  *)

(*       specialize (H2 w' H). destruct H2 as [Pw' [HPw' Hphi]]. apply Hphi. admit. *)
   
  - intros. eapply IHphi2.  apply res_mono with (w0 := w). apply H. apply H0.
    intros v' Hv'.
    pose proof Hv' as Hv'2.
    apply res_ext in Hv' as (v & Hv &  Hvv').
    eapply X; eauto.
    apply mono with (w:=w').
      + eapply cov_future; try eapply res_mono; eauto.
      + assumption.
Qed.



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
