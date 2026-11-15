From Stdlib Require Import List Bool ZArith.
From WMLR Require Import Expressions Languages Machine BufferRelations Separation RepairedSeparation
  GeneralizedFlushing FrameDecomposition OperationalSemantics ProgramSteps Assertions AssertionSemantics
  PersistentAssertions TemporalSafety SpatialExchange PrivateOwnership AssertionResourceEquivalence
  OwnedSafety BufferedPoolCandidate BufferedDekkerResources.
Import ListNotations BD.

(** A checked decision procedure for these finite, constant-address premises.
    The normalization theorem covers every satisfying resource and mark set;
    this is not an assumption justified by the earlier bounded search. *)
Module BDV.
Local Open Scope Z_scope.
Inductive operation := Store (second : bool) (loc : location) (v : Z)
  | Fence (second : bool) | Load (second : bool) (loc : location) (target : ident).
Definition writer op := match op with Store b _ _ |Fence b |Load b _ _ => actor b end.
Definition primitive op := match op with Store _ l v => S.Store (EVal (Z.pos l)) (EVal v)
  |Fence _ => S.Fence |Load _ l x => S.Load x (EVal (Z.pos l)) end.
Definition annotation op := EVal (Z.pos (writer op)).
Definition enqueue_image im (second : bool) loc v := Image (heap_cells im)
  (first_buffer im ++ if second then [] else [(loc,v)])
  (second_buffer im ++ if second then [(loc,v)] else []).
Definition run op im : option (image * option Z) := match op with
  |Store b l v => Some (enqueue_image im b l v,None)
  |Fence b => match buffers (mem im) (actor b) with [] => Some (im,None) |_ => None end
  |Load b l _ => match local_read (mem im) (actor b) (Z.pos l) with Some v => Some (im,Some v) |None => None end
  end.
Definition access_ok op im := match op with
  |Store b l _ |Load b l _ => match local_read (mem im) (actor b) (Z.pos l) with Some _ => true |None => false end
  |Fence _ => true end.
Definition result_stack op result s := match op,result with Load _ _ x,Some v => update s x v |_,_ => s end.
Definition result_ok op result := match op,result with
  |Load _ _ _,Some v => Z.eqb v 0 || Z.eqb v 1
  |Load _ _ _,None => false |_,None => true |_,Some _ => false end.
Definition postcondition op (post : option Z -> description) := match op with
  |Load _ _ x => A.Or (A.And (A.Pure (BEq (EVar x) (EVal 1))) (assertion (post (Some 1))))
      (A.And (A.Pure (BEq (EVar x) (EVal 0))) (assertion (post (Some 0))))
  |_ => assertion (post None) end.
Definition certificate invariant pre op post := checked invariant && plain pre && checked pre &&
  forallb (fun pool => if apart pool (only_image pre) then
    access_ok op (join pool (only_image pre)) &&
    match run op (join pool (only_image pre)) with
    |None => true
    |Some (after,value) => plain (post value) && checked (post value) && result_ok op value &&
      existsb (fun returned => apart returned (only_image (post value)) &&
        image_eqb (join returned (only_image (post value))) after) (images invariant)
    end else true) (images invariant).

Lemma read_equiv a b i address : memory_equiv a b -> local_read a i address = local_read b i address.
Proof.
  intros [Hh [Hb Hk]]; destruct address; try reflexivity.
  unfold local_read; rewrite Hb,Hh; reflexivity.
Qed.
Lemma enqueue_equiv a b i loc v : memory_equiv a b -> memory_equiv (enqueue a i loc v) (enqueue b i loc v).
Proof.
  intros [Hh [Hb Hk]]; split; [exact Hh |]. split; [|exact Hk].
  intros j; cbn; unfold buffer_update; destruct (Pos.eq_dec j i); rewrite Hb; reflexivity.
Qed.
Lemma enqueue_image_spec im second loc v :
  memory_equiv (enqueue (mem im) (actor second) loc v) (mem (enqueue_image im second loc v)).
Proof.
  split; [intros; reflexivity |]. split; [|intros; reflexivity].
  intros i; destruct second; unfold enqueue,actor,mem,enqueue_image; cbn; unfold buffer_update;
    destruct (Pos.eq_dec i 1%positive), (Pos.eq_dec i 2%positive); cbn; rewrite ?app_nil_r;
    try reflexivity; congruence.
Qed.
Lemma equiv_trans a b c : memory_equiv a b -> memory_equiv b c -> memory_equiv a c.
Proof. intros [Hh [Hb Hk]] [Hh' [Hb' Hk']]; split; [intros; rewrite Hh,Hh'; reflexivity |].
  split; [intros; rewrite Hb,Hb'; reflexivity |intros; rewrite Hk,Hk'; reflexivity]. Qed.

Lemma operation_abort op im s whole : memory_equiv whole (mem im) -> access_ok op im = true ->
  ~ abort active (C.Prim (C.Common (primitive op)) (annotation op)) (State s whole).
Proof.
  intros HE HC Hbad; inversion Hbad; subst.
  match goal with E : eval_expr s (annotation op) = Z.pos ?i |- _ =>
    change (Z.pos (writer op) = Z.pos i) in E; injection E as E; subst i end.
  destruct op; cbn [primitive] in *;
    match goal with H : primitive_abort _ _ _ _ |- _ => inversion H; subst end;
    unfold access_ok in HC; rewrite (read_equiv _ _ _ _ HE) in *; cbn [eval_expr writer] in *;
    match goal with H : local_read _ _ _ = None |- _ => rewrite H in HC; discriminate end.
Qed.

Lemma operation_step op im s whole action next t whole' : memory_equiv whole (mem im) ->
  program_step active action (C.Prim (C.Common (primitive op)) (annotation op)) (State s whole) next (State t whole') ->
  exists after value, run op im = Some (after,value) /\ memory_equiv whole' (mem after) /\
    t = result_stack op value s.
Proof.
  intros HE HS; inversion HS; subst.
  match goal with E : eval_expr s (annotation op) = Z.pos ?i |- _ =>
    change (Z.pos (writer op) = Z.pos i) in E; injection E as E; subst i end.
  destruct op; cbn [primitive] in *;
    match goal with H : primitive_step _ _ _ _ _ |- _ => inversion H; subst end; cbn [eval_expr writer] in *.
  - match goal with H : Z.pos _ = Z.pos _ |- _ => injection H as H; subst end.
    eexists; exists None; split; [reflexivity |]. split; [|reflexivity].
    eapply equiv_trans; [apply enqueue_equiv,HE |apply enqueue_image_spec].
  - exists im,None; split; [|auto]. unfold run.
    match goal with H : buffers _ _ = [] |- _ => rewrite (proj1 (proj2 HE)) in H; rewrite H; reflexivity end.
  - match goal with H : local_read _ _ _ = Some _ |- _ =>
      rewrite (read_equiv _ _ _ _ HE) in H; cbn [eval_expr] in H;
      exists im, (Some v); split; [unfold run; rewrite H; reflexivity |auto] end.
Qed.

Lemma post_model op post value s source owner Hmark :
  plain (post value) = true -> checked (post value) = true -> result_ok op value = true ->
  persistent_models active (result_stack op value s)
    (with_marks (only_image (post value)) source owner Hmark) (postcondition op post).
Proof.
  intros HP HC HV.
  pose proof (marked_image_models _ HP HC _ (only_image_in _) (result_stack op value s) source owner Hmark) as HM.
  destruct op; destruct value as [v'|]; cbn [result_ok] in HV; try discriminate; try exact HM.
  apply orb_true_iff in HV; destruct HV as [HV |HV]; apply Z.eqb_eq in HV; subst v'.
  - right; split; [|exact HM]. change (Z.eqb (update s target 0 target) 0 = true); rewrite update_same; reflexivity.
  - left; split; [|exact HM]. change (Z.eqb (update s target 1 target) 1 = true); rewrite update_same; reflexivity.
Qed.

Theorem certificate_sound invariant pre op post : certificate invariant pre op post = true ->
  buffered_atomic_premise active (assertion invariant) (assertion pre)
    (primitive op) (annotation op) (postcondition op post).
Proof.
  unfold certificate; rewrite !andb_true_iff; intros [[[CJ PP] CP] HC].
  split; [destruct op; exact I |]. intros s local pool whole HP HJ Hsp Hfree.
  destruct (spatial_free_parts _ _ _ Hsp Hfree) as [FJ FP].
  destruct HJ as (pool_resource & Epool & HJ).
  assert (Fpool : lock_free (resource_memory active pool_resource)) by (unfold resource_memory; rewrite Epool; exact FJ).
  destruct (models_image _ CJ _ _ HJ Fpool) as (pool_image & IP & EP).
  change (memory_equiv (underlying (proj1_sig pool_resource)) (mem pool_image)) in EP; rewrite Epool in EP; cbn in EP.
  destruct (models_image _ CP _ _ HP FP) as (private_image & IL & EL).
  rewrite (plain_images _ PP) in IL; destruct IL as [<- |[]].
  destruct (plain_mark _ PP _ _ HP) as (owner & Hmark).
  assert (HA : apart pool_image (only_image pre) = true).
  { apply apart_spec. exact (proj1 (proj1 (spatial_equiv _ _ _ _ _ _ EP EL (assertion_memory_equiv_refl _) Hsp))). }
  assert (HE : memory_equiv whole (mem (join pool_image (only_image pre)))).
  { apply (spatial_shape _ _ _ _ _ Hsp EP EL). unfold compatible; rewrite HA.
    destruct (plain_buffers _ PP _ (only_image_in _)) as [B1 B2]; rewrite B1,B2.
    destruct (first_buffer pool_image), (second_buffer pool_image); reflexivity. }
  rewrite forallb_forall in HC; specialize (HC pool_image IP); rewrite HA in HC.
  apply andb_true_iff in HC; destruct HC as [Haccess Hrun].
  split; [apply (operation_abort op _ s whole HE Haccess) |]. intros action next t whole' HS.
  destruct (operation_step _ _ _ _ _ _ _ _ HE HS) as (after & value & ER & EA & ET).
  rewrite ER in Hrun; rewrite !andb_true_iff in Hrun; destruct Hrun as [[[Ppost Cpost] Vpost] HX].
  apply existsb_exists in HX; destruct HX as (returned & IR & HX).
  apply andb_true_iff in HX; destruct HX as [Hapart Heq]; apply image_eqb_spec in Heq.
  pose (local' := with_marks (only_image (post value)) local owner Hmark).
  assert (Hsplit : memory_spatial (mem returned) (resource_memory active local') whole').
  { eapply spatial_equiv; [apply assertion_memory_equiv_refl |apply assertion_memory_equiv_refl | |apply join_spatial,Hapart].
    eapply equiv_trans; [exact Heq |apply assertion_memory_equiv_sym,EA]. }
  exists local', (mem returned); split; [exact Hsplit |]. split.
  - intros i H; apply (proj2 (proj2 EA) i) in H; exact H.
  - split.
    + exists (full returned); split; [reflexivity |apply image_models; assumption].
    + split.
      * rewrite ET; apply post_model; assumption.
      * constructor.
        -- intros loc HD; apply (spatial_merge_domain _ _ _ (proj2 Hsp)).
           apply (step_domain_subset _ _ _ _ _ (program_step_erases _ _ _ _ _ _ HS)).
           apply (spatial_merge_domain _ _ _ (proj2 Hsplit)); exact HD.
        -- intros i H; left; exact H.
Qed.
End BDV.
