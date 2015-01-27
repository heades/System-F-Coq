(* Author: Harley Eades
 *
 * Coq Version: 8.3pl3 
 *
 * This file contains results related to substitution (subst_t). *)
Require Import Arith.
Require Import List.
Require Import F.
Require Import names.

Lemma trm_app_eq : forall t1 t2 t'1 t'2,
  t1 = t'1 ->
  t2 = t'2 -> trm_app t1 t2 = trm_app t'1 t'2.
Proof.
  intros; subst; eauto.
Qed.

Lemma subst_free_t : forall (x:nat) (u t:trm),
  ~ (free_in_t x t) -> subst_t u x t = t.
Proof.
  induction t; intros; simpl in *; eauto.
  clarify_compares_natc; subst; simpl in *; eauto.
  unfold free_in_t in H. contradict H; simpl; eauto.

  rewrite -> IHt; auto.
  rewrite -> IHt; auto.
  
  unfold free_in_t in H. 
  rewrite -> IHt1; unfold free_in_t; eauto.
  rewrite -> IHt2; unfold free_in_t; eauto.

  rewrite -> IHt; auto.
Qed.

Lemma subst_open_t : forall t u w x,
  lc u ->
  subst_t u x (open_t 0 w t) = open_t 0 (subst_t u x w) (subst_t u x t).
Proof.
  intros. generalize 0. induction t; intros; simpl; f_equal; auto;
  clarify_compares_natc; subst; simpl; eauto with naming_open.
Qed.
Hint Resolve subst_open_t : naming_open.

Lemma subst_id : forall t' t x,
  ~ In x (FV_t t') -> subst_t t x t' = t'.
Proof.
  induction t'; intros; simpl; eauto.
  clarify_compares_natc; auto.
  subst. contradict H. simpl. eauto.
  rewrite -> IHt'; auto.

  rewrite -> IHt'; auto.

  rewrite -> IHt'1; eauto.
  rewrite -> IHt'2; eauto.

  rewrite -> IHt'; auto.
Qed.

Lemma subst_open_var_t : forall (y x:nat) (u t:trm),
  lc u ->
  (trm_fvar x) <> (trm_fvar y) -> 
  subst_t u x (open_t 0 (trm_fvar y) t) = open_t 0 (trm_fvar y) (subst_t u x t).
Proof.
  intros. rewrite -> subst_open_t; auto.
  rewrite -> subst_id; auto.
  simpl. unfold not; intros. destruct H1; auto.
Qed.

Lemma subst_id' : forall t x, subst_t (trm_fvar x) x t = t.
Proof.
  induction t; intros; simpl; eauto.
  
  clarify_compares_natc; subst; auto.

  rewrite -> IHt. auto.
  rewrite -> IHt; auto.
  rewrite -> IHt1. rewrite -> IHt2. auto.
  rewrite -> IHt; auto.
Qed.

Lemma close_open_alpha_neq : forall t,
  lc t ->
  forall n x y,
    y <> x ->
    open_t n (trm_fvar y) (close_t n x t) = subst_t (trm_fvar y) x t.
Proof.
  intros t H. induction H; intros; simpl;
  try apply_ccn; auto.

  apply trm_lam_eq_lc with (L:=L++x::y::nil); intros.
  rewrite open_comm at 1; destruct_nin; simpl in *; auto.
  rewrite <- close_id with (t:=trm_fvar y0) (n:=S n) (x:=x) at 1; [ | simpl; omega].
  rewrite <- close_open_comm; [| auto | simpl; omega].
  rewrite -> H1; auto.
  rewrite -> subst_open_t; auto.
  rewrite -> subst_id at 1; auto; simpl; omega.
  
  apply f_equal; auto.
  
  rewrite -> IHlc1; auto.
  rewrite -> IHlc2; auto.

  rewrite -> IHlc; auto.
Qed. 

Lemma close_open_alpha : forall t,
  lc t ->
  forall n y x, open_t n (trm_fvar y) (close_t n x t) = subst_t (trm_fvar y) x t.
Proof.
  intros. case_split_names y x. 
  rewrite -> subst_id'. apply close_open_id; auto.

  apply close_open_alpha_neq; auto with arith.
  apply close_open_alpha_neq; auto with arith.
Qed.

Lemma close_alpha_conv : forall t y z,
  ~ In y (FV_t t) -> close_t 0 z t = close_t 0 y (subst_t (trm_fvar y) z t).
Proof.
  intros t y z. generalize t 0 y z. clear t y z.
  induction t; intros; simpl; 
    try apply_ccn; auto; try smash_contra.

  rewrite -> IHt with (y:=y); auto.

  rewrite -> IHt with (y:=y); auto.

  rewrite -> IHt1 with (y:=y); eauto.
  rewrite -> IHt2 with (y:=y); eauto.

  rewrite -> IHt with (y:=y); auto.
Qed.

Lemma app_eq_subst : forall t1 t2 x,
  ~ In x (FV_t t1++FV_t t2) ->
  trm_app t1 t2 = subst_t t1 x (trm_app (trm_fvar x) t2).
Proof.
  intros. simpl. 
  rewrite -> nat_compare_eq_eq.
  rewrite -> subst_free_t; auto.
Qed.

Lemma subst_open_eq : forall t t' L,
  let y := pick_fresh (L++FV_t t) in 
    open_t 0 t' t = subst_t t' y (open_t 0 (trm_fvar y) t).
Proof.
  intros t t' L y. unfold y. clear y. generalize t t' L 0.
  clear t t' L.
  induction t; intros; simpl; eauto; try apply_ccn; eauto.
  
  contradict Heqc; eauto.

  rewrite -> IHt with (L:=L); auto.

  rewrite -> IHt with (L:=L); auto.

  rewrite -> IHt1 with (L:=L++FV_t t2). 
  rewrite -> IHt2 with (L:=L++FV_t t1).
  
  apply trm_app_eq. 

  rewrite -> pick_fresh_eq'. repeat rewrite <- app_assoc. auto.
  repeat rewrite <- app_assoc. auto.

  rewrite -> IHt with (L:=L); auto.
Qed.

Lemma subst_open_t_gen : forall t u w x n,
  lc u ->
  subst_t u x (open_t n w t) = open_t n (subst_t u x w) (subst_t u x t).
Proof.
  induction t; intros; simpl; f_equal; auto;
    clarify_compares_natc; subst; simpl; eauto with naming_open.
Qed.

Lemma subst_open_eq_gen : forall t t' y n,
  ~ In y (FV_t t) -> 
  open_t n t' t = subst_t t' y (open_t n (trm_fvar y) t).
Proof.
  induction t; intros; simpl; eauto; try apply_ccn.

  rewrite -> IHt with (y:=y); auto; simpl in H; auto.
  
  apply f_equal; auto.

  simpl FV_t in *. destruct_nin.
  rewrite -> IHt1 with (y:=y); auto.
  rewrite -> IHt2 with (y:=y); auto.

  rewrite -> IHt with (y:=y); auto.
Qed.

Lemma open_alpha_subst : forall t' t x y n,
  ~ In x (FV_t t') ->
  ~ In y (FV_t t') ->    
  open_t n (trm_fvar x) t' = t ->
  open_t n (trm_fvar y) t' = (subst_t (trm_fvar y) x t).
Proof.
  induction t'; intros; simpl; try apply_ccn; try (simpl; apply_ccn). 
  
  simpl in H1; subst; simpl; apply_ccn.
  
  simpl in H1; subst.  simpl.
  rewrite <- subst_open_eq_gen with (y:=x); auto.

  simpl in *; subst; simpl; apply f_equal; auto.
  
  apply open_app in H1. subst. simpl in *. destruct_nin.
  rewrite <- IHt'1 with (t:=open_t n (trm_fvar x) t'1) (x:=x) (n:=n); auto.
  rewrite <- IHt'2 with (t:=open_t n (trm_fvar x) t'2) (x:=x) (n:=n); auto.

  simpl in *. invert_typing H1; simpl.
  Lemma trm_tapp_eq : forall t t' T T',
    t = t' ->
    T = T' ->
    trm_tapp t T = trm_tapp t' T'.
  Proof.
    intros; subst; auto.
  Qed.
  apply trm_tapp_eq; auto.
  
  simpl in H1; subst; auto.
Qed.

Lemma open_alpha_eq_subst : forall t t' z y,
  ~ In z (FV_t t) ->
  ~ In y (FV_t t) ->
  open_t 0 (trm_fvar z) t = t' ->
  open_t 0 (trm_fvar y) t = subst_t (trm_fvar y) z t'.
Proof.
  induction t; intros. 
  case_split_names n 0; simpl in *; apply_ccn; simpl; auto.
  simpl in *; subst; simpl; apply_ccn.
  
  simpl in *. subst. simpl.
  
  rewrite -> subst_open_t_gen; auto.
  simpl. rewrite -> nat_compare_eq_eq. rewrite -> subst_id; intuition eauto.

  simpl in *; subst; simpl; apply f_equal; auto.

  simpl in *; apply open_app in H1; subst; simpl.
  rewrite -> IHt1 with (t':=open_t 0 (trm_fvar z) t1) (z:=z); auto.
  rewrite -> IHt2 with (t':=open_t 0 (trm_fvar z) t2) (z:=z); auto.

  simpl in *; subst; simpl.
  apply trm_tapp_eq; auto.

  simpl in *; subst; intuition.
Qed.

Lemma subst_close_comm : forall t x y z n,
  x <> z ->
  x <> y ->
  close_t n x (subst_t (trm_fvar y) z t) = subst_t (trm_fvar y) z (close_t n x t).
Proof.
  induction t; intros; simpl; auto.
  
  apply_ccn. 
  
  rewrite -> IHt; auto.
  
  rewrite -> IHt; auto.
  
  rewrite -> IHt1; auto. rewrite IHt2; auto.

  rewrite -> IHt; auto.  
Qed.

Lemma el_nin_fv_subst : forall t x y z,
  x <> y ->
  x <> z ->
  ~ In x (FV_t (subst_t (trm_fvar y) z t)) ->
  ~ In x (FV_t t).
Proof.
  induction t; intros. simpl in *. auto.

  simpl in H1. remember (nat_compare z n). destruct c; auto. apply eq_sym in Heqc.
  apply nat_compare_eq in Heqc. subst. intuition. simpl in H2. destruct H2; eauto. 

  simpl. apply IHt with (y:=y) (z:=z); auto.
  simpl in *. apply IHt with (y:=y) (z:=z); auto.

  simpl. apply el_nin_conj_2. split.
  apply IHt1 with (y:=y) (z:=z); auto.
  simpl in H1. destruct_nin*.
  apply IHt2 with (y:=y) (z:=z); auto.
  simpl in H1. destruct_nin*. 

  simpl in *. apply IHt with (y:=y) (z:=z); auto.

  simpl in H1. auto.
Qed.

Lemma subst_lc : forall t',
  lc t' ->
  forall x t, 
    lc t ->
    lc (subst_t t x t').
Proof.
  induction 1; intros; simpl; eauto.
  
  apply_ccn.

  apply lc_lam with (L:=x::L++FV_t t0); intros; auto.
  rewrite <- subst_id with (t':=trm_fvar x0) (t:=t0) (x:=x).
  rewrite <- subst_open_t; auto. eauto.
  destruct_nin. simpl in *. unfold not; intros. destruct H6; auto; subst.
Qed.

Lemma open_eq_subst : forall t t1 t2 x y n,
  ~ In y (x::FV_t t) ->
  ~ In x (FV_t t) ->
  t1 = open_t n (trm_fvar x) t ->
  t2 = open_t n (trm_fvar y) t ->
  t2 = subst_t (trm_fvar y) x t1.
Proof.
  induction t; intros. 
  simpl in H1; simpl in H2. 
  case_split_names n n0; simpl. rewrite -> nat_compare_eq_eq; auto.
  subst; simpl; auto. subst; simpl; auto.
  subst; simpl. simpl FV_t in *. 
  apply_ccn.

  subst; simpl;
    rewrite -> IHt with
      (t1:=open_t (S n) (trm_fvar x) t)
      (t2:=open_t (S n) (trm_fvar y) t)
      (x:=x)
      (y:=y)
      (n:=S n); auto.
  
  subst; simpl; 
    rewrite -> IHt with
      (t1:=open_t n (trm_fvar x) t)
      (t2:=open_t n (trm_fvar y) t)
      (x:=x)
      (y:=y)
      (n:=n); auto.  

  subst; simpl; simpl FV_t in *; destruct_nin.
  rewrite -> IHt1 with
    (t2:=open_t n (trm_fvar x) t1)
    (t3:=open_t n (trm_fvar y) t1)
    (x:=x)
    (y:=y)
    (n:=n); auto.
  rewrite -> IHt2 with
    (t1:=open_t n (trm_fvar x) t2)
    (t3:=open_t n (trm_fvar y) t2)
    (x:=x)
    (y:=y)
    (n:=n); auto.
  rewrite list_cons_eq_app; apply el_nin_conj_2; split; auto.
  rewrite list_cons_eq_app; apply el_nin_conj_2; split; auto.
  
  simpl in *; subst.
  simpl.
  rewrite -> IHt with
    (t1:=open_t n (trm_fvar x) t)
    (t2:=open_t n (trm_fvar y) t)
    (x:=x)
    (y:=y)
    (n:=n); auto.

  subst; simpl; auto.
Qed.

Lemma subst_close_comm_gen : forall t t' x z n,
  x <> z ->
  ~ In x (FV_t t') ->
  close_t n x (subst_t t' z t) = subst_t t' z (close_t n x t).
Proof.
  induction t; intros; eauto; simpl; 
    try (apply_ccn; [ apply close_id; auto | apply close_id; auto]).
  
  rewrite -> IHt; auto.
  rewrite -> IHt; auto.
  rewrite -> IHt1; auto. rewrite IHt2; auto.           
  rewrite -> IHt; auto.
Qed.

Lemma close_eq_close_alpha : forall t y x n,
  ~ In y (x ::FV_t t) ->
  close_t n x t = close_t n y (subst_t (trm_fvar y) x t).
Proof.
  induction t; intros; auto; simpl; simpl FV_t in H.
  apply_ccn. 
  
  rewrite -> IHt with (y:=y); auto.
  rewrite -> IHt with (y:=y); auto.

  simpl FV_t in *; rewrite list_cons_eq_app in H; destruct_nin.
  rewrite -> IHt1 with (y:=y); auto.
  rewrite -> IHt2 with (y:=y); auto.
  rewrite list_cons_eq_app. apply el_nin_conj_2. split; auto.
  rewrite list_cons_eq_app. apply el_nin_conj_2. split; auto.

  rewrite -> IHt with (y:=y); auto.
Qed.

Ltac not_in_var_var :=
  match goal with
    | [|- ~ In ?x (FV_t (trm_fvar ?y)) ] =>
      match goal with
        | [H : ~ In y (x :: _) |- _] =>
          let new_var := fresh "H" in 
            unfold not; intro new_var; simpl in *;
              destruct new_var; simpl; auto
      end
  end.
Hint Extern 5 (~ In _ _) => not_in_var_var.

Lemma close_open_subst_gen : forall t ,
  lc t ->
  forall t' n x, lc t' -> open_t n t' (close_t  n x t) = subst_t t' x t.
Proof.
  induction 1; intros; simpl; auto; try apply_ccn.
  
  apply trm_lam_eq_lc with (L:=x::L++FV_t t'); intros.
  destruct_nin.
  rewrite -> open_comm'; auto.      
 
  rewrite <- close_id with (t:=trm_fvar y) (x:=x) (n:=S n) at 1; auto.
  rewrite <- close_open_comm; auto with arith; auto.
  rewrite <- subst_id with (t':=trm_fvar y) (t:=t') (x:=x) at 2; auto.

  rewrite <- subst_open_t; auto.
  
  apply f_equal; auto.

  apply trm_app_eq; eauto.
  apply trm_tapp_eq; auto.
Qed.

Lemma lc_open_inst : forall x t t' L n,
  lc t' ->
  ~ In x (L++FV_t t) -> 
  lc (open_t n (trm_fvar x) t) ->
  lc (open_t n t' t).
Proof.
  intros. remember (open_t n (trm_fvar x) t) as t''.
  generalize x t t' L n H H0 Heqt''. clear - H1.
  induction H1; intros; destruct_nin.

  (* Case: trm_fvar. *)
  apply eq_sym in Heqt''.
  case_split_names x n.
  apply open_eq_fvar in Heqt''.
  destruct Heqt''; subst.
  simpl; apply_ccn.
  simpl; auto.
  apply open_neq_fvar in Heqt''; auto; subst.
  simpl; auto.
  apply open_neq_fvar in Heqt''; auto; subst.
  simpl; auto.

  (* Case: trm_lam. *)
  apply eq_sym in Heqt''. 
  apply open_eq_lam_fv in Heqt''; auto.
  destruct Heqt''. destruct_conj. subst.
  simpl. apply lc_lam with (L:=x::L++L0++FV_t t'); intros; auto.
  destruct_nin.

  rewrite -> open_comm'; auto.
  rewrite <- close_id with (t := trm_fvar x0) (x:=x) (n:=S n); auto.
  rewrite <- close_open_comm; auto with arith.

  rewrite -> close_open_subst_gen; auto.
  apply subst_lc; auto. 
  
  apply eq_sym in Heqt''. 
  Lemma open_eq_Lam : forall n x t' t,
    open_t n (trm_fvar x) t' = trm_Lam t ->
    exists a, t' = trm_Lam a.
  Proof.
    induction t'; intros; simpl in *; try smash_contra.
    contradict H; apply_ccn; unfold not; intros; smash_contra.
    exists t'; auto.    
  Qed.
  copy_hyp Heqt'' Ha. 
  apply open_eq_Lam in Heqt''.
  destruct Heqt''.
  subst. simpl in *.
  apply lc_Lam. invert_typing Ha.
  apply IHlc with (x1:=x) (L:=L); auto.

  (* Case: trm_app. *)
  apply eq_sym in Heqt''. 
  copy_hyp Heqt'' Hc.
  apply open_eq_app in Heqt''.
  destruct Heqt''. destruct H2. subst.
  simpl. apply lc_app. 
  simpl in *; destruct_nin.
  apply IHlc1 with (x:=x) (L:=L); auto.
  invert_typing Hc; auto.
  simpl in *; destruct_nin.
  apply IHlc2 with (x:=x) (L:=L); auto.
  invert_typing Hc; auto.

  Lemma open_eq_tapp
     : forall (t t' : trm) (T:typ) (n x : nat),
       open_t n (trm_fvar x) t = trm_tapp t' T ->
       exists (t'' : trm), t = trm_tapp t'' T.
  Proof.
    induction t; intros; simpl in *; try smash_contra.
    contradict H; apply_ccn; unfold not; intros; smash_contra.
    exists t; auto.    
    invert_typing H; auto.
  Qed.
  apply eq_sym in Heqt''.
  copy_hyp Heqt'' Ha.
  apply open_eq_tapp in Ha.
  destruct Ha. subst.
  simpl in *. invert_typing Heqt''.
  apply lc_tapp; auto. 
  apply IHlc with (x1:=x) (L:=L); auto.

  (* Case: trm_c. *)
  apply eq_sym in Heqt''. 
  apply open_eq_trmc in Heqt''; subst; simpl; auto.
Qed.

Lemma lc_renaming : forall t'',    
  lc t'' ->
  forall t x n,
    ~ In x (FV_t t) ->
    t'' = open_t n (trm_fvar x) t ->
    (forall y, ~ In y (x::FV_t t) -> lc (open_t n (trm_fvar y) t)).
Proof.
  induction 1; intros q x m Ha Hb y H3; simpl open_t in *; apply eq_sym in Hb.
  
  case_split_names n x.
  apply open_eq_fvar in Hb.
  destruct Hb; subst; simpl; auto.
  rewrite -> nat_compare_eq_eq; auto.
  apply open_neq_fvar in Hb; try omega; subst; simpl; auto.
  apply open_neq_fvar in Hb; try omega; subst; simpl; auto.
  
  apply open_eq_lam_fv in Hb; auto. destruct Hb; destruct H2; subst; simpl in *.
  apply lc_lam with (L:=x::y::L); intros; auto.
  rewrite -> open_comm; auto with arith.
  rewrite <- close_id with (x:=x) (n:=S m) (t:=trm_fvar x0); auto.
  rewrite <- close_open_comm; auto with arith.
  rewrite -> close_open_alpha.
  destruct_nin. rewrite list_cons_eq_app in H4; destruct_nin.
  apply_hyp (H0 x0 H5) Hc. apply subst_lc with (t:=trm_fvar y) (x:=x) in Hc; auto.
  destruct_nin. rewrite list_cons_eq_app in H4; destruct_nin.
  apply H0; auto.
  unfold not; intros. subst. smash_contra.
  
  copy_hyp Hb Hb'.
  apply open_eq_Lam in Hb. destruct Hb; subst.
  simpl; simpl in IHlc; simpl in Ha; simpl FV_t in *.
  apply lc_Lam. apply IHlc with (x:=x).

  rewrite -> cons_to_app in H3. destruct_nin; auto.
  simpl in Hb'. invert_typing Hb'; auto.
  rewrite -> cons_to_app in H3. destruct_nin; auto.
  unfold not; intros; destruct H2; subst; simpl in *;
    smash_contra.
  
  copy_hyp Hb Hb'.
  apply open_eq_app in Hb. destruct Hb. destruct H1; subst.
  apply open_app in Hb'. invert_typing Hb'. clear Hb'.
  simpl FV_t in *; destruct_nin.
  simpl. apply lc_app. 
  
  apply IHlc1 with (x1:=x); auto.
  rewrite -> list_cons_eq_app. apply el_nin_conj_2. split; auto.

  apply IHlc2 with (x0:=x); auto.
  rewrite -> list_cons_eq_app. apply el_nin_conj_2. split; auto.

  copy_hyp Hb Hb'.
  apply open_eq_tapp in Hb.
  destruct Hb. 
  subst. simpl FV_t in *. simpl.
  apply lc_tapp; auto.
  apply IHlc with (x:=x); auto.
  simpl in Hb'. invert_typing Hb'; auto.

  apply open_eq_trmc in Hb; subst; intuition. 
Qed.  
