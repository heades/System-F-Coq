(* begin hide *)
Require Import F.
Require Import names.
Require Import subst.
Require Import basic.

Lemma typ_term_open_term_open_comm : forall t1 x T n m,
  open_t n (trm_fvar x) (open_tT m T t1) = open_tT m T (open_t n (trm_fvar x) t1).
Proof.
  induction t1 as [r | r | A t IH | t IH | t IH1 t' IH2 | t IH A | ];
    intros t2 T n m; simpl; auto; try apply_ccn.

  destruct A; simpl; try (rewrite -> IH; auto).
  
  rewrite -> IH; auto.

  rewrite -> IH1. rewrite -> IH2. auto.

  rewrite -> IH; auto.
Qed.

Lemma lc_open_tT : forall t,
  lc t ->
  forall n T, 
    lc_T T ->
    lc (open_tT n T t).
Proof.  admit. Qed.


Lemma step_lc : forall t t', lc t -> t ~> t' -> lc t'.
Proof.
  intros t t' Hlc. generalize t'. clear - Hlc.
  induction Hlc; intros t' H2. 
  
  invert_typing H2. 
  
  invert_typing H2. apply lc_lam with (L:=L++L0); auto. intros.
  apply H1 with (x:=x); auto. destruct_nin.
  apply_hyp (H7 x H4) H5a. destruct H5a. destruct_conj. subst.
  rewrite -> close_open_id; auto. 
  apply H1 with (x:=x); auto. auto.
  
  invert_typing H2. auto. 

  invert_typing H2.
  invert_typing Hlc1.
  assert (~ In (pick_fresh (L++(FV_t t0)++(FV_t t2))) L).
  auto.
  apply_hyp (H5 (pick_fresh (L++(FV_t t0)++(FV_t t2))) H) H5a.
  
  apply lc_open_inst with (x:=pick_fresh (L ++ FV_t t0 ++ FV_t t2)) (L:=L); auto.

  apply lc_app; eauto.
  apply lc_app; eauto.
  
  invert_typing H2.  apply lc_open_tT; auto.

  auto. invert_typing H2.
Qed.
(* end hide *)
(** At this point we can now define the church-encoding of pairs.   The following defines the 
    constructor for pairs. 
  *)

(* Church-Encoding of pairs in system F. *)
Definition pair_cons := trm_Lam (trm_Lam (trm_lam (typ_bvar 1) 
  (trm_lam (typ_bvar 0) (trm_Lam (trm_lam (typ_arrow (typ_bvar 2) (typ_arrow (typ_bvar 1) (typ_bvar 0))) 
    ((trm_app (trm_app (trm_bvar 0) (trm_bvar 2)) (trm_bvar 1)))))))).

(** This is a little hard to read so lets take a look at this in mathematical notation.
    \( \Lambda X.\Lambda Y.\lambda x:X.\lambda y:Y.\Lambda Z.\lambda z:X \rightarrow (Y \rightarrow Z).(z\,x)\,y. \)
    Here the variables \(x\) and \(y\) are the data we are packaging up in the pair.  The variable \(z\)
    is used to project out the data of the pair. Next we define the type of [pair_cons].
  *)

Definition pair_cons_type := typ_forall (typ_forall (typ_arrow (typ_bvar 1) (typ_arrow (typ_bvar 0) 
   (typ_forall (typ_arrow (typ_arrow (typ_bvar 2) (typ_arrow (typ_bvar 1) (typ_bvar 0))) (typ_bvar 0)))))).

(** In mathematical notation this looks like the following:
    \(\forall X.\forall Y.X \rightarrow (Y \rightarrow \forall Z.((X \rightarrow (Y \rightarrow Z)) \rightarrow Z))\).
    The previous definitions are how we encode church-style pairs in system F.  We define two convince definitions which
    will allow us to easily construct pairs.  The following is the definition of a pair given two terms [a:A] and [b:B].
  *)

Definition pair (A B:typ) (a b:trm) := trm_app (trm_app (trm_tapp (trm_tapp pair_cons A) B) a) b.

(** The following is the type of [pair]. *)


Definition pair_type A B := (typ_forall (typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0))).

(** We need to be sure these are the correct definitions so we first show that [pair_cons] has the type [pair_cons_type]
    and that [pair] has the type [pair_type]. We omit proofs for brevity. *)
(* begin hide *)
Lemma open_T_id : forall A,
  lc_T A -> forall n B, open_T n B A = A.
Proof. 
  induction 1; intros; simpl; auto.

  rewrite -> IHlc_T1. rewrite IHlc_T2. auto.

  (* Apply Hyp. H0 and commute the opens to obtain *
   * an equation between open_T (S n) B t and t.   *)
  admit.
Qed.

Lemma typing_lc : forall G a A, G :> a ; A -> lc a /\ lc_T A.
Proof. admit. Qed.
Hint Resolve typing_lc.
Lemma open_tT_id : forall n A a, lc a -> open_tT n A a = a.
Proof. admit. Qed.  
Hint Rewrite open_id open_tT_id open_T_id : open_rw_db.

Ltac SNIN_C_Hyp :=
  match goal with
    | [H : ~In ?x _ |- _] =>
      match goal with
        | [H' : ~In x (x::_) |- _] =>
          contradiction H'; auto using in_eq
      end
  end.
Hint Extern 1  =>
  SNIN_C_Hyp.
Ltac SNIN_goal :=
  match goal with
    | [ |- ~ In ?x _] => 
      let H := fresh in
        simpl; unfold not; intros H;
          let H1 := fresh H in 
            let H2 := fresh H in
              destruct H as [H1 | H2]; 
                [subst | destruct H2; subst]; auto
  end.
Hint Extern 1 (~In _ _) => SNIN_goal.
Ltac SC_Ok :=
  match goal with
    | [ |- Ok (_ :: nil) ] =>
      idtac "SC_OK: Need to write this goal."
    | [ |- Ok (_ :: _ :: nil) ] =>
      idtac "SC_OK: Need to write this goal."
    | [ |- Ok (_ :: _ :: _ :: nil) ] =>
      repeat apply Ok_ex; auto; simpl dom_t
    | [ |- Ok (_ :: _ :: _ :: _ :: nil) ] =>
      idtac "SC_OK: Need to write this goal."
    | [ |- Ok (_ :: _ :: _ :: _ :: _ :: nil) ] =>
      idtac "SC_OK: Need to write this goal."
    | [ |- Ok (_ :: _ :: _ :: _ :: _ :: _ :: nil) ] =>
      idtac "SC_OK: Need to write this goal."
  end.
Hint Extern 1 (Ok (_::nil)) => SC_Ok.

Hint Extern 1 (In _ _) =>
  match goal with
    | [ |- In ?x _] =>
      match goal with
        | [ |- In x (_ :: x :: _ :: nil)] =>
          simpl; apply or_intror; apply or_introl
        | [ |- In x (_ :: _ :: x :: nil)] =>
          simpl; apply or_intror; apply or_intror; apply or_introl            
        | [ |- In x (_ :: x :: nil) ] =>
          simpl; apply or_intror; apply or_introl
      end; auto
  end. 

Ltac typing_apply_var :=
  match goal with
    | [ |- _ :> trm_fvar ?x ; ?T ] => 
      apply T_Var; auto using in_eq              
  end.
Hint Extern 1 (_ :> trm_fvar _ ; _) => (typing_apply_var).

Ltac roundup_names :=
  let rec roundup L :=
    match goal with
      | H: nat |- _ =>
        let name := constr:H in
          match L with
            | nil => roundup (name::nil)
            | context [name] => fail 1
            | _ => roundup (name::L)
          end
      | _ => L
    end 
    in let L := roundup (nil:list nat) in eval simpl in L.
Ltac inject_names L :=
  let names := roundup_names in
    remember names as L.

Ltac typing_apply_TLam := 
  match goal with
    | [|- _ :> trm_Lam _; _] =>
      let names := roundup_names in
        apply T_TLam with (L:=names); intros; simpl
  end.
Hint Extern 1 (_ :> trm_Lam _; _) => (typing_apply_TLam).

Ltac typing_apply_Lam := 
  match goal with
    | [|- _ :> trm_lam _ _; _] =>
      let names := roundup_names in
        apply T_Lam with (L:=names); intros; simpl
  end.
Hint Extern 1 (_ :> trm_lam _; _) => (typing_apply_Lam).

Fixpoint ctx_lookup_type (n:nat) (G:context) : option typ := 
  match G with
    | nil => None
    | ((x,T)::G') => 
      match (nat_compare x n) with
        | Eq => Some T
        | _ => ctx_lookup_type n G'
      end
  end.
Fixpoint construct_type (G:context) (t:trm) (t':trm) {struct t} : option typ := 
  match t with
    | trm_bvar _ => 
      match t' with
        | trm_fvar n => (* Lookup the type of n in G. *) 
          let T := ctx_lookup_type n G in T
        | _ => None
      end
    | trm_fvar n => (* Lookup the type of n in G. *) 
      let T := ctx_lookup_type n G in T        
    | trm_lam A b => 
      match t' with
        | trm_lam A' b' => 
          let y := pick_fresh (dom_t G) in 
            let a := open_t 0 (trm_fvar y) b' in 
              let T' := construct_type ((y,A)::G) b a in
                match T' with
                  | Some B => Some (typ_arrow A B)
                  | _ => None
                end
        | _ => None
      end
    | _ => None
  end.

Hint Extern 1 (((_,_) :: _) :> _ ; _) =>
  match goal with 
    | [|- ((?x,?A) :: ?G) :> ?t ; ?T] =>
      match goal with
        |  [H : G :> t ; T |- _] =>
          apply weakening_typing with (G2:=((x,A)::nil)) (G1:=G) (G3:=nil)
      end
  end; simpl; auto.

Ltac typing_apply_app :=
  match goal with
    | [ |- _ :> trm_app _ (trm_fvar ?x) ; _ ] =>
      match goal with
        | [ |- (_ :: (x,?T) :: _ :: nil) :> _ ; _] =>
          apply T_App with (T1:=T)              
        | [ |- (_ :: _ :: (x,?T) :: nil) :> _ ; _] =>
          apply T_App with (T1:=T)              
      end
    | [ |- ?G :> trm_app _ ?a ; _] =>
      match goal with
        | [H : _ :> a ; ?A |- _] =>
          apply T_App with (T1:=A)
        | _ =>
          let T := eval simpl in (construct_type G a a) in
            match T with
              | None => fail 2 "Failed to Construct Type of:" a
              | Some ?T' => apply T_App with (T1:=T')
            end
      end
    | [|- _ :> trm_app ?t _; _] =>
       match goal with
         | [H : _ :> t ; typ_arrow ?A _ |- _] =>
           apply T_App with (T1:=A)
       end
  end.
Hint Extern 1 (_ :> trm_app _ _; _) => (typing_apply_app).

Fixpoint type_eq (A:typ) (B:typ) : comparison :=
  match A with
    | typ_arrow A1 A2 => 
      match B with
        | typ_arrow B1 B2 => 
          match (type_eq A1 B1) with
            | Eq => 
              match (type_eq A2 B2) with
                | Eq => Eq
                | _ => Lt
              end
            | _ => Lt
          end
        | _ => Lt
      end
    | typ_forall A1 => 
      match B with
        | typ_forall B1 => 
          match (type_eq A1 B1) with
            | Eq => Eq                
            | _ => Lt
          end
        | _ => Lt
      end          
    | typ_base => 
      match B with
        | typ_base => Eq
        | _ => Lt
      end
    | typ_fvar m =>         
      match B with
        | typ_fvar m' => 
          match (nat_compare m m') with
            | Eq => Eq                
            | _ => Lt
          end
        | _ => Lt
      end
    | typ_bvar m => 
      match B with
        | typ_bvar m' => 
          match (nat_compare m m') with
            | Eq => Eq                
            | _ => Lt
          end
        | _ => Lt
      end
  end.

Fixpoint close_type (A:typ) (n:nat) (B:typ) : typ := 
  match B with
    | typ_arrow B1 B2 => 
      typ_arrow 
      (match (type_eq B1 A) with
         | Eq => (typ_bvar n)
         | _ => (close_type A n B1)
       end) 
      (match (type_eq B2 A) with
         | Eq => (typ_bvar n)
         | _ => (close_type A n B2)
       end) 
    | typ_forall B1 =>
      typ_forall 
      (match (type_eq B1 A) with
         | Eq => (typ_bvar (S n))
         | _ => close_type A (S n) B1
       end)
    | typ_base => typ_base
    | typ_bvar m => 
      match (type_eq B A) with
        | Eq => typ_bvar n
        | _ => typ_bvar m
      end
    | typ_fvar m => 
      match (type_eq B A) with
        | Eq => typ_fvar n
        | _ => typ_fvar m
      end
  end.
Ltac typing_apply_tapp :=
  match goal with
    | [ |- _ :> trm_tapp _ ?A; ?B] =>
      let T := (constr:(close_type A 0 B)) in
        let a := T in
          idtac a
  end.

Ltac type_check :=
  repeat match goal with
    | [|- _ :> trm_fvar _ ; _] =>
      try typing_apply_var
    | [|- _ :> trm_Lam _ ; _] =>
      try typing_apply_TLam
    | [|- _ :> trm_lam _ _ ; _] =>
      try typing_apply_Lam
    | [|- _ :> trm_app _ _ ; _] =>
      try typing_apply_app
  end; try destruct_nin; auto.
(* end hide *)

Lemma pair_cons_typing : nil :> pair_cons ; pair_cons_type.
Proof.
  unfold pair_cons; unfold pair_cons_type; type_check.
Qed.

Lemma pair_typing : forall A B a b, 
  lc_T A ->
  lc_T B ->
  nil :> a ; A ->
  nil :> b ; B ->
  nil :> pair A B a b ; pair_type A B.
Proof.
  intros; unfold pair; unfold pair_type; try type_check.

  apply T_AppT with (T:=typ_arrow A
     (typ_arrow (typ_bvar 0)
        (typ_forall
          (typ_arrow (typ_arrow A (typ_arrow (typ_bvar 1) (typ_bvar 0))) (typ_bvar 0))))); simpl;   auto.
  apply T_AppT with (T:=typ_forall
     (typ_arrow (typ_bvar 1)
        (typ_arrow (typ_bvar 0)
           (typ_forall
              (typ_arrow (typ_arrow (typ_bvar 2) (typ_arrow (typ_bvar 1) (typ_bvar 0)))
                 (typ_bvar 0)))))); simpl; auto.
  apply pair_cons_typing.
  
  repeat (rewrite -> open_T_id; auto).
Qed.
(* begin hide *)
Hint Resolve pair_typing.
(* end hide *)

(** Using our [pair] definition we can construct pairs, but we still need ways of getting
    the data back out of the pairs.  Next we define the first and second projections of
    our pairs. First, we need two very simple functions.  They are used for deciding which
    projection we want. The first function, [arg_one], is used to get the first projection,
    while the second, [arg_two] is used to get the second. *)

Definition arg_one A B := trm_lam A (trm_lam B (trm_bvar 1)).
Definition arg_two A B := trm_lam A (trm_lam B (trm_bvar 0)).

(** Now using [arg_one] and [arg_two] we can define the first and second projections
    as follows: *)

Definition fst (A:typ) (B:typ) (p:trm) := trm_app (trm_tapp p A) (arg_one A B).
Definition snd (A:typ) (B:typ) (p:trm) := trm_app (trm_tapp p B) (arg_two A B).

(** Again we must be sure these are the first definitions.  We first show that
    [fst] and [snd] have the expect type. *)

Lemma fst_typing : forall A B p,
  lc_T A ->
  lc_T B ->
  nil :> p ; pair_type A B ->
  nil :> fst A B p ; A.
Proof. 
  intros; unfold fst; unfold arg_one; try type_check.
  apply T_AppT with (T:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); 
    simpl; auto.
  repeat rewrite -> open_T_id; auto.
Qed.

Lemma snd_typing : forall A B p,
  lc_T A ->
  lc_T B ->
  nil :> p ; pair_type A B ->
  nil :> snd A B p ; B.
Proof. 
  intros; unfold snd; unfold arg_two; try type_check.
  apply T_AppT with (T:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); 
    simpl; auto.
  repeat rewrite -> open_T_id; auto.
Qed.

(* begin hide *)
Lemma Eq_refl : forall a A G, G :> a <~> a ; A.
Proof.
  admit.
Qed.
Hint Extern 1 (_ :> _ <~> _ ; _) => (apply Eq_refl).

Hint Extern 1 =>
  (match goal with
     [|- context[open_T _ _ ?A] ] =>
     match goal with
       | [ _ : lc_T A |- _] =>
         repeat rewrite -> open_T_id; auto
     end
   end).

Ltac eq_apply_app :=
  match goal with     
    [ |- ?G :> trm_app _ ?t <~> trm_app _ _ ; _] =>    
    match goal with 
      | [ H : _ :> t ; ?T |- _] =>
        apply Eq_app with (A:=T)
      | _ =>
        let T := eval simpl in (construct_type G t t) in 
          match T with
            | None => fail 1 "eq_apply_app: Failed to construct the type of" t
            | Some ?T' => apply Eq_app with (A:=T')
          end
    end
  end; auto.

Ltac eq_apply_beta := 
  match goal with 
    | [ |- ?G :> trm_app (trm_lam _ ?b) ?a <~> _; _] =>
      apply Eq_beta with (L:=nil) (a':=a) (b':=b)
  end; simpl; auto.
(* end hide *)

(** Recall that we defined \(\beta\eta\)-equality.  All equational
    reasoning we will do will be using \(\beta\eta\)-equality. Using this
    we show that applying [fst] to a [pair] is equivalent to the first project
    of the pair. *)

Lemma fst_eq : forall A B a b,
  nil :> a ; A ->
  nil :> b ; B ->
  nil :> (pair A B a b) ; pair_type A B ->
  nil :> fst A B (pair A B a b) <~> a ; A.
Proof.
  intros A B a b H1 H2; intros; unfold fst; unfold arg_one; unfold pair; unfold pair_cons.
  copy_hyp H1 H1a.
  copy_hyp H2 H2a.
  apply typing_lc in H1; destruct H1.
  apply typing_lc in H2; destruct H2.
  
  apply Eq_trans with (t3:=
    trm_app
    (trm_tapp
      (trm_app
        (trm_app
          (trm_tapp
            (open_tT 0 A
              (trm_Lam
                  (trm_lam (typ_bvar 1)
                    (trm_lam (typ_bvar 0)
                      (trm_Lam
                        (trm_lam
                          (typ_arrow 
                            (typ_bvar 2)
                            (typ_arrow 
                              (typ_bvar 1) 
                              (typ_bvar 0)))
                          (trm_app
                            (trm_app 
                              (trm_bvar 0) 
                              (trm_bvar 2)) 
                            (trm_bvar 1)))))))) B) a) b) A) (trm_lam A (trm_lam B (trm_bvar 1)))); simpl; auto; try eq_apply_app.

  apply Eq_tapp with (A:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); simpl; auto; try eq_apply_app.
  eq_apply_app.
  
  apply Eq_tapp with (A:=typ_arrow A
     (typ_arrow (typ_bvar 0)
        (typ_forall
           (typ_arrow (typ_arrow A (typ_arrow (typ_bvar 1) (typ_bvar 0))) (typ_bvar 0))))); simpl; auto.
  
  apply Eq_tbeta with (L:=FV_T A++FV_T B) 
    (b:=trm_Lam
     (trm_lam (typ_bvar 1)
        (trm_lam (typ_bvar 0)
           (trm_Lam
              (trm_lam (typ_arrow (typ_bvar 2) (typ_arrow (typ_bvar 1) (typ_bvar 0)))
                 (trm_app (trm_app (trm_bvar 0) (trm_bvar 2)) (trm_bvar 1))))))) 
    (A:=typ_forall
      (typ_arrow (typ_bvar 1)
        (typ_arrow (typ_bvar 0)
          (typ_forall
            (typ_arrow (typ_arrow (typ_bvar 2) (typ_arrow (typ_bvar 1) (typ_bvar 0)))
              (typ_bvar 0)))))); simpl; auto.

  apply Eq_trans with (t3:=trm_app
        (trm_tapp
           (trm_app
              (trm_app
                 (open_tT 0 B 
                       (trm_lam A
                          (trm_lam (typ_bvar 0)
                             (trm_Lam
                                (trm_lam
                                   (typ_arrow A
                                      (typ_arrow (typ_bvar 1) (typ_bvar 0)))
                                   (trm_app
                                      (trm_app (trm_bvar 0) (trm_bvar 2))
                                      (trm_bvar 1))))))) a) b) A)
        (trm_lam A (trm_lam B (trm_bvar 1)))); simpl; auto.
  eq_apply_app.
  apply Eq_tapp with (A:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); simpl; auto.
  eq_apply_app.
  eq_apply_app.
  apply Eq_tbeta with (L:=nil) 
    (b:=(trm_lam A
              (trm_lam (typ_bvar 0)
                 (trm_Lam
                    (trm_lam
                       (typ_arrow A (typ_arrow (typ_bvar 1) (typ_bvar 0)))
                       (trm_app (trm_app (trm_bvar 0) (trm_bvar 2))
                          (trm_bvar 1))))))) 
    (A:=typ_arrow A
     (typ_arrow (typ_bvar 0)
        (typ_forall
           (typ_arrow (typ_arrow A (typ_arrow (typ_bvar 1) (typ_bvar 0))) (typ_bvar 0))))); simpl; auto.
  
  apply Eq_trans with (t3:=trm_app
        (trm_tapp
           (trm_app
              (open_t 0 a 
                    (trm_lam B
                       (trm_Lam
                          (trm_lam
                             (typ_arrow (open_T 1 B A)
                                (typ_arrow B (typ_bvar 0)))
                             (trm_app (trm_app (trm_bvar 0) (trm_bvar 2))
                                (trm_bvar 1)))))) b) A)
        (trm_lam A (trm_lam B (trm_bvar 1)))); simpl; auto.
   eq_apply_app.
   apply Eq_tapp with (A:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); simpl; auto.
   eq_apply_app.
   
  apply Eq_beta with (L:=nil) 
    (a':=a)
    (b':=trm_lam B
              (trm_Lam
                 (trm_lam
                    (typ_arrow (open_T 1 B A) (typ_arrow B (typ_bvar 0)))
                    (trm_app (trm_app (trm_bvar 0) (trm_bvar 2)) (trm_bvar 1))))); simpl; auto.

  apply Eq_trans with (t3:=trm_app
        (trm_tapp
           (open_t 0 b 
                 (trm_Lam
                    (trm_lam
                       (typ_arrow (open_T 1 B A) (typ_arrow B (typ_bvar 0)))
                       (trm_app (trm_app (trm_bvar 0) a) (trm_bvar 1)))))
           A) (trm_lam A (trm_lam B (trm_bvar 1)))); simpl; auto.
  eq_apply_app.
  apply Eq_tapp with (A:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); simpl; auto.
  eq_apply_beta.

  apply Eq_trans with (t3:=trm_app
        (open_tT 0 A
              (trm_lam (typ_arrow (open_T 1 B A) (typ_arrow B (typ_bvar 0)))
                 (trm_app (trm_app (trm_bvar 0) (open_t 1 b a)) b)))
        (trm_lam A (trm_lam B (trm_bvar 1)))); simpl; auto.

  eq_apply_app.
  apply Eq_tbeta with (L:=nil)
    (b:=trm_lam (typ_arrow A (typ_arrow B (typ_bvar 0)))
              (trm_app (trm_app (trm_bvar 0) (open_t 1 b a)) b))
    (A:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); simpl; auto.
  
  apply Eq_trans with (t3:=    
          open_t 0 (trm_lam A (trm_lam B (trm_bvar 1)))
           (trm_app (trm_app (trm_bvar 0) (open_tT 0 A (open_t 1 b a)))
              (open_tT 0 A b))); simpl; auto.  
    
  eq_apply_beta; autorewrite with open_rw_db; auto.
  
  repeat autorewrite with open_rw_db; auto.
  
  apply Eq_trans with 
    (t3:=trm_app (open_t 0 a (trm_lam B (trm_bvar 1))) b); simpl.
  apply Eq_app with (A:=B); simpl; auto; eq_apply_beta. 

  eq_apply_beta; autorewrite with open_rw_db; auto.
Qed.

(* Finally, we do the same for [snd]. *)
Lemma snd_eq : forall A B a b,
  nil :> a ; A ->
  nil :> b ; B ->
  nil :> (pair A B a b) ; pair_type A B ->
  nil :> snd A B (pair A B a b) <~> b ; B.
Proof.
  intros A B a b H1 H2; intros; unfold snd; unfold arg_two; unfold pair; unfold pair_cons.
  copy_hyp H1 H1a.
  copy_hyp H2 H2a.
  apply typing_lc in H1; destruct H1.
  apply typing_lc in H2; destruct H2.
  
  apply Eq_trans with (t3:=
    trm_app
    (trm_tapp
      (trm_app
        (trm_app
          (trm_tapp
            (open_tT 0 A
              (trm_Lam
                  (trm_lam (typ_bvar 1)
                    (trm_lam (typ_bvar 0)
                      (trm_Lam
                        (trm_lam
                          (typ_arrow 
                            (typ_bvar 2)
                            (typ_arrow 
                              (typ_bvar 1) 
                              (typ_bvar 0)))
                          (trm_app
                            (trm_app 
                              (trm_bvar 0) 
                              (trm_bvar 2)) 
                            (trm_bvar 1)))))))) B) a) b) B) (trm_lam A (trm_lam B (trm_bvar 0)))); simpl; auto; try eq_apply_app.

  apply Eq_tapp with (A:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); simpl; auto; try eq_apply_app.
  eq_apply_app.
  
  apply Eq_tapp with (A:=typ_arrow A
     (typ_arrow (typ_bvar 0)
        (typ_forall
           (typ_arrow (typ_arrow A (typ_arrow (typ_bvar 1) (typ_bvar 0))) (typ_bvar 0))))); simpl; auto.
  
  apply Eq_tbeta with (L:=FV_T A++FV_T B) 
    (b:=trm_Lam
     (trm_lam (typ_bvar 1)
        (trm_lam (typ_bvar 0)
           (trm_Lam
              (trm_lam (typ_arrow (typ_bvar 2) (typ_arrow (typ_bvar 1) (typ_bvar 0)))
                 (trm_app (trm_app (trm_bvar 0) (trm_bvar 2)) (trm_bvar 1))))))) 
    (A:=typ_forall
      (typ_arrow (typ_bvar 1)
        (typ_arrow (typ_bvar 0)
          (typ_forall
            (typ_arrow (typ_arrow (typ_bvar 2) (typ_arrow (typ_bvar 1) (typ_bvar 0)))
              (typ_bvar 0)))))); simpl; auto.

  apply Eq_trans with (t3:=trm_app
        (trm_tapp
           (trm_app
              (trm_app
                 (open_tT 0 B 
                       (trm_lam A
                          (trm_lam (typ_bvar 0)
                             (trm_Lam
                                (trm_lam
                                   (typ_arrow A
                                      (typ_arrow (typ_bvar 1) (typ_bvar 0)))
                                   (trm_app
                                      (trm_app (trm_bvar 0) (trm_bvar 2))
                                      (trm_bvar 1))))))) a) b) B)
        (trm_lam A (trm_lam B (trm_bvar 0)))); simpl; auto.
  eq_apply_app.
  apply Eq_tapp with (A:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); simpl; auto.
  eq_apply_app.
  eq_apply_app.
  apply Eq_tbeta with (L:=nil) 
    (b:=(trm_lam A
              (trm_lam (typ_bvar 0)
                 (trm_Lam
                    (trm_lam
                       (typ_arrow A (typ_arrow (typ_bvar 1) (typ_bvar 0)))
                       (trm_app (trm_app (trm_bvar 0) (trm_bvar 2))
                          (trm_bvar 1))))))) 
    (A:=typ_arrow A
     (typ_arrow (typ_bvar 0)
        (typ_forall
           (typ_arrow (typ_arrow A (typ_arrow (typ_bvar 1) (typ_bvar 0))) (typ_bvar 0))))); simpl; auto.
  
  apply Eq_trans with (t3:=trm_app
        (trm_tapp
           (trm_app
              (open_t 0 a 
                    (trm_lam B
                       (trm_Lam
                          (trm_lam
                             (typ_arrow (open_T 1 B A)
                                (typ_arrow B (typ_bvar 0)))
                             (trm_app (trm_app (trm_bvar 0) (trm_bvar 2))
                                (trm_bvar 1)))))) b) B)
        (trm_lam A (trm_lam B (trm_bvar 0)))); simpl; auto.
   eq_apply_app.
   apply Eq_tapp with (A:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); simpl; auto.
   eq_apply_app.   
   eq_apply_beta.

  apply Eq_trans with (t3:=trm_app
        (trm_tapp
           (open_t 0 b 
                 (trm_Lam
                    (trm_lam
                       (typ_arrow (open_T 1 B A) (typ_arrow B (typ_bvar 0)))
                       (trm_app (trm_app (trm_bvar 0) a) (trm_bvar 1)))))
           B) (trm_lam A (trm_lam B (trm_bvar 0)))); simpl; auto.
  eq_apply_app.
  apply Eq_tapp with (A:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); simpl; auto.
  eq_apply_beta.

  apply Eq_trans with (t3:=trm_app
        (open_tT 0 B
              (trm_lam (typ_arrow (open_T 1 B A) (typ_arrow B (typ_bvar 0)))
                 (trm_app (trm_app (trm_bvar 0) (open_t 1 b a)) b)))
        (trm_lam A (trm_lam B (trm_bvar 0)))); simpl; auto.

  eq_apply_app.
  autorewrite with open_rw_db; auto.
  apply Eq_tbeta with (L:=nil)
    (b:=trm_lam (typ_arrow A (typ_arrow B (typ_bvar 0)))
              (trm_app (trm_app (trm_bvar 0) a) b))
    (A:=typ_arrow (typ_arrow A (typ_arrow B (typ_bvar 0))) (typ_bvar 0)); simpl; 
      autorewrite with open_rw_db; auto.
  
  apply Eq_trans with (t3:=    
          open_t 0 (trm_lam A (trm_lam B (trm_bvar 0)))
           (trm_app (trm_app (trm_bvar 0) (open_tT 0 A (open_t 1 b a)))
              (open_tT 0 B b))); simpl; auto.  
    
  eq_apply_beta; autorewrite with open_rw_db; auto.
  
  autorewrite with open_rw_db; auto.
  
  apply Eq_trans with 
    (t3:=trm_app (open_t 0 a (trm_lam B (trm_bvar 0))) b); simpl.
  repeat autorewrite with open_rw_db; auto.
  apply Eq_app with (A:=A); simpl; auto; eq_apply_beta. 

  eq_apply_beta; autorewrite with open_rw_db; auto.
Qed.

(** We have set out on a journey to better understand the relationship between
    church-encoded pairs in system F and categorical products.  So far we have defined
    system F with \(\beta\eta\)-equality and defined church-encoded pairs in system F. 
    In the next post we will layout all the necessary category theory we will need for the
    main result. Stay tuned. *)

(* begin hide *)
Definition mp_prod_def A B C f g u := 
  (nil :> u ; typ_arrow C (pair_type A B)) /\ 
  (nil :> f <~> (trm_lam C (fst A B (trm_app u (trm_bvar 0)))) ; typ_arrow C A) /\
  (nil :> g <~> (trm_lam C (snd A B (trm_app u (trm_bvar 0)))) ; typ_arrow C B).

Definition couple C A B f g := trm_lam C (pair A B (trm_app f (trm_bvar 0)) (trm_app g (trm_bvar 0))).

(* Shows the UMP diagram commutes. *)
Theorem mp_prod : forall f g A B C,
  nil :> f ; typ_arrow C A ->
  nil :> g ; typ_arrow C B ->
  exists u, mp_prod_def A B C f g u.
Proof.
  intros.
  exists (couple C A B f g).
  unfold mp_prod_def.

  copy_hyp H H'; apply typing_lc in H'; destruct H'.
  copy_hyp H0 H0'; apply typing_lc in H0'; destruct H0'.
  invert_typing H2.
  invert_typing H4.

  split.
  apply T_Lam with (L:=nil); intros.
  unfold pair. unfold pair_cons. simpl. autorewrite with open_rw_db; auto.
  admit. 

  split.
  admit.
  admit.
Qed.

(* This is where we run into trouble. Beta-eta equality
 * cannot prove that the universal map is unique. *)
Lemma a : forall c A B,
  nil :> c ; pair_type A B ->
  nil :> (pair A B (fst A B c) (snd A B c)) <~> c ; pair_type A B.
Proof.
  intros c A B H1.

  Print pair.
  Print pair_cons.

  Lemma c : forall A B a b,
    nil :> pair A B a b <~> (trm_Lam (trm_lam (A --> (B --> (typ_bvar 0))) (trm_app (trm_app (trm_bvar 0) a) b))) ; pair_type A B.
  Proof.
    admit.
  Qed.

  Lemma b : forall c A B,
    nil :> c ; pair_type A B ->
    exists a, exists b,
      nil :> c <~> pair A B a b ; pair_type A B.
  Proof.
    intros c A B H1.

    inversion H1; subst.

    inversion H0.

    simpl in *. unfold pair; unfold pair_type in *.
  Qed.
Qed.

Theorem ump_counter : forall A B C f g, 
  nil :> f ; C --> A ->
  nil :> g ; C --> B ->
  exists u', 
    mp_prod_def A B C f g u' ->
    ~ (nil :> couple C A B f g <~> u' ; typ_arrow C (pair_type A B)).
Proof.
  intros A B C f g H1 H2.
  
  unfold pair.
Qed.
(* end hide *)