(* Author: Harley Eades
 *
 * Coq Version: 8.3pl3 
 *
 * This file contains results and tactics related to handing variable 
 * naming and contexts. *)
Require Import Arith.
Require Import List.
Require Import F.
Require Import Omega.

(* Converts an inequality into a disjunction. *)
Lemma neq_lt_or_gt : forall n1 n2,
  n1 <> n2 -> n1 < n2 \/ n1 > n2.
Proof.
  intros; omega.
Qed.

(* These tactics I borrowed from Chris Casigno's Coq development
 * of his work on using step indices in normalization proofs. 
 *
 * The next two tactics are helper tactics of clarify_compares_natc. *)
Ltac compares_cleanup_natc :=
    match goal with
    | [ H : nat_compare _ _ = Eq |- _ ] => apply nat_compare_eq in H
    | [ H : nat_compare _ _ = Lt |- _ ] => apply nat_compare_lt in H
    | [ H : nat_compare _ _ = Gt |- _ ] => apply nat_compare_gt in H
    end.
  
Ltac destruct_compares_natc n m :=
  remember (nat_compare n m);
  match goal with | [ H : ?comp = nat_compare n m |- _ ] =>
    apply eq_sym in H;
    destruct comp
  end;
  compares_cleanup_natc.
(* This is a very handy tactic for breaking up a 
 * nat comparison into several different subgaols.
 *
 * For example if we have a subterm matching
 *   nat_compare _ _ 
 * then clarify_compares_natc generates three
 * subgoals replacing the subterm with either an
 * equality, less-than, or greater-than. *)
Ltac clarify_compares_natc :=
  match goal with
  | [ |- context[match nat_compare ?n ?m with
                 | Lt => _ | Eq => _ | Gt => _ 
                 end]
    ] => destruct_compares_natc n m
  | [ H : ?P (match nat_compare ?n ?m with
              | Lt => _ | Eq => _ | Gt => _ 
              end) _ |- _
    ] => destruct_compares_natc n m
  | [ H : ?P _ (match nat_compare ?n ?m with
                | Lt => _ | Eq => _ | Gt => _ 
                end) |- _
    ] => destruct_compares_natc n m
  end.

(* This tactic case-splits on whether two names are equal,
 * less than, or greater than.  This can be used to case split
 * on whether or not two names are equal. *)
Ltac case_split_names x y := 
  remember (nat_compare x y) as xneq; destruct xneq;
    match goal with
      | [H : Eq = nat_compare x y |- _] =>
        apply eq_sym in H; apply nat_compare_eq in H; subst
      | [H : Gt = nat_compare x y |- _] =>
        apply eq_sym in H; apply nat_compare_gt in H
      | [H : Lt = nat_compare x y |- _] =>
        apply eq_sym in H; apply nat_compare_lt in H
    end.

Lemma nat_compare_eq_eq : forall x,
  nat_compare x x = Eq.
Proof.
  induction x; auto. 
Qed.

Lemma nat_compare_gt_gt : forall x n,
  n < x -> nat_compare x n = Gt.
Proof.
  induction x; destruct n; intros; simpl; auto; try (contradict H; omega).

  invert_typing H;  apply IHx; omega.
Qed.

Lemma nat_compare_lt_lt : forall x n,
  n > x -> nat_compare x n = Lt.
Proof.
  induction x; destruct n; intros; simpl; auto; try (contradict H; omega).

  invert_typing H;  apply IHx; omega.
Qed.

Lemma nil_not_nil : forall {T} A B (x:T),
  ~ (nil = A ++ x::B).
Proof.
  unfold not. intros T A B x H.

  destruct A; simpl in H;
    contradict H; auto using nil_cons.
Qed.

Lemma nil_not_nil_nat : forall A B (x:nat),
  ~ (nil = A ++ x::B).
Proof.
  apply nil_not_nil.
Qed.

Lemma nil_not_nil_ctx : forall A B (x:nat*typ),
  ~ (nil = A ++ x::B).
Proof.
  apply nil_not_nil.
Qed.
Hint Resolve nil_not_nil_nat nil_not_nil_ctx.

Lemma in_app_nat_list : forall (a:nat) A B,
  In a A \/ In a B -> In a (A++B).
Proof.
  auto using in_or_app.
  
Qed.

Lemma in_app_ctx_list : forall (a:context) A B,
  In a A \/ In a B -> In a (A++B).
Proof.
  auto using in_or_app. 
Qed.
Hint Resolve in_app_nat_list in_app_ctx_list.

Lemma dom_app : forall A B,
  dom_t (A++B) = (dom_t A)++(dom_t B).
Proof.
  induction A; intros; simpl; auto.
  
  repeat rewrite -> app_nil_r; auto.
  
  rewrite -> IHA.  destruct a as (x, _ ); auto.
Qed.

Lemma in_dom : forall G x A, In (x,A) G -> In x (dom_t G).
Proof.
  intros G x A H1.  apply in_split in H1. destruct H1. destruct H. subst.
  
  rewrite -> dom_app.  apply in_app_nat_list.
  apply or_intror. simpl. auto.
Qed.  

Lemma in_app_mid : forall {T} A B (x:T), In x (A ++ x::B).
Proof.
  intros. apply in_or_app. apply or_intror. apply in_eq.
Qed.

Lemma in_app_mid_nat : forall A B (x:nat), In x (A ++ x::B).
Proof.
  apply in_app_mid.
Qed.

Lemma in_app_mid_ctx : forall A B (x:context), In x (A ++ x::B).
Proof.
  apply in_app_mid.
Qed.
Hint Resolve in_app_mid_nat in_app_mid_ctx.

Lemma ok_app_dom : forall G G' x T,
  Ok (G ++ (x, T) :: G') ->
  ~ In x (dom_t G) /\ ~ In x (dom_t G').
Proof.
  induction G; intros G' x T H1; split; auto.

  simpl in H1. invert_typing H1; auto.

  simpl in *. destruct a as (x0, A). 
  unfold not; intros H2. apply in_inv in H2. destruct H2 as [H2 | H2].
  subst. invert_typing H1. rewrite -> dom_app in H4. simpl in H4.
  apply H4. auto. invert_typing H1.  apply IHG in H3. destruct H3. contradiction.

  invert_typing H1. apply IHG in H2. destruct H2. auto.
Qed.

Lemma in_types_eq : forall x A B (G G':context),
  Ok (G ++ (x, B) :: G') ->
  In (x, A) (G ++ (x, B) :: G') -> A = B.
Proof.
  intros x A B G G' H1 H2. 
  apply in_app_or in H2.  destruct H2 as [H2' | H2'].

  apply ok_app_dom in H1.
  destruct H1. 
  
  apply in_dom in H2'. contradiction.
  apply in_inv in H2'. destruct H2'.
  invert_typing H; auto.

  apply in_dom in H. apply ok_app_dom in H1. destruct H1. 
  contradiction.
Qed.

Lemma ele_nin_3 : forall L0 L1 L2 (y:nat),
  ~ In y (L0 ++ L1 ++ L2) -> ~ In y L2.
Proof.
  intros L0 L1 L2 y H1.

  unfold not; intro H2. 
  apply or_intror with (A:=In y L1) in H2.

  apply in_app_nat_list in H2.
  apply or_intror with (A:=In y L0) in H2.
  apply in_app_nat_list in H2.
  auto.
Qed.
Hint Resolve ele_nin_3.

Lemma eq_list_ex : forall {A} (a:A) (G1 G2:list A),
   G1 = G2 -> a :: G1 = a :: G2.
Proof.
  intros. destruct G1. destruct G2.

  reflexivity.

  inversion H.

  rewrite <- H. reflexivity.
Qed.

Lemma x_nin_el_rm : forall (x y:nat) L,
  ~ In x (y::L) -> ~ In x L.
Proof.
  unfold not; intros x y L H1 H2.

  apply in_cons with (a:=y) in H2. auto.
Qed.
Hint Resolve x_nin_el_rm.

Lemma eq_ex_list_eq_el : forall {A} (G1 G2:list A) a b,
   a :: G1 = b :: G2 -> a = b.
Proof.
  intros. inversion H. auto.
Qed.

Lemma eq_ex_list_eq : forall {A} (G1 G2:list A) a b,
   a :: G1 = b :: G2 -> G1 = G2.
Proof.
  intros. destruct G1. destruct G2.

  reflexivity.

  inversion H. inversion H. reflexivity.
Qed.

Lemma eq_ex_list_eq_conj : forall {A} (G1 G2:list A) a b,
   a :: G1 = b :: G2 -> a = b /\ G1 = G2.
Proof.
  intros. remember (eq_ex_list_eq_el  G1 G2 a b H). remember (eq_ex_list_eq G1 G2 a b H).
  apply conj. auto. auto.
Qed.

Lemma eq_len_list_ex : forall {A} (a:A) (G1 G2:list A),
  length (a :: G1) = length (a :: G2) -> length G1 = length G2.
Proof.
  intros A a G1 G2 Hlen.
  destruct G1. destruct G2.
  
  eauto.

  inversion Hlen.
  auto.
Qed.

Lemma eq_list_eq_len : forall {A} (G1 G2:list A),
  G1 = G2 -> length G1 = length G2.
Proof.
  intros A G1 G2 Heq.
  destruct G1. destruct G2.
  
  eauto.

  inversion Heq.

  rewrite -> Heq. auto.
Qed.

Lemma el_nin_weakening : forall L A (y:nat),
  ~ In y (L ++ A) -> ~ In y (L ++ A ++ A).
Proof.
  intros L a y H1.  unfold not; intro H2.

  rewrite -> app_assoc in H2.
  apply in_app_or in H2. destruct H1. 
  destruct H2; auto.
Qed.
Hint Resolve el_nin_weakening.

Lemma el_nin_contraction1 : forall (y:nat) L A B C,
  ~ In y (L ++ (A ++ B) ++ C) ->
  ~ In y (L ++ (A ++ B) ++ C ++ B).
Proof.
  unfold not; intros y L A B C H1 H2. 
  
  rewrite <- app_assoc in H2. repeat rewrite -> app_assoc in H2.
  apply in_app_or in H2.  destruct H2.
  repeat rewrite <- app_assoc in H.
  rewrite <- app_assoc in H1; auto.

  apply or_intror with (A:=In y A) in H.
  apply in_or_app in H.
  apply or_introl with (B:=In y C) in H.
  apply in_or_app in H.
  apply or_intror with (A:=In y L) in H.
  apply in_or_app in H.
  auto.
Qed.
Hint Resolve el_nin_contraction1.

Lemma el_nin_conj_2 : forall L1 L2 (x:nat),
  ~ In x L1 /\ ~ In x L2 -> ~ In x (L1 ++ L2).
Proof.
  intros L1 L2 x H1.

  destruct H1 as [H1  H2]. unfold not; intro H3.
  apply in_app_or in H3. destruct H3 as [H3 | H4]; auto.
Qed.
Hint Resolve el_nin_conj_2.

Lemma el_nin_conj_3' : forall L1 L2 L (x:nat),
  ~ In x (L ++ L1 ++ L2) ->
  ~ In x L /\ ~ In x L1 /\ ~ In x L2.
Proof.
  intros L1 L2 L x H1; split; auto.

  split. rewrite -> app_assoc in H1. unfold not; intro.
  apply H1. auto.

  unfold not; intro. apply H1. auto.
Qed.
Hint Resolve el_nin_conj_3'.

Lemma el_nin_conj_3 : forall L1 L2 L (x:nat),
  ~ In x L /\ ~ In x L1 /\ ~ In x L2 -> ~ In x (L ++ L1 ++ L2).
Proof.
  intros L1 L2 L x H1. unfold not; intros H2.
  destruct H1 as [H1 H1'].
  destruct H1' as [H1' H1''].
  
  apply in_app_or in H2. destruct H2 as [H2 | H2]; auto.
  apply in_app_or in H2. destruct H2; auto.  
Qed.
Hint Resolve el_nin_conj_3.

Lemma el_nin_trans1 : forall (y:nat) A B C L,
  ~ In y (L ++ A ++ B) ->
  ~ In y (L ++ A ++ C) ->
  ~ In y (L ++ A ++ B ++ C).
Proof.
  intros y A B C L H1 H2.
  
  apply el_nin_conj_3' in H2. apply el_nin_conj_3' in H1.
  destruct H2. destruct H0.
  
  apply conj with (A:=~ In y L /\ ~ In y A /\ ~ In y B) in H2; auto.
  repeat rewrite -> and_assoc in H2.
  
  apply el_nin_conj_3. split; auto. split; auto.
  apply el_nin_conj_2. split. 
  destruct H2. destruct H3. destruct H4; auto.
  destruct H2. destruct H3. destruct H4; auto.
Qed.
Hint Resolve el_nin_trans1.

Lemma el_nin_contraction2 : forall (y:nat) L A B C,
  ~ In y (L ++ A ++ B ++ C) ->
  ~ In y (L ++ A ++ B ++ A ++ C).
Proof.
  unfold not; intros y L A B C H1 H2.
  
  repeat rewrite -> app_assoc in H2. apply in_app_or in H2.
  destruct H2 as [H2 | H2]. apply in_app_or in H2. destruct H2 as [H2 | H2].

  repeat rewrite <- app_assoc in H2.
  apply or_introl with (B:=In y C) in H2.
  apply in_or_app in H2.
  repeat rewrite <- app_assoc in H2; auto.

  apply or_introl with (B:=In y B) in H2.
  apply in_or_app in H2.
  apply or_introl with (B:=In y C) in H2.
  apply in_or_app in H2.
  apply or_intror with (A:=In y L) in H2.
  apply in_or_app in H2.
  repeat rewrite <- app_assoc in H2; auto.

  apply or_intror with (A:=In y B) in H2.
  apply in_or_app in H2.
  apply or_intror with (A:=In y A) in H2.
  apply in_or_app in H2.
  apply or_intror with (A:=In y L) in H2.
  apply in_or_app in H2.
  auto.
Qed.
Hint Resolve el_nin_contraction2.

Lemma el_nin_trans2 : forall (y:nat) A B C L,
  ~ In y (L ++ A ++ B) ->
  ~ In y (L ++ B ++ C) ->
  ~ In y (L ++ A ++ B ++ C).
Proof.
  intros. apply el_nin_trans1; eauto.
  
  apply el_nin_conj_3. 
  split; auto.
  split. 
  apply el_nin_conj_3' in H. destruct H. destruct H1; auto.
  apply el_nin_conj_3' in H0. destruct H0. destruct H1; auto.
Qed.
Hint Resolve el_nin_trans2.

Lemma el_nin_permute1 : forall A B C D (y:nat),
  ~ In y (A ++ B ++ C ++ D) -> ~ In y (A ++ B ++ D ++ C).
Proof.
  unfold not; intros A B C D y H1 H2.

  repeat rewrite -> app_assoc in H2.
  apply in_app_or in H2. destruct H2 as [H2 | H2].
  apply in_app_or in H2. destruct H2 as [H2 | H2].
  
  apply or_introl with (B:=In y C) in H2.
  apply in_or_app in H2.
  apply or_introl with (B:=In y D) in H2.
  apply in_or_app in H2.
  repeat rewrite <- app_assoc in H2. auto.

  apply or_intror with (A:=In y C) in H2.
  apply in_or_app in H2.
  apply or_intror with (A:=In y B) in H2.
  apply in_or_app in H2.
  apply or_intror with (A:=In y A) in H2.
  apply in_or_app in H2.
  auto.

  apply or_introl with (B:=In y D) in H2.
  apply in_or_app in H2.
  apply or_intror with (A:=In y B) in H2.
  apply in_or_app in H2.
  apply or_intror with (A:=In y A) in H2.
  apply in_or_app in H2.
  auto.
Qed.
Hint Resolve el_nin_permute1.

Theorem app_eq_lengths_eq : forall {A} (G1 G2 G3 G4 : list A),
     G1 ++ G2 = G3 ++ G4
  -> length G1 = length G3
  -> G1 = G3 /\ G2 = G4. 
Proof.
  (* Kick off induction and introduce our
   * our assumptions. *)
  induction  G1. intros G2 G3 G4 Heq Hlen.

  (* We case split on G3. *)
  destruct G3.

  (* Base case. *)
  auto. inversion Hlen.

  (* Step Case. 
   * Introduce our assumptions. *)
  intros G2 G3 G4 Heq Hlen.
  (* Case split on G3. *)
  destruct G3.
  (* G3 = nil case. *)
  inversion Hlen. inversion Hlen. inversion Heq.
  (* Context extend case. 
   * Use our induction hypothesis. *)
  destruct IHG1 with G2 G3 G4.
  (* At this point we need G1 = G3 and G2 = G4. *)
  auto. rewrite -> H1 in Hlen. apply eq_len_list_ex with a0. auto.
  (* Now that we have the equalites all we need to do
   * is use conjunction and eq_list_ex and 
   * finish off with auto. *)
  apply conj. apply eq_list_ex. auto. auto.
Qed.  

Lemma ex_app_list_eq : forall {A} (G1 G2 G3 G4 : list A) a b,
  (a :: G1) ++ G2 = (b :: G3) ++ G4 -> G1 ++ G2 = G3 ++ G4.
Proof.
  intros A G1 G2 G3 G4 a b Heq. 
  destruct G1. destruct G3.

  (* Nil,Nil case. *)
  simpl in *. apply eq_ex_list_eq in Heq. auto.
  (* Ni, cons case. *)
  simpl in *. inversion Heq. auto. 
  (* Cons, cons case. *)
  inversion Heq. rewrite <- app_comm_cons. auto.
Qed.

Lemma len_ex_list_eq : forall {A} (G1 G2 : list A) a b,
  length (a :: G1) < length (b :: G2) -> length G1 < length G2.
Proof.
  intros A G1 G2 a b Hlen. 
  destruct G1. destruct G2.

  (* Nil, nul case. *)
  simpl in *. inversion Hlen. inversion H0.
  (* Nil, cons case. *)
  simpl in *. inversion Hlen. eauto. rewrite <- H in Hlen. rewrite <- H. inversion Hlen. auto.
  rewrite <- H in H0. omega. 
  (* Cons, cons case. *)  
  simpl in *. inversion Hlen. omega. omega.
Qed.

Lemma eq_list_cons_eq : forall {A} (G1 G2 G3 : list A) a,
  G1 = G2 ++ G3 -> a :: G1 = (a :: G2) ++ G3.
Proof.
  intros. destruct G1. destruct G2.
  simpl in *. rewrite <- H. auto.
  simpl in *. rewrite <- H. auto.
  simpl in *. rewrite <- H. auto.
Qed.

Theorem app_eq_lengths_lt2 : forall {A} (G1 G2 G3 G4 : list A) a,
     G1 ++ a :: G2 = G3 ++ G4
  -> length G1 < length G3
  -> exists G5, G3 = G1 ++ a :: G5 /\ G2 = G5 ++ G4.
Proof.
  (* We will kick off with induction and case split on G3. *)
  induction G1. intros G2 G3 G4 a Heq Hlen. destruct G3. 

  (* Base case. *)
  simpl in *. inversion Hlen.  simpl in *. inversion Heq. 
  exists G3. auto. 

  (* Step case. *)
  intros G2 G3 G4 b Heq Hlen. destruct G3. 
  simpl in *. inversion Hlen. 
  simpl in *. inversion Heq. destruct IHG1 with G2 G3 G4 b.
  auto. omega.

  destruct H. exists x. apply eq_list_cons_eq with G3 G1 (b :: x) a0 in H. 
  apply conj. auto. auto.
Qed.

Theorem app_eq_lengths_lt : forall {A} (G1 G2 G3 G4 : list A),
  G1 ++ G2 = G3 ++ G4
  -> length G1 < length G3
  -> exists G5, G3 = G1 ++ G5 /\ G2 = G5 ++ G4.
Proof.
  (* We will kick off with induction and case split on G3. *)
  induction G1. intros G2 G3 G4 Heq Hlen. destruct G3.

  (* Base case.
   * Nil case. *)
  simpl in *. inversion Hlen. 
  (* List app case. *)
  simpl in *. rewrite -> Heq. eauto.

  (* Step case. 
   * Introduce our assumptions and case split on G3. *)
  intros G2 G3 G4 Heq Hlen. destruct G3.
  (* Nil case. *)
  simpl in *. inversion Hlen.
  (* List app case. 
   * Apply the induction hypothesis, which will generate three subgoals. *)
  destruct IHG1 with G2 G3 G4. 
  (* First subgoal.
   * We know that (a::G1) ++ G2 = (a0 :: G3) ++ G4, and this implies that
   * G1 ++ G2 = G3 ++ G4, which we can obtain by applying ex_app_list_eq. 
   * This also finishes off the current subgoal. *)
  apply ex_app_list_eq in Heq. auto.
  (* Second subgoal.
   * We have to show that the length G1 > length G3 which is easly obtained by
   * applying len_ex_list_eq.*)
  apply len_ex_list_eq in Hlen. auto. 
  (* Third subgoal.
   * We now need to show the final part of the induction hypothesis.  
   * Grab all the equalites from Heq and simplify. *)
  inversion Heq. subst. 
  (* Declare our witness and grab some more equalites. *)
  exists x. inversion H. 
  (* Now we need to show the conjunction we already know the second part and
   * the first part is a result of applying eq_list_cons_eq. *)
  apply eq_list_cons_eq with G3 G1 x a0 in H0.
  apply conj. auto. auto.  
Qed.

Lemma list_sum_len_eq : forall {A} (G1 G2 : list A) n m,
  n = length G1 -> m = length G2 -> n + m = length (G1 ++ G2).
Proof.
  intros A G1 G2 n m H1len H2len.

  induction n. destruct m. 

  (* Base case.*)
  rewrite -> app_length. auto.
  rewrite -> app_length. auto.

  (* Step case. *)
  rewrite -> H1len.
  rewrite -> H2len.
  rewrite <- app_length. auto.
Qed.

Lemma list_app_list_eq_nil_r : forall {A} (G1 : list A),
    G1 = G1 ++ nil.
Proof.
  induction G1. intros. 

  (* Base case.*)
  auto. 
  (* Step case. *)
  simpl in *. rewrite -> app_comm_cons. rewrite -> app_nil_r. auto.
Qed.

Lemma list_app_list_eq_nil_l : forall {A} (G1 : list A),
    G1 = nil ++ G1.
Proof.
  auto.
Qed.

Lemma gt_comm_lt : forall n m,
  n > m -> m < n.
Proof.
  auto with arith.
Qed.

Lemma nat_lteq_succ_lteq : forall n m,
  n <= m -> (S n) <= (S m).
Proof.
  intros. auto with arith.
Qed.

Lemma nat_succ_plus : forall n m,
  (S n) + m = S (n + m).
Proof.
  auto with arith.
Qed.

Lemma plus_to_succ : forall n,
  n + 1 = S n.
Proof.
  intros. omega.
Qed.

Lemma length_succ_cons : forall {A} (G:list A) n T,
  n = length G -> n + 1 = length (T :: G).
Proof.
  destruct G; intros; simpl in *; rewrite ->  H; auto with arith.
  rewrite -> plus_to_succ; auto. 
Qed.

Lemma eq_list_eq_cons : forall {A} (G G1 G2 : list A) a,
  G = G1 ++ G2 -> a :: G = (a :: G1) ++ G2.
Proof.
  intros. rewrite -> H. rewrite -> app_comm_cons. auto.
Qed.

(* Lemmas related to well-formed contexts. *)
Lemma ok_rest : forall G x,
  Ok (x::G) -> Ok G.
Proof.
  intros. inversion H. auto.
Qed.

Lemma ok_app_conj : forall G1 G2, Ok (G1++G2) -> Ok G1 /\ Ok G2.
Proof.
  induction G1; destruct G2; intros H1; auto.

  rewrite -> app_nil_r in H1. auto.
  
  split. 
  destruct a; apply Ok_ex.
  copy_hyp H1 H1'.
  simpl in H1. apply ok_rest in H1.
  copy_hyp H1' H1''.
  apply IHG1 in H1. destruct H1. auto.
  
  invert_typing H1. rewrite -> dom_app in H4.
  eauto.

  simpl in H1. apply ok_rest in H1. apply IHG1. auto.
Qed.
Hint Resolve ok_app_conj.

Lemma ok_app_de_app : forall G1 G2 G3,
  Ok (G1++G2++G3) -> Ok(G1++G2).
Proof.
  intros G1 G2 G3 H1.

  rewrite -> app_assoc in H1.
  apply ok_app_conj in H1. destruct H1; auto.
Qed.
Hint Resolve ok_app_de_app.

Lemma ok_app : forall G' G,
  Ok (G++G') -> Ok G.
Proof.
  intros. remember (ok_app_de_app G nil G'). simpl in *. 
  clear Heqo. rewrite -> app_nil_r in o. auto.
Qed.

Lemma ok_app_de_cons : forall G1 G2 a,
  Ok (G1++a::G2) -> Ok(G1++G2).
Proof.
  induction G1; intros.  simpl in *. invert_typing H; auto.

  simpl in *. destruct a. invert_typing H. 
  apply Ok_ex. apply IHG1 with (a:=a0); auto.

  rewrite -> dom_app. rewrite -> dom_app in H4.
  apply el_nin_conj_2. split; eauto.
  
  apply el_nin_conj_3' with (L:=nil) in H4. 
  destruct H4. destruct H1. simpl in H3. destruct a0 in H3.
  eauto.
Qed.
Hint Resolve ok_app_de_cons.

Lemma in_weakening : forall G1 G2 G3 (a:nat*typ),
  In a (G1 ++ G3) -> In a (G1 ++ G2 ++ G3).
Proof.
  intros G1 G2 G3 a H1. apply in_app_or in H1.
  apply or_introl with (B:=In a G2) in H1.
  rewrite -> or_assoc in H1.
  rewrite -> or_comm with (A:=In a G3) (B:=In a G2) in H1.
  rewrite <- or_assoc in H1. 
  destruct H1 as [ H1 | ]; eauto using in_or_app. 
  destruct H1; eauto using in_or_app. 
Qed.
Hint Resolve in_weakening.

Lemma not_in_app_l : forall (x:nat) L L',
  ~ In x (L ++ L') -> ~ In x L.
Proof.
  eauto.
Qed.
Hint Resolve not_in_app_l.

Lemma el_nin_app_rm_2_4 : forall L1 L2 L3 L (x:nat),
  ~ In x (L ++ L1 ++ L2 ++ L3) ->
  ~ In x (L ++ L2).
Proof.
  intros L1 L2 L3 L x H1. apply el_nin_conj_3' in H1. 
  destruct H1 as [H1  H2]. destruct H2 as [H2  H3].
  eauto.
Qed.
Hint Resolve el_nin_app_rm_2_4.

Lemma el_nin_conj : forall L1 L2 (x:nat),
  ~ In x (L1 ++ L2) -> ~ In x L1 /\ ~ In x L2.
Proof.
  eauto.
Qed.
Hint Resolve el_nin_conj.

Lemma trm_fvar_close : forall x y n,
  x <> y ->
  trm_fvar x = (close_t n y (trm_fvar x)).
Proof.
  intros. simpl. clarify_compares_natc; auto.
  subst. contradict H; auto.
Qed.

Lemma list_cons_eq_app : forall {A} L (x:A), x :: L = (x::nil)++L.
Proof.
  eauto. 
Qed.

Lemma cons_to_app : forall (x:nat) L,
  (x :: L) = (x :: nil)++L.
Proof.
  simpl; auto.
Qed.

(* This tactic finds all conjuncts in the context
 * and destructs them.  *)
Ltac destruct_conj :=
  match goal with
    | [H : _ /\ _ |- _ ] =>
      destruct H; try destruct_conj
  end.
(* Much like destruct_conj this tactic first finds all 
 * elements of the context whose type is of the form ~ In x _
 * and converts them into conjuncts, and then destructs those
 * conjunctions.  This is a very handy tactic when reasoning about
 * names. *)
Ltac destruct_nin :=
  match goal with
    | [H : ~ In _ (_ ++ _) |- _] =>
      apply el_nin_conj in H; destruct_conj; try destruct_nin
    | [H : ~ In _ (_ :: _ ++ _) |- _] =>
      rewrite -> list_cons_eq_app in H; apply el_nin_conj in H; 
        destruct_conj; try destruct_nin
    | [H : ~ In _ (_ :: _ :: _) |- _] =>
      rewrite -> list_cons_eq_app in H; apply el_nin_conj in H; 
        destruct_conj; try destruct_nin
  end.
Tactic Notation "destruct_nin" "*" := destruct_nin; intuition eauto.

Lemma not_in_app_r : forall (x:nat) L L',
  ~ In x (L ++ L') -> ~ In x L'.
Proof.
  eauto.
Qed.
Hint Resolve not_in_app_r.

Lemma el_nin_app_rm_1 : forall L1 L2 L3 L (x:nat),
  ~ In x (L ++ L1 ++ L2 ++ L3) ->
  ~ In x (L1 ++ L2 ++ L3).
Proof.
  eauto.
Qed.
Hint Resolve el_nin_app_rm_1.

Lemma not_in_not_eq_head : forall {A} (x0 x:A) L,
  ~ In x0 (x :: L) -> x0 <> x.
Proof.
  unfold not; intros A x0 x L H1 H2. 
  subst. auto using in_eq.
Qed.

Lemma ok_ex_head : forall x x0 T T1 G1 G2,
  Ok (G1 ++ (x, T) :: G2) ->
  x0 <> x ->
  ~ In x0 (dom_t G1) ->
  ~ In x0 (dom_t G2) ->
  Ok ((x0, T1) :: G1 ++ (x, T) :: G2).
Proof.
  intros. apply Ok_ex; auto. unfold not; intros.
  rewrite -> dom_app in H3. simpl in H3. 
  apply in_app_or in H3. destruct H3; auto.

  simpl in H3. destruct H3; auto.  
Qed.
Hint Resolve ok_ex_head.

Lemma ok_in_unique : forall G G' x T T',
  Ok (G++(x,T)::G') -> In (x,T') (G++(x,T)::G') -> T = T'.
Proof.
  induction G; intros. simpl in *. 
  destruct H0. invert_typing H0; auto.

  invert_typing H. apply in_dom in H0. contradiction.

  simpl in *. destruct H0. subst. contradict H. unfold not; intros. 
  invert_typing H. apply H4. rewrite -> dom_app. apply in_or_app.
  apply or_intror. simpl. auto.
  
  apply IHG with (G':=G') (x:=x); auto; invert_typing H; auto.
Qed.
Hint Resolve ok_in_unique.

Lemma in_squash : forall (x x' : nat) (T T':typ) G G',
  In (x,T) (G++(x',T')::G') -> x <> x' -> In (x,T) (G++G').
Proof.
  intros.  apply in_app_or in H.
  destruct H.
  apply or_introl with (B:=In (x,T) G') in H.
  apply in_or_app in H. auto.

  simpl in H. destruct H. invert_typing H. contradict H0; auto.
  apply or_intror with (A:=In (x,T) G) in H.
  apply in_or_app in H. auto.
Qed.
Hint Resolve in_squash.

Lemma ok_in_squash : forall x x0 T T0 G1 G2,
  x <> x0 ->
  Ok (G1 ++ (x, T) :: G2) ->
  In (x0, T0) (G1 ++ (x, T) :: G2) -> 
  In (x0, T0) (G1 ++ G2).
Proof.
  eauto.
Qed.
Hint Resolve ok_in_squash.

Lemma lt_not_eq : forall n m,
  n < m -> n <> m.
Proof.
  intros; omega. 
Qed.
Hint Resolve lt_not_eq.

Lemma gt_not_eq : forall n m,
  n > m -> n <> m.
Proof.
  intros; omega.
Qed.
Hint Resolve gt_not_eq.

Lemma not_free_in_var : forall x x0 L,
  ~ In x0 (x :: L) -> ~ free_in_t x (trm_fvar x0).
Proof.
  intros. unfold free_in_t. simpl. unfold not; intros.
  destruct H0; auto. subst. apply H. apply in_eq.
Qed.
Hint Resolve not_free_in_var.

Lemma in_app : forall G' (a:nat*typ) G,
  In a G -> In a (G++G').
Proof.
  intros. induction G; destruct G'. auto. contradict H. simpl.
  simpl in *. rewrite -> app_nil_r. auto.
  simpl. simpl in H. destruct H. auto. auto.
Qed.
Hint Resolve in_app.

Lemma unique_elem_G : forall x x0 T T0 G,
  Ok G -> In (x,T) G -> In (x0,T0) G -> x = x0 -> T = T0.
Proof.
  induction G; intros. subst. 

  simpl in *. contradiction.
  
  subst; simpl in *.
  destruct H1; destruct H0. subst. invert_typing H0; auto.
  invert_typing H. invert_typing H2. apply in_dom in H0.
  contradiction.
  invert_typing H. invert_typing H2. apply in_dom in H1. 
  contradiction.
  apply IHG; invert_typing H; auto.
Qed.
Hint Resolve unique_elem_G.

(* Results for picking fresh variables. *)
Lemma pick_fresh_app : forall L1 L2,
  pick_fresh (L1 ++ L2) = pick_fresh L1 + pick_fresh L2.
Proof.
  intros. induction L1. simpl; auto. 

  simpl. rewrite -> IHL1. omega.
Qed.

Lemma pick_fresh_gt : forall L,
  (forall y, In y L -> pick_fresh L > y).
Proof.
  induction L; intros. 

  simpl in H. contradiction.

  simpl in *. inversion H. subst. omega. apply IHL in H0. omega.
Qed.
Hint Resolve pick_fresh_gt.

Lemma gt_not_in : forall L (y:nat),
  (forall z, In z L -> y > z) -> ~ (In y L).
Proof.
  induction L; intros.  

  auto.

  simpl in *. unfold not; intros. inversion H0. subst. inversion H0. 
  remember (H y). clear Heqg. apply g in H0. omega.
  
  contradict H1; apply IHL. intros. apply H. auto.

  contradict H1; apply IHL. intros. apply H. auto.
Qed.
Hint Resolve gt_not_in.

Lemma nat_refl : forall (n:nat), n = n.
Proof. 
  auto with arith.
Qed.
Hint Resolve nat_refl.

(* Results regarding context. *)
Lemma ctx_refl : forall (G:context), G = G.
Proof.
  intros; auto.
Qed.
Hint Resolve ctx_refl.

Lemma ctx_refl_nil : forall (G:context), G = nil ++ G.
Proof.
  intros; auto.
Qed.
Hint Resolve ctx_refl_nil.

Lemma el_nin_app_head : forall (x:nat) L1 L2, ~ In x (L1++L2) -> ~ In x L1.
Proof.
  eauto.
Qed.
Hint Resolve el_nin_app_head.

Lemma el_nin_app_tail : forall (x:nat) L1 L2, ~ In x (L1++L2) -> ~ In x L2.
Proof.
  eauto.
Qed.
Hint Resolve el_nin_app_tail.

Lemma el_nin_rm_2 : forall (x:nat) L1 L2 L3, ~ In x (L1++L2++L3) -> ~ In x (L1++L3).
Proof.
  eauto.
Qed.
Hint Resolve el_nin_rm_2.

Lemma el_nin_app_decomp : forall (x:nat) A B, ~ In x A -> ~ In x B -> ~ In x (A++B).
Proof.
  unfold not; intros. apply in_app_or in H1. 
  destruct H1; auto.
Qed.
Hint Resolve el_nin_app_decomp.

Lemma pick_fresh_nin' : forall L1 n,
  n = pick_fresh L1 -> ~ In n L1.
Proof.
  intros. apply gt_not_in. intros. subst. apply pick_fresh_gt. auto.      
Qed.
Hint Resolve pick_fresh_nin'.

Lemma pick_fresh_nin : forall L1,
  ~ In (pick_fresh L1) L1.
Proof.
  intros. apply pick_fresh_nin'. auto.
Qed.
Hint Resolve pick_fresh_nin.

Lemma pick_fresh_app_nin' : forall L1 L2 n,
  n = pick_fresh (L1 ++ L2) ->
  ~ In n L1 /\ ~ In n L2.
Proof.
  intros. remember (pick_fresh_nin (L1++L2)). clear Heqn0. 
  unfold not in *. 
  split; intros; apply n0; apply in_or_app; 
    [apply or_introl | apply or_intror]; subst; auto.
Qed.
Hint Resolve pick_fresh_app_nin'.

Lemma pick_fresh_app_tail : forall L1 L2, ~ In (pick_fresh (L1++L2)) L2.
Proof.
  eauto.
Qed.
Hint Resolve pick_fresh_app_tail.

Lemma pick_fresh_app_head : forall L1 L2, ~ In (pick_fresh (L1++L2)) L1.
Proof.
  eauto.
Qed.
Hint Resolve pick_fresh_app_head.

Lemma pick_fresh_app_nin : forall L1 L2,
  ~ In (pick_fresh (L1 ++ L2)) L1 /\ ~ In (pick_fresh (L1 ++ L2)) L2.
Proof.
  intros. apply pick_fresh_app_nin'; auto.
Qed.
Hint Resolve pick_fresh_app_nin.

Lemma pick_fresh_nin_1 : forall L0 L1 L2,
  ~ In (pick_fresh (L0 ++ L1 ++ L2)) L0.
Proof.
  intros. 
  (remember (pick_fresh_app_nin' L0 (L1 ++ L2) (pick_fresh (L0++L1++L2)) (nat_refl _))). destruct a. 
  auto.
Qed.
Hint Resolve pick_fresh_nin_1.

Lemma pick_fresh_nin_3 : forall L0 L1 L2,
  ~ In (pick_fresh (L0 ++ L1 ++ L2)) L2.
Proof.
  intros. 
  remember (pick_fresh_app_nin (L0 ++ L1) L2). clear Heqa. rewrite <- app_assoc in a.
  destruct a; auto.
Qed.
Hint Resolve pick_fresh_nin_3.

Lemma pick_fresh_eq : forall L1 L2 L3,
  pick_fresh (L1++L2++L3) = pick_fresh (L2++L1++L3).
Proof.
  intros; repeat rewrite -> pick_fresh_app; omega.
Qed.
Hint Resolve pick_fresh_eq.

Lemma pick_fresh_eq' : forall L1 L2 L3,
  pick_fresh (L1++L2++L3) = pick_fresh (L1++L3++L2).
Proof.
  intros; repeat rewrite -> pick_fresh_app; omega.
Qed.
Hint Resolve pick_fresh_eq'.

Lemma pick_fresh_nin_2 : forall L0 L1 L2,
  ~ In (pick_fresh (L0 ++ L1 ++ L2)) L1.
Proof.
  intros. 
  remember (pick_fresh_app_nin L1 (L0++L2)). destruct a.
  clear Heqa.
  rewrite <- pick_fresh_eq in n. auto.
Qed. 
Hint Resolve pick_fresh_nin_2.

Lemma pick_fresh_nin_4_3 : forall L0 L1 L2 L3,
  ~ In (pick_fresh (L0 ++ L1 ++ L2++L3)) L2.
Proof.
  eauto.
Qed. 
Hint Resolve pick_fresh_nin_4_3.

Lemma pick_fresh_nin_5_4 : forall L0 L1 L2 L3 L4,
  ~ In (pick_fresh (L0 ++ L1 ++ L2 ++ L3 ++ L4)) L3.
Proof.
  eauto.
Qed. 
Hint Resolve pick_fresh_nin_5_4.

Lemma pick_fresh_nin_rm_2 : forall L1 L2 L3,
    ~ In (pick_fresh (L1 ++ L2 ++ L3)) (L1 ++ L3).
Proof.
  eauto. 
Qed.
Hint Resolve pick_fresh_nin_rm_2.

Lemma pick_fresh_nin_rm_2_3 : forall L1 L2 L3 L4,
  ~ In (pick_fresh (L1 ++ L2 ++ L3 ++ L4)) (L1 ++ L4).
Proof.
  eauto.
Qed.
Hint Resolve pick_fresh_nin_rm_2_3.

Lemma pick_fresh_nin_rm_1_3 : forall L1 L2 L3 L4,
    ~ In (pick_fresh (L1 ++ L2 ++ L3 ++ L4)) (L2 ++ L4).
Proof.
  eauto. 
Qed.
Hint Resolve pick_fresh_nin_rm_1_3.

Lemma pick_fresh_nin_5_5 : forall L0 L1 L2 L3 L4,
  ~ In (pick_fresh (L0 ++ L1 ++ L2 ++ L3++L4)) L4.
Proof.
  eauto. 
Qed. 
Hint Resolve pick_fresh_nin_5_5.

Lemma pick_fresh_rm_el_C : forall A B C x,
  ~ In (pick_fresh (A++B++x::C)) (A++B++C).
Proof.
  eauto.
Qed.
Hint Resolve pick_fresh_rm_el_C.

Lemma in_pick_fresh_neq : forall x L,
  In x L -> trm_fvar x <> trm_fvar (pick_fresh L).
Proof.
  unfold not; intros. invert_typing H0; clear H0.
  contradict H. eauto.
Qed.
Hint Resolve in_pick_fresh_neq.

Lemma pick_fresh_premute1 : forall A B C D,
  pick_fresh (A ++ B ++ C ++ D) = pick_fresh (A ++ B ++ D ++ C).
Proof.
  intros. repeat rewrite -> pick_fresh_app. omega.
Qed.
Hint Resolve pick_fresh_premute1.

Lemma el_nin_fv_open : forall t t' x n,
~ In x (FV_t t ++ FV_t t') ->
~ In x (FV_t (open_t n t t')).
Proof.
  induction t'; intros. simpl.

  clarify_compares_natc; eauto.

  eauto.

  simpl in *. apply IHt'; eauto.
  simpl in *. apply IHt'; auto.

  simpl. apply el_nin_conj_2. split. apply IHt'1; simpl in H.
  rewrite -> app_assoc in H. apply el_nin_conj in H.
  eauto.

  apply IHt'2; simpl in H; eauto.
  
  simpl in *. apply IHt'. auto.

  simpl in *; auto.
Qed.
Hint Resolve el_nin_fv_open : naming_fv.

Lemma trm_lam_eq : forall t t' T T',
  trm_lam T t = trm_lam T' t' <-> T = T' /\ t = t'.
Proof.
  split; intros; inversion H; auto.
  
  destruct H; subst; auto.
Qed.

Lemma trm_Lam_eq : forall t t',
  trm_Lam t = trm_Lam t' <-> t = t'.
Proof.
  split; intros H; inversion H; auto.
Qed.

Lemma trm_lam_eq_bodies : forall t t' T,
  trm_lam T t = trm_lam T t' -> t = t'.
Proof.
  intros; inversion H; auto.
Qed.

Lemma open_comm : forall t n m y z,
  n <> m ->
  z <> y ->
  open_t n (trm_fvar y) (open_t m (trm_fvar z) t) = 
  open_t m (trm_fvar z) (open_t n (trm_fvar y) t).
Proof.
  induction t as [x | x | A t IH | t IH | t1 IH1 t2 IH2 | t IH T | ];
    intros n m y z H1 H2; simpl; auto.
  
  clarify_compares_natc; simpl; auto; clarify_compares_natc; 
    auto; simpl; subst; auto; try clarify_compares_natc; subst; auto; 
      try (contradict Heqc; omega).
  
  contradict H1; auto.
  
  rewrite -> IH; auto.
  rewrite -> IH; auto.
  
  rewrite -> IH1; auto. rewrite -> IH2; auto.

  rewrite -> IH; auto.
Qed.

Lemma close_id : forall t x n,
  ~ In x (FV_t t) -> close_t n x t = t.
Proof.
  induction t; intros; simpl; eauto.

  clarify_compares_natc; auto. subst. contradict H. apply in_eq.
  
  rewrite -> IHt; eauto.
  rewrite -> IHt; eauto.

  rewrite -> IHt1; eauto. rewrite -> IHt2; eauto.
  rewrite -> IHt; auto.
Qed.

Lemma close_open_comm : forall t1 t2 m n x,
  m <> n ->
  ~ In x (FV_t t2) ->
  close_t m x (open_t n t2 t1) = open_t n (close_t m x t2) (close_t m x t1).
Proof.
  induction t1; intros; rewrite -> close_id with (t:=t2); eauto; simpl.

  clarify_compares_natc; subst; eauto. rewrite -> close_id with (t:=t2); eauto.
  clarify_compares_natc; subst; eauto. 
  simpl. clarify_compares_natc; subst; eauto. contradict H. auto.

  rewrite -> IHt1; eauto. rewrite -> close_id with (t:=t2); eauto.
  rewrite -> IHt1; eauto. rewrite -> close_id with (t:=t2); eauto.

  rewrite -> IHt1_1; eauto. rewrite -> IHt1_2; eauto.
  rewrite -> close_id with (t:=t2); eauto.
  
  rewrite -> IHt1; auto. rewrite -> close_id with (t:=t2); auto.
Qed.

Lemma trm_fvar_eq1 : forall n m,
  n = m -> trm_fvar n = trm_fvar m.
Proof.
  intros. inversion H. auto.
Qed.

Lemma trm_fvar_eq2 : forall n m,
    trm_fvar n = trm_fvar m -> n = m.
Proof.
  intros. inversion H. auto.
Qed.

Definition Is_bvar (t:trm) := 
  match t with
    | trm_bvar n => True
    | _ => False
  end.

Definition Is_fvar (t:trm) := 
    match t with
      | trm_fvar n => True
      | _ => False
    end.

Definition Is_lam (t:trm) := 
  match t with
    | trm_lam A t1 => True
    | _ => False
  end.

Definition Is_Lam (t:trm) := 
  match t with
    | trm_Lam t1 => True
    | _ => False
  end.

Definition Is_app (t:trm) := 
  match t with
    | trm_app t1 t2 => True
    | _ => False
  end.

Definition Is_tapp (t:trm) := 
  match t with
    | trm_tapp _ _ => True
    | _ => False
  end.

Definition Is_arrow (T:typ) := 
  match T with
    | typ_arrow T1 T2 => True
    | _ => False
  end.

Definition Is_base (T:typ) := 
  match T with
    | typ_base => True
    | _ => False
  end.

Definition Is_trm_c (t:trm) := 
  match t with
    | trm_c => True
    | _ => False
  end.

Definition Is_some (t:option typ) := 
  match t with
    | Some _ => True
    | _ => False
  end.

Definition Is_none (t:option typ) := 
  match t with
    | None => True
    | _ => False
  end.

Lemma opt_refl : forall {A} (a:A),
  Some a = Some a.
Proof.
  auto.
Qed.

Lemma neq_sym : forall {A} (a b : A),
  a <> b -> b <> a.
Proof.
  auto.
Qed.

Lemma none_neq_some : forall (a:typ),
  None <> Some a.
Proof.
  intros. 
  red. intros. change (Is_none (Some a)). rewrite <- H. simpl. trivial.
Qed.

Ltac smash_help H t1 t2 is_f RD :=
  contradict H; unfold not; intros; 
    match goal with
      | [H' : t1 = t2 |- _ ] =>
        change is_f; 
          match RD with
            | True => rewrite -> H'
            | False => rewrite <- H'
          end; simpl; auto
    end. 
  
Ltac match_contra_form :=
  match goal with
    | [ H : ?A = ?B |- _ ] =>
      match A with
        | trm_c => 
          match B with
            | trm_c => constr:True
            | _ => constr:(H, A, B, (Is_trm_c B))
          end
        | trm_bvar _ => 
          match B with
            | trm_bvar _ => constr:True
            | _ => constr:(H, A, B, (Is_bvar B))
          end
        | trm_fvar _ => 
          match B with
            | trm_fvar _ => constr:True
            | _ => constr:(H, A, B, (Is_fvar B))
          end
        | trm_lam _ _ => 
          match B with
            | trm_lam _ _ => constr:True
            | _ => constr:(H, A, B, (Is_lam B))
          end
        | trm_Lam _ => 
          match B with
            | trm_Lam _ => constr:True
            | _ => constr:(H, A, B, (Is_Lam B))
          end
        | trm_app _ _ => 
          match B with
            | trm_app _ _ => constr:True
            | _ => constr:(H, A, B, (Is_app B))
          end
        | trm_tapp _ _ => 
          match B with
            | trm_tapp _ _ => constr:True
            | _ => constr:(H, A, B, (Is_tapp B))
          end
        | None =>
          match B with
            | None => constr:True
            | _ => constr:(H, A, B, (Is_none B))
          end
        | Some _ => 
          match B with
            | Some _ => constr:True
            | _ => constr: (H, A, B, (Is_some B))
          end
        | typ_arrow _ _ =>
          match B with
            | typ_arrow _ _ => constr:True
            | _ => constr:(H, A, B, (Is_arrow B))
          end
        | typ_base =>
          match B with
            | typ_base => constr:True
            | _ => constr:(H, A, B, (Is_base B))
          end
      end
  end.

(* This tactic tries to solve any goal who results from a contradiction
 * formed by a contradictory equality between terms, types, or option constructors. *)
Ltac smash_trm_typ_contra := 
  let A := match_contra_form in 
    match A with
      | True => idtac
      | (?H, ?t, ?t', ?is_f) => 
        contradict H; unfold not; intros; change is_f;
          match goal with
            [ H' : t = t' |- _] => rewrite <- H'
          end; simpl; auto
    end.
(* This tactic tries to solve a goal which has a hypothesis of an
 * inequality between nats and a hypothesis of an equality between
 * trm_fvar's whose names are said nats. *)
Ltac smash_var_contra := 
  match goal with
    | [ H' : ?x <> ?x' |- _ ] =>
      match goal with
        | [ H : trm_fvar x' = trm_fvar x |- _] =>
          contradict H; unfold not; intros; apply (trm_fvar_eq2 x' x) in H; auto
        | [ H : trm_fvar x = trm_fvar x' |- _] =>
          contradict H; unfold not; intros; apply (trm_fvar_eq2 x x') in H; auto
        | [ H : x = x' |- _ ] => 
          contradict H'; auto
      end
  end.
(* Clears all trivial equalities. *)
Ltac clear_trivial_eqs := 
  match goal with
    | [_ : ?A = _ |- _] =>
      match goal with
        | [H : A = A |- _] => 
          clear H; clear_trivial_eqs
        | _ => idtac
      end
  end.  
  (* Nat. contras. *)
Ltac nat_contra :=
  match goal with
    | [ _ : ?x < ?y |- _] =>
      match goal with
        | [ H : x < x |- _ ] =>
          contradict H; omega
        | [ H : y < x |- _] =>
          contradict H; omega
      end
    | [ _ : ?x > ?y |- _] =>
      match goal with
        | [ H : x > x |- _ ] =>
          contradict H; omega
      end
    | [ H : _ < 0 |- _ ] =>
      contradict H; omega
    | [ _ : ?x <> _ |- _] =>
      match goal with
        | [  H : x <> x |- _ ] =>
          contradict H; auto
      end
  end.

Ltac names_contra :=
  match goal with
    | [H : ~ In ?y (FV_t (trm_fvar ?x)) |- _] =>
      match goal with
        | [H : ~ In y (FV_t (trm_fvar y)) |- _] =>
          simpl in H; contradict H; auto
      end
    | [H : ~ (?y = ?x \/ False) |- _] =>
      match goal with
        | [H : ~ (?y = ?x \/ False) |- _] =>
          contradict H; auto
      end
    | [ _ : ~ In ?n (_ :: _) |- _] =>
      match goal with
        | [ H : ~ In n (n :: _) |- _] =>
          contradict H; auto using in_eq
        | [ H : ~ In n (_ :: n :: _) |- _] =>
          destruct_nin; names_contra
      end
  end.

(* Tries to apply one of the previous four tactics. *)
Ltac smash_contra' := smash_trm_typ_contra || smash_var_contra || nat_contra || names_contra.
Ltac smash_contra := (try clear_trivial_eqs); try repeat smash_contra'.

Ltac apply_ccn :=
  match goal with
    | [ |- context [nat_compare ?n ?n'] ] => 
      clarify_compares_natc; simpl; try apply_ccn
  end; auto; try ((subst; smash_contra) || smash_contra).

Lemma open_eq_fvar : forall t n x,
  open_t n (trm_fvar x) t = trm_fvar x ->
  t = trm_bvar n \/ t = trm_fvar x.
Proof.
  induction t; intros; simpl; auto; simpl in *; try smash_trm_typ_contra.
  clarify_compares_natc; subst; auto; smash_trm_typ_contra.  
Qed.

Lemma open_eq_bvar : forall t n n' x,
  open_t n (trm_fvar x) t = trm_bvar n' -> t = trm_bvar n'.
Proof.
  induction t; intros; simpl; auto; simpl in *; try smash_trm_typ_contra.
  clarify_compares_natc; subst; auto; smash_trm_typ_contra.
Qed.
Hint Resolve eq_sym open_eq_fvar open_eq_bvar : naming_open.

Lemma open_eq_helper : forall t t' x L A n,
    ~ In x (L ++ FV_t t ++ FV_t t') ->
    (forall x n, ~ In x (L ++ FV_t t ++ FV_t t') -> open_t n (trm_fvar x) t = open_t n (trm_fvar x) t' -> t = t') ->
    open_t n (trm_fvar x) (trm_lam A t) = open_t n (trm_fvar x) (trm_lam A t') ->
    (trm_lam A t) = (trm_lam A t').
Proof.
  intros; simpl. apply trm_lam_eq; split; auto.
  apply H0 with (x:=x) (n:=S n); eauto.
  simpl in H1. apply trm_lam_eq in H1. destruct H1. auto.
Qed.

Lemma open_eq : forall t t' x L n,
  ~ In x (L ++ FV_t t ++ FV_t t') ->
  open_t n (trm_fvar x) t = open_t n (trm_fvar x) t' ->
  t = t'.
Proof.
  induction t; intros. simpl in H0. clarify_compares_natc; subst.
  
  apply eq_sym in H0; apply open_eq_fvar in H0. destruct H0; eauto. subst.
  simpl in H. contradict H. eauto.

  eauto with naming_open. 
  eauto with naming_open.
  
  simpl in H0.
  destruct t'; simpl in *; auto; try smash_trm_typ_contra.
  clarify_compares_natc; try smash_trm_typ_contra.
  invert_typing H0. contradict H; eauto.
  
  destruct t'; simpl in *; try smash_trm_typ_contra.
  clarify_compares_natc; smash_trm_typ_contra.
  apply trm_lam_eq in H0. destruct H0; subst. 
  apply open_eq_helper with (x:=x) (L:=L) (n:=n); eauto.
  simpl. apply trm_lam_eq; auto.
  
  destruct t'; simpl in *; try smash_trm_typ_contra.
  clarify_compares_natc; smash_trm_typ_contra.
  rewrite -> trm_Lam_eq in H0.
  apply trm_Lam_eq. apply IHt with (x:=x) (L:=L) (n:=n); auto.
  
  simpl in H0. 

  assert(t' = trm_app t1 t2).
  (* Proof of assert. *)
  destruct t'; intros; simpl in *; try smash_trm_typ_contra.

  clarify_compares_natc; smash_trm_typ_contra.

  invert_typing H0. 
  rewrite -> IHt1 with (t':=t'1) (x:=x) (L:=L) (n:=n); auto.
  rewrite -> IHt2 with (t':=t'2) (x:=x) (L:=L) (n:=n); auto.
  apply el_nin_conj in H. destruct H.
  apply el_nin_conj in H1. destruct H1. 
  apply el_nin_conj in H1. destruct H1.
  apply el_nin_conj in H4. destruct H4. eauto.
  apply el_nin_conj in H. destruct H.
  apply el_nin_conj in H1. destruct H1. 
  apply el_nin_conj in H1. destruct H1.
  apply el_nin_conj in H4. destruct H4. eauto.
  (* End proof of assert. *)
  subst. auto.

  destruct t'; simpl in *; try smash_trm_typ_contra.
  clarify_compares_natc; smash_trm_typ_contra.
  invert_typing H0. clear H0.
  rewrite -> IHt with (x:=x) (n:=n) (L:=L) (t':=t'); auto.

  simpl in H0. destruct t'; simpl in *; auto; try smash_trm_typ_contra.
  clarify_compares_natc; smash_trm_typ_contra.
Qed.

Lemma trm_lam_eq_lc : forall t t' A L,
  (forall y, ~ In y L -> open_t 0 (trm_fvar y) t = open_t 0 (trm_fvar y) t') ->
  trm_lam A t = trm_lam A t'.
Proof.
  intros. apply trm_lam_eq; split; auto. 
  apply open_eq with (x:=pick_fresh (L++FV_t t++FV_t t')) (L:=L) (n:=0); eauto.
Qed.

Lemma el_nin_neq : forall L1 L2 (y x:nat),
  ~ In y (L1 ++ x::L2) -> y <> x.
Proof.
  intros. unfold not; intros; subst. contradict H; eauto.
Qed.
Hint Resolve el_nin_neq : naming_el.

Ltac auto_simp := simpl ; auto.
Lemma close_open_id : forall t n x,
  lc t ->
  open_t n (trm_fvar x) (close_t n x t) = t.
Proof.
  intros t0 n0 x0 H.
  generalize n0 x0. clear - H.
  induction H; intros; auto_simp.
  
  clarify_compares_natc; auto_simp.
  rewrite -> nat_compare_eq_eq; auto.
  
  apply trm_lam_eq_lc with (L:=L++(x0::nil)). 
  intros. apply_hyp (H1 y (el_nin_app_head _ _ _ H2) (S n0) x0) H0a.
  rewrite -> close_open_comm in H0a; auto with arith.
  rewrite -> close_id in H0a.
  rewrite -> open_comm in H0a. auto. auto with arith.

  eauto with naming_el.
  simpl. unfold not; intros.  destruct H3; subst; eauto.
  simpl. unfold not; intros.  destruct H3; subst; eauto.

  apply trm_Lam_eq. auto.

  rewrite -> IHlc1. rewrite -> IHlc2. auto.
  rewrite -> IHlc. auto.
Qed.

Lemma el_nin_fv_close : forall t x y n,
  ~ In y (x::FV_t t) ->
  ~ In y (FV_t (close_t n x t)).
Proof.
  induction t; intros; simpl; auto.

  clarify_compares_natc; eauto.

  apply el_nin_conj_2. split. 
  apply IHt1; simpl FV_t in H. destruct_nin.
  rewrite -> list_cons_eq_app. apply el_nin_conj_2. split; auto.
  apply IHt2; simpl FV_t in H. destruct_nin.
  rewrite -> list_cons_eq_app. apply el_nin_conj_2. split; auto.
Qed.

Lemma open_app : forall t' t1 t2 z n,
  open_t n (trm_fvar z) (trm_app t1 t2) = t' ->
  t' = trm_app (open_t n (trm_fvar z) t1) (open_t n (trm_fvar z) t2).
Proof.
  eauto.
Qed.

Lemma open_neq_fvar : forall t n x y,
  x <> y ->
  open_t n (trm_fvar x) t = trm_fvar y ->
  t = trm_fvar y.
Proof.
  induction t; intros; simpl; auto; simpl in *; try smash_trm_typ_contra.
  clarify_compares_natc; subst; auto; smash_trm_typ_contra.
  inversion H0. contradict H2; auto.
Qed.

Lemma open_eq_fvar' : forall t n x y,
  open_t n (trm_fvar x) t = trm_fvar y ->
  t = trm_bvar n \/ t = trm_fvar y.
Proof.
  induction t; intros; simpl; auto; simpl in *; try smash_trm_typ_contra.
  clarify_compares_natc; subst; auto; smash_trm_typ_contra.
Qed.

Lemma lc_open_id : forall t,
  lc t ->
  forall n x, lc (open_t n (trm_fvar x) t).
Proof.
  induction 1; intros; simpl; auto. 

  apply lc_lam with (L:=x::L++(FV_t t)); auto; intros. 
  rewrite -> open_comm; try auto with arith. apply H1; auto.
  destruct_nin; auto.
  destruct_nin. unfold not; intros; subst. contradict H1; auto using in_eq.
Qed.

Lemma el_nin_fv_open_fvar : forall t' z y,
  ~ In y (z :: nil) ->
  ~ In y (FV_t t')  ->
  ~ In y (FV_t (open_t 0 (trm_fvar z) t')).
Proof.
  intros t'; generalize t' 0. clear t'. 
  induction t'; intros; simpl.
  
  clarify_compares_natc; subst; auto.
  intuition auto.
  subst. apply H0. simpl. auto.
  simpl in H0. intuition eauto.
  simpl in H0. intuition eauto.
  
  simpl in H0. destruct_nin. eauto. 
  simpl in H0. eauto.
  auto.
Qed.
Hint Resolve el_nin_fv_open_fvar.

Lemma trm_fvar_eq : forall x y,
  x = y -> trm_fvar x = trm_fvar y.
Proof.
  auto.
Qed.
Hint Resolve trm_fvar_eq.

Lemma trm_fvar_eq' : forall x y,
  trm_fvar x = trm_fvar y -> x = y.
Proof.
  intros; invert_typing H; auto.
Qed.
Hint Resolve trm_fvar_eq.

Lemma trm_fvar_neq : forall x y,
  x <> y -> trm_fvar x <> trm_fvar y.
Proof.
  unfold not; intros. 
  
  apply trm_fvar_eq' in H0. auto.
Qed.
Hint Resolve trm_fvar_neq.

Lemma name_pick_fresh : forall x L L', x <> pick_fresh (L++x::L').
Proof.
  destruct L; intros; simpl. 
  omega.
  rewrite -> pick_fresh_app; simpl; omega.
Qed.
Hint Resolve name_pick_fresh.

Lemma open_close_id : forall (t : trm) (n x : nat),
  ~ In x (FV_t t) ->
  close_t n x (open_t n (trm_fvar x) t) = t.
Proof.
  induction t; intros; simpl in *; auto.
  
  clarify_compares_natc; auto. subst.
  simpl. rewrite -> nat_compare_eq_eq; auto.
  clarify_compares_natc; subst; auto. contradict H; auto.

  rewrite -> IHt; auto.
  rewrite -> IHt; auto.
  
  destruct_nin.
  rewrite -> IHt1; auto.
  rewrite -> IHt2; auto.

  rewrite -> IHt; auto.
Qed.

Lemma open_eq_lam : forall t t' n x T,
  open_t n (trm_fvar x) t = trm_lam T t' ->
  exists t'', t = trm_lam T t''.
Proof.
  induction t; intros; simpl in *; try smash_trm_typ_contra.
  
  clarify_compares_natc; simpl in *; try smash_trm_typ_contra.    
  
  invert_typing H. exists t; auto.
Qed.

Lemma open_eq_lam_fv : forall t t' n x T,
  ~ In x (FV_t t) ->
  open_t n (trm_fvar x) t = trm_lam T t' ->
  exists t'', t = trm_lam T t'' /\ t'' = close_t (S n) x t'.
Proof.
  induction t; intros; simpl in *; try smash_trm_typ_contra.
  
  clarify_compares_natc; simpl in *; try smash_trm_typ_contra.    
  
  copy_hyp H0 H0'. inversion H0. rewrite <- H2 in *. clear H2.
  
  rewrite -> open_close_id. exists t; split; auto. exact H.
Qed.

Lemma open_eq_app : forall t t1 t2 n x,
  open_t n (trm_fvar x) t = trm_app t1 t2 ->
  exists t1', exists t2', t = trm_app t1' t2'.
Proof.
  induction t; intros; simpl in *; try smash_trm_typ_contra.
  
  clarify_compares_natc; simpl in *; try smash_trm_typ_contra.    
  
  exists t1. exists t2; auto.
Qed.

Lemma open_rec_term_core :forall t j v i u, i <> j ->
  open_t j v t = open_t i u (open_t j v t) ->
  open_t i u t = t.
Proof.
  induction t; intros; simpl in *; auto.

  repeat clarify_compares_natc; auto.
  rewrite -> Heqc0 in *. contradict H; auto. subst.
  simpl in H0. rewrite -> nat_compare_eq_eq in H0; auto.
  subst. simpl in H0. rewrite -> nat_compare_eq_eq in H0; auto.
  
  rewrite -> IHt with (j:=S j) (v:=v); auto.
  apply trm_lam_eq in H0. destruct H0. auto.

  apply trm_Lam_eq. apply IHt with (j:=j) (v := v); auto.
  apply trm_Lam_eq; auto.

  invert_typing H0. 
  rewrite -> IHt1 with (j:=j) (v:=v); auto.
  rewrite -> IHt2 with (j:=j) (v:=v); auto.

  invert_typing H0.
  rewrite -> IHt with (j:=j) (v:=v); auto.
Qed.
Hint Resolve open_rec_term_core.

Lemma open_id : forall t t',
  lc t -> (forall n, open_t n t' t = t).
Proof.
  induction 1; intros; simpl; auto.
  
  apply f_equal. 
  eapply (open_rec_term_core t 0 (trm_fvar (pick_fresh L))); eauto.
  apply eq_sym. apply H1; eauto.

  apply f_equal. auto.
  rewrite -> IHlc1. rewrite -> IHlc2. auto.

  rewrite -> IHlc; auto.
Qed.
Hint Resolve open_id : naming_open.

Lemma open_comm' : forall t t' x n m,
  lc t' ->
  n <> m ->
  ~ In x (FV_t t') ->
  open_t n (trm_fvar x) (open_t m t' t) = 
  open_t m t' (open_t n (trm_fvar x) t).
Proof.
  induction t; intros.
  
  simpl. case_split_names n m. apply neq_lt_or_gt in H0. destruct H0.
  rewrite -> nat_compare_gt_gt; auto. simpl. rewrite -> nat_compare_eq_eq.
  apply open_id; auto.
  rewrite -> nat_compare_lt_lt; auto. simpl. rewrite -> nat_compare_eq_eq.
  apply open_id; auto.

  case_split_names n n0. simpl. rewrite -> nat_compare_eq_eq; auto.
  simpl. repeat rewrite -> nat_compare_lt_lt; auto.
  simpl. rewrite -> nat_compare_gt_gt with (n:=n0); auto.
  rewrite -> nat_compare_lt_lt; auto.

  case_split_names n n0. simpl. rewrite -> nat_compare_eq_eq; auto.
  simpl. rewrite -> nat_compare_lt_lt with (n:=n0); auto.
  rewrite -> nat_compare_gt_gt; auto.      
  simpl. repeat rewrite -> nat_compare_gt_gt; auto.
  
  simpl; auto.

  simpl in *. rewrite -> IHt; auto.
  simpl in *. rewrite -> IHt; auto.
  
  simpl. 
  rewrite -> IHt1; auto.
  rewrite -> IHt2; auto.

  simpl. rewrite -> IHt; auto.
  simpl; auto.
Qed.

Lemma open_eq_trmc : forall t n x,
  open_t n (trm_fvar x) t = trm_c
  -> t = trm_c.
Proof.
  destruct t; intros; simpl in *; try clarify_compares_natc; 
    try smash_trm_typ_contra; auto.
Qed.

Lemma close_comm : forall t,
  forall x y n m,
    x <> y ->
    n <> m ->
    close_t n x (close_t m y t) = close_t m y (close_t n x t).
Proof.
  induction t; intros; simpl in *; auto.

  case_split_names n y. apply neq_lt_or_gt in H. destruct H.
  rewrite -> nat_compare_gt_gt; auto. simpl. rewrite -> nat_compare_eq_eq; auto.
  rewrite -> nat_compare_lt_lt; auto. simpl. rewrite -> nat_compare_eq_eq; auto.

  simpl. case_split_names n x. simpl; auto.
  simpl. rewrite -> nat_compare_lt_lt; auto. 
  simpl. rewrite -> nat_compare_lt_lt; auto. 

  simpl. case_split_names n x. simpl; auto.
  simpl. rewrite -> nat_compare_gt_gt; auto. 
  simpl. rewrite -> nat_compare_gt_gt; auto. 

  rewrite -> IHt; auto.
  rewrite -> IHt; auto.

  rewrite -> IHt1; auto.
  rewrite -> IHt2; auto.

  rewrite -> IHt; auto.
Qed.
Hint Rewrite close_comm : base0. 
