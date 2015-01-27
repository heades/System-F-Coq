Require Import F.
Require Import names.
Require Import subst.

Lemma weakening_typing : forall G1 G2 G3 t T,
  (G1++G3) :> t ; T ->
  Ok (G1++G2++G3) -> 
  (G1 ++ G2 ++ G3) :> t ; T.
Proof. admit. Qed.