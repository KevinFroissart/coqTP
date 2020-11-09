


(***************************** LIFLF - TPNOTE *********************************)
(************* Evaluation pratique en temps limité : 30' **********************)

(************************ SUJET D'ENTRAINEMENT ********************************)
(* Ce sujet est représentatif de celui qui vous sera donné à réaliser en temps 
limité. Les fonctions lemmes demandés ici sont tout à fait classiques.
*)
Require Import Utf8.


(******************************************************************************)
(* Logique propositionnelle *)
(******************************************************************************)
Section PL.

Context (P Q : Prop).

(* EXERCICE : prouver la propriété suivante SANS UTILISER UNE TACTIQUE AUTOMATIQUE *)
Lemma de_morgan : (~P \/ ~Q) -> ~(P /\ Q).
intros.
unfold not.
intros.
unfold not in H.
destruct H0.
destruct H.
- apply H.
  assumption.
- apply H.
  assumption.
Qed.

End PL. 

(******************************************************************************)
(* Les listes *)
(******************************************************************************)

Print length. (* la longueur de listes *)

Print list.

(* EXERCICE :  énoncer le lemme "mystere" en langue naturelle *)
(*
Lemma mystere A:  forall l : list A, length l = 0 <-> l = nil.
Admitted.
*)
(*
Pour toute liste de A 'l : "list A"', sa longueur ("length l") = 0 ssi elle est vide ("l = nil").
*)

(* EXERCICE :  prouver le lemme "mystere"  SANS UTILISER "Require Import List." *)
Lemma mystere A:  forall l : list A, length l = 0 <-> l = nil.
split.
- intros.
  destruct l.
  + reflexivity.
  + simpl in H.
    discriminate H.
- intros.
  rewrite H.
  simpl.
  reflexivity.
Qed.