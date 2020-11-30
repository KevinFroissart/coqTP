


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
Proof.
unfold not.
intros.
destruct H.
apply H.
destruct H0.
assumption.
apply H.
destruct H0.
assumption.
Qed.

End PL. 

(******************************************************************************)
(* Les listes *)
(******************************************************************************)

Print length. (* la longueur de listes *)

(* EXERCICE :  énoncer le lemme "mystere" en langue naturelle *)
Lemma mystere A:  forall l : list A, length l = 0 <-> l = nil.
Proof.
induction l; split.
- simpl. reflexivity.
- simpl. reflexivity.
- intros. discriminate H.
- simpl. intros. discriminate H.
Qed.

Goal 1 = 0 -> 42 = 3.
Proof.
intros.
discriminate H.
Qed.



(* EXERCICE :  prouver le lemme "mystere"  SANS UTILISER "Require Import List." *)