
(***************************** LIFLF - TPX ************************************)
(************* Evaluation pratique en temps limité : 30' **********************)
(******************************************************************************)

Require Import List.
Import ListNotations.


(***************************** fonction mystère *******************************)

Print nat.

(* EXERCICE : Définir la fonction "mystere" avec le corps donné ci-dessus. *)
(*            Donner son type *)
(*            Expliquer simplement ce que fait cette fonction. *)
Definition mystere (x: option nat) : list nat :=
    match x with
   | Some x => [x]
   | None   => []
  end.

(***************************** "zip" ******************************************)

(* EXERCICE : définir la fonction "zip" qui prend en paramètre une paire de listes
              et retourne la liste de paires correspondantes
   EXEMPLE  : voir les tests unitaires ci-dessous
*)

Print list.

Fixpoint zip {A B} (l1: list A) (l2: list B) : list (A*B) := 
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x::lx, y::ly => (x,y)::(zip lx ly)
  end.

Goal  zip [1; 2] [true; false] = [(1, true); (2, false)].
reflexivity.
Qed.

Goal  zip [1] [true; false] = [(1, true)].
reflexivity.
Qed.

Goal  zip [1; 2] [true] = [(1, true)].
reflexivity.
Qed.

(***************************** "unzip" ****************************************)

(* EXERCICE : définir la fonction "unzip" qui prend en paramètre
              une liste de paires et retourne la paire de listes correspondantes
   EXEMPLE  : voir les tests unitaires ci-dessous
*)


Fixpoint unzip ??? : ??? := ???



Goal  unzip [(1, true); (2, false)] = ([1; 2], [true; false]).
reflexivity.
Qed.

(*********************** explication d'énoncé *********************************)

(* EXERCICE : On donne l'énoncé suivant "a_expliquer". 
              Expliquer en français cette propriété
*)
Lemma a_expliquer : forall ls, (fun p => zip (fst p) (snd p)) (unzip ls) = ls.
Admitted.

