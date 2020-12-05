
(***************************** LIFLF - TPX ************************************)
(************* Evaluation pratique en temps limité : 30' **********************)
(******************************************************************************)

Require Import List.
Import ListNotations.

(***************************** fonction mystère *******************************)

(* On donne le corps suivant d'une fonction

  match ls with
   | []     => None
   | x::xs  => Some x
  end.
*)

(* EXERCICE : Définir la fonction "mystere" avec le corps donné ci-dessus. *)
(*            Donner son type *)
(*            Expliquer simplement ce que fait cette fonction. *)

Definition mystere (ls : list nat) : option nat :=
match ls with
   | []     => None
   | x::xs  => Some x
  end.

(***************************** "take" *****************************************)

(* EXERCICE : définir "take n ls" qui renvoie le préfixe de ls de longueur n
   EXEMPLE  : voir les tests unitaires ci-dessous
*)

(* nombre element liste list nb elem concat list ++ :: n-1*)

Fixpoint take (n: nat) (ls: list nat) : list nat :=
  match ls with
  | [] => []
  | n'::l' => if (Nat.eqb n 0) then [] else n'::[] ++ (take (n-1) l')
  end.

Goal  take 0 [1;2;3;4;5] = [].
simpl.
reflexivity.
Qed.

Goal  take 6 [1;2;3;4;5] = [1;2;3;4;5].
simpl.
reflexivity.
Qed.

Goal  take 3 [1;2;3;4;5] = [1;2;3].
simpl.
reflexivity.
Qed.

Print app.

(***************************** "drop" *****************************************)

(* EXERCICE : définir "drop n ls" qui renvoie le suffixe de ls privée de ses n 
              premiers éléments
   EXEMPLE  : voir les tests unitaires ci-dessous
*)

(* enlever element liste list drop elements number list*)

Fixpoint drop (n: nat) (l: list nat) : list nat :=
  match l with
  | [] => []
  | n'::l' => if (Nat.eqb n 0) then l else drop (n-1) l'
  end.


Goal  drop 0 [1;2;3;4;5] = [1;2;3;4;5].
simpl.
reflexivity.
Qed.

Goal  drop 6 [1;2;3;4;5] = [].
simpl.
reflexivity.
Qed.

Goal  drop 3 [1;2;3;4;5] = [4;5].
simpl.
reflexivity.
Qed.

(*********************** explication d'énoncé *********************************)


(* EXERCICE : On donne l'énoncé suivant "a_expliquer". 
              Expliquer en français cette propriété
*)
Lemma a_expliquer : forall n la, (fun p => app (fst p) (snd p) ) (take n la, drop n la) = la. 
Admitted.

(* c'est le theoreme qui verifie que pour tout entier n et tout liste la si on applique 
take et drop en parallele sur la meme liste, le resultat de leurs deux liste concatenes
revient a la liste de depart la*)

Compute (take 3 [1;2;3;4;5;6]).
Compute (drop 3 [1;2;3;4;5;6]).
Compute (take 3 [1;2;3;4;5;6]) ++ (drop 3 [1;2;3;4;5;6]).
Compute (a_expliquer 3 [1;2;3;4;5;6]).

