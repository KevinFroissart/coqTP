(* Nom : kkk 
   Prenom : aa
   Num etudiant : pp *)


(***************************** LIFLF - TPX ************************************)
(************* Evaluation pratique en temps limité : 30' **********************)
(******************************************************************************)

Require Import List.
Import ListNotations.


(***************************** fonction mystère *******************************)

(* On donne le corps suivant d'une fonction

  match x with
   | Some x => [x]
   | None   => []
  end.
*)

(* EXERCICE : Définir la fonction "mystere" avec le corps donné ci-dessus. *)
(*            Donner son type *)
(*            Expliquer simplement ce que fait cette fonction. *)
(* la fonction construit une liste de [x] si la valeure n'est pas nulle, et renvoie 
la liste vide dans le cas ou la valeure est vide [] *)

Print nat.

(* mystere option nat liste vide Some None *)

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

(* paire list pair nat bool ++ concat list *)

Fixpoint zip (l1 : list nat) (l2 : list bool) : list (nat * bool) :=
  match l1 with
  | [] => []
  | x::l1' => match l2 with
              | [] => []
              | y::l2' => [(x,y)] ++ (zip l1' l2')
              end
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

Print fst. (*element gauche d'une paire*)
Print snd. (*element droite d'une paire*)

(* pair list paire liste fst snd droite gauche x,y y,x *)

Fixpoint unzip (ls : list (nat*bool)) : list nat * list bool :=
  match ls with
  | [] => ([],[])
  | n::l => match n with
            | (nn,bb) => ( [nn] ++ fst (unzip l), [bb] ++ snd (unzip l))
            end
  end.
  
Goal  unzip [(1, true); (2, false)] = ([1; 2], [true; false]).
reflexivity.
Qed.

(*********************** explication d'énoncé *********************************)

(* EXERCICE : On donne l'énoncé suivant "a_expliquer". 
              Expliquer en français cette propriété
*)
Lemma a_expliquer : forall ls, (fun p => zip (fst p) (snd p)) (unzip ls) = ls.
Admitted.


(* c'est le theorem qui verfie que pour tout liste donnees si on zip, ensuite unzip un liste,
on retombe sur notre liste de depart, cela permet de bien verifier que nos fonctions fonctionne correctement. *)
