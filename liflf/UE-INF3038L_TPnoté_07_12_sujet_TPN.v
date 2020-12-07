
(******************************************************************************)
(**************** LIFLF - TP noté - lundi 7 décembre 2020 *********************)
(*************** Evaluation pratique en temps limité : 45' ********************)
(******************************************************************************)

(* QUESTION 1 *)
(* À REPONDRE SUR UNE FEUILLE DE PAPIER, dont vous téléverserez un scan dans Tomuss à 8h10 au plus tard
                                         dans la case "TPnoté_07/12_copie1". *)

(* Soit l'alphabet {a,b}. Soit L le langage des mots commençant par aab.
     a) Définissez l'automate à états finis déterministe complet qui accepte L.
     b) Donnez une expression rationnelle correspondant à L.
     c) Définissez une grammaire régulière qui génère L. *)

(* La suite se fera en complétant ce fichier .v, qui sera à téléverser dans Tomuss à 8h45 au plus tard. *)

(* Définitions nécessaires pour la suite des exercices *)

Inductive Alphabet : Type :=
| a : Alphabet
| b : Alphabet.
Definition comp_alphabet (x y : Alphabet) : bool :=
  match (x,y) with
  | (a,a) => true
  | (b,b) => true
  | (_,_) => true
end.
Require Export List.
Import ListNotations.
Fixpoint appartient (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | h::rl => (Nat.eqb x h) || (appartient x rl)
  end.
Fixpoint trouve (assoc : list (Alphabet * nat)) (key : Alphabet) : option nat :=
  match assoc with
    | [] => None
    | h::rassoc => if (comp_alphabet key (fst h)) then (Some (snd h))
                   else trouve rassoc key
  end.
Inductive Automate : Type :=
    automate : list nat -> list Alphabet -> (nat -> Alphabet -> option nat) -> nat -> list nat -> Automate.
Definition etats (M : Automate) :  list nat :=
  match M with
    automate ql _ _ _ _ => ql
  end.
Definition symboles (M : Automate) :  list Alphabet :=
  match M with
    automate _ sigma _ _ _ => sigma
  end.
Definition initial  (M : Automate) :  nat :=
  match M with
    automate _ _ _ q0 _ => q0
  end.
Definition acceptant  (M : Automate) (q : nat) : bool  :=
  match M with
    automate _ _ _ _ lF => (appartient q lF)
  end.
Definition transition  (M : Automate) (q : nat) (c : Alphabet) : option nat :=
  match M with
    automate _ _ f _ _ => f q c
  end.
Fixpoint execute (M : Automate)  (q : nat) (w : list Alphabet) : option nat :=
  match w with
  | [] => Some q
  | h::rw => match transition M q h with
             | None => None
             | Some e => execute M e rw end
  end.
Definition reconnait (M : Automate) (w : list Alphabet) : bool :=
  match (execute M (initial M) w) with
  | None => false
  | Some e => acceptant M e
  end.


(* À REPONDRE EN COMPLÉTANT DIRECTEMENT CE FICHIER, que vous téléverserez dans Tomuss à 8h45 au plus tard
                                                    dans la case "TPnoté_07/12_copie2". *)

(* QUESTION 2a *)
(* Définissez l'automate complet "M_commence_par_aab" à cinq états qui accepte le langage L. *)
Definition delta_commence_par_aab (q : nat) (c : Alphabet) : option nat :=
match (q,c) with
 | (1,a) => Some 2
 | (1,b) => Some 5
 | (2,a) => Some 3
 | (2,b) => Some 5
 | (3,a) => Some 5
 | (3,b) => Some 4
 | (4,a) => Some 4
 | (4,b) => Some 5
 | (5,a) => Some 5
 | (5,b) => Some 5
 | (_,_) => None
end.

Definition M_commence_par_aab := automate [1;2;3;4] [a;b] (delta_commence_par_aab) 1 [4].

(* QUESTION 2b *)
(* Vérifiez que votre automate accepte les mots aab et aabaa, et refuse le mot vide et le mot bba. *)

Example M_commence_par_aab_refuse_vide : reconnait M_commence_par_aab [] = false.
cbv. reflexivity. Qed.

Example M_commence_par_aab_reconnait_aab : reconnait M_commence_par_aab [a;a;b] = true.
cbv. reflexivity. Qed.

Example M_commence_par_aab_reconnait_aabaa : reconnait M_commence_par_aab [a;a;b;a;a] = true.
cbv. reflexivity. Qed.

(* QUESTION 3a *)
(* Définissez "G_commence_par_aab" le PREDICAT "mot généré par G_commence_par_aab à partir du non-terminal i",
   correspondant à la grammaire générant le langage L. *)
(* Décommentez et complétez. *)
Inductive G_commence_par_aab : (list Alphabet) -> nat -> Prop := 
| G_commence_par_aab_0 : G_commence_par_aab [] 4
| G_commence_par_aab_1a : forall m, G_commence_par_aab m 2 -> G_commence_par_aab (a::m) 1 
| G_commence_par_aab_1b : forall m, G_commence_par_aab m 5 -> G_commence_par_aab (b::m) 1 
| G_commence_par_aab_2a : forall m, G_commence_par_aab m 3 -> G_commence_par_aab (a::m) 2
| G_commence_par_aab_2b : forall m, G_commence_par_aab m 5 -> G_commence_par_aab (b::m) 2
| G_commence_par_aab_3a : forall m, G_commence_par_aab m 5 -> G_commence_par_aab (a::m) 3
| G_commence_par_aab_3b : forall m, G_commence_par_aab m 4 -> G_commence_par_aab (b::m) 3
| G_commence_par_aab_4a : forall m, G_commence_par_aab m 4 -> G_commence_par_aab (a::m) 4
| G_commence_par_aab_4b : forall m, G_commence_par_aab m 4 -> G_commence_par_aab (b::m) 4
| G_commence_par_aab_5a : forall m, G_commence_par_aab m 5 -> G_commence_par_aab (a::m) 5
| G_commence_par_aab_5b : forall m, G_commence_par_aab m 5 -> G_commence_par_aab (b::m) 5
.
(* QUESTION 3b *)
(* Vérifiez que votre grammaire génère les mots aab et aabaaa à partir du non-terminal 1 *)

Example ex_G_commence_par_aab_1 : G_commence_par_aab [a;a;b] 1.
Proof.
  apply G_commence_par_aab_1a.
  apply G_commence_par_aab_2a.
  apply G_commence_par_aab_3b.
  apply G_commence_par_aab_0.
Qed.

Example G_commence_par_aab_1 : G_commence_par_aab [a;a;b;a;a;a] 1.
Proof.
  apply G_commence_par_aab_1a.
  apply G_commence_par_aab_2a.
  apply G_commence_par_aab_3b.
  apply G_commence_par_aab_4a.
  apply G_commence_par_aab_4a.
  apply G_commence_par_aab_4a.
  apply G_commence_par_aab_0.
Qed.

(*----------------------------------------------------------------------------*)

(* QUESTION 4a *)
(* Définissez un type "oiseau" avec trois éléments albatros, pigeon, manchot. *)

Inductive oiseau : Type :=
  | albatros : oiseau
  | pigeon : oiseau
  | manchot : oiseau.

(* QUESTION 4b *)
(* Définissez une fonction "comp_Oiseau" de comparaison de ce type. *)

Definition comp_Oiseau (O1 O2: oiseau) : bool :=
  match O1, O2 with
  | albatros, albatros => true
  | pigeon,   pigeon   => true 
  | manchot,  manchot  => true
  | _,        _        => false
  end.

(* QUESTION 4c *)
(* Prouvez que votre fonction de comparaison est correcte. *)

Lemma comp_Oiseau_correct : forall x y, (comp_Oiseau x y) = true -> y = x.
Proof.
destruct x.
destruct y.
- simpl. reflexivity.
- discriminate.
- discriminate.
- destruct y.
  + discriminate.
  + reflexivity.
  + discriminate.
- destruct y.
  + discriminate.
  + discriminate.
  + reflexivity.
Qed.


(* QUESTION 4d *)
(* Prouvez que votre fonction de comparaison est complète. *)

Lemma comp_Oiseau_complet : forall x y, y = x -> (comp_Oiseau x y) = true.
Proof.
destruct x.
destruct y.
- reflexivity.
- discriminate.
- discriminate.
- destruct y.
  + discriminate.
  + reflexivity.
  + discriminate.
- destruct y.
  + discriminate.
  + discriminate.
  + reflexivity.
Qed.

(*----------------------------------------------------------------------------*)


(* QUESTION 5a *)
(* Définissez la fonction "take" qui prend en paramètre un entier n et une liste ls
              et retourne le préfixe de ls de longueur n.
   EXEMPLE : voir les tests unitaires ci-dessous
*)
Fixpoint take (n: nat) (ls: list nat) : list nat :=
  match ls with
  | [] => []
  | n'::l' => if (Nat.eqb n 0) then [] else n'::[] ++ (take (n-1) l')
  end.

(* Décommentez les exemples *)

Goal  take 0 [1;2;3;4;5] = [].
reflexivity.
Qed.

Goal  take 6 [1;2;3;4;5] = [1;2;3;4;5].
reflexivity.
Qed.

Goal  take 3 [1;2;3;4;5] = [1;2;3].
reflexivity.
Qed.



(* QUESTION 5b *)
(* Définissez la fonction "drop" qui prend en paramètre un entier n et une liste ls
              et retourne le suffixe de ls privée de ses n premiers éléments.
   EXEMPLE : voir les tests unitaires ci-dessous
*)
Fixpoint drop (n: nat) (l: list nat) : list nat :=
  match l with
  | [] => []
  | n'::l' => if (Nat.eqb n 0) then l else drop (n-1) l'
  end.

(* Décommentez les exemples *)

Goal  drop 0 [1;2;3;4;5] = [1;2;3;4;5].
reflexivity.
Qed.

Goal  drop 6 [1;2;3;4;5] = [].
reflexivity.
Qed.

Goal  drop 3 [1;2;3;4;5] = [4;5].
reflexivity.
Qed.


(*----------------------------------------------------------------------------*)
