
(***************************** LIFLF - TPA ************************************)
(************* Evaluation pratique en temps limité : 30' **********************)
(******************************************************************************)

Require Import Arith.
Require Import List.
Export ListNotations.


(* Partie 1. Exercices sur les listes d'entiers *)
(* -------------------------------------------- *)


(* EXERCICE *)
(* Écrire la fonction "lgr" qui calcule la longueur d'une liste de nat (et donc de type list nat) *)

Fixpoint lgr (l: list nat) : nat :=
match l with
| [] => 0
| n::l' => 1 + (lgr l')
end.

Example ex_lgr : (lgr (1::2::3::4::5::[])) = 5.
Proof. cbv. reflexivity. Qed.


(* EXERCICE *)
(* Écrire la fonction "mir" qui calcule le miroir d'une liste de nat *)

Fixpoint mir (l: list nat) : list nat :=
match l with
| [] => []
| n::l' => (mir l') ++ [n]
end.


Example ex_mir : (mir (1::2::3::4::5::[])) = 5::4::3::2::1::[].
Proof. cbv. reflexivity. Qed.



(* EXERCICE *)
(* Exprimer et prouver que le miroir d'une liste à laquelle on a ajouté un élément en tête
   est le miroir de la liste concaténé à la liste constituée de juste cet élément *)

Theorem mir_correct : (mir (1::2::3::4::5::[]))++[6] = 5::4::3::2::1::6::[].
Proof. cbv. reflexivity. Qed.

(* Partie 2. Exercices sur les arbres binaires *)
(* ------------------------------------------- *)


(* On donne le type "btree" des arbres binaires avec valeurs de type nat stockées dans les feuilles *)
Inductive btree : Type :=
| F : nat -> btree
| N : btree -> btree -> btree
.

(* exemples *)
(* L'arbre "ab1" :  o    et "ab2" :    o
                   / \                / \
                  o   2              1   o
                 / \                    / \
                1   o                  o   5
                   / \                / \
                  o   3              2   o
                 / \                    / \
                4   5                  3   4
*)
(* On donne l'arbre "ab1" : *)
Definition ab1 := N (N (F 1) (N (N (F 4) (F 5)) (F 3))) (F 2).

(* EXERCICE *)
(* Définir l'arbre "ab2" correspondant à l'exemple ci-dessus *)

Definition ab2 := N (F 1) (N (N (F 2) (N (F 3) (F 4))) (F 5) ).

(* EXERCICE *)
(* Écrire la fonction "bnbf" qui calcule le nombre de feuilles d'un tel arbre *)

Fixpoint bnbf (b: btree) : nat :=
match b with
| F n => 1
| N l r => (bnbf l) + (bnbf r)
end.


Example ex_bnbf_ab1 : (bnbf ab1) = 5.
Proof. cbv. reflexivity. Qed.



(* EXERCICE *)
(* Écrire la fonction "bnbn" qui calcule le nombre de noeuds d'un tel arbre *)

Fixpoint bnbn (b: btree) : nat :=
match b with
| F n => 0
| N l r => 1 + (bnbn l) + (bnbn r)
end.


Example ex_bnbn_ab1 : (bnbn ab1) = 4.
Proof. cbv. reflexivity. Qed.



(* EXERCICE *)
(* Écrire la fonction "bsumval" qui calcule la somme des valeurs contenues dans l'arbre *)

Fixpoint bsumval (b: btree) : nat :=
match b with
| F n => n
| N l r => (bsumval l) + (bsumval r)
end.


Example ex_bsumval_ab1 : (bsumval ab1) = 15.
Proof. cbv. reflexivity. Qed.



(* EXERCICE *)
(* Écrire la fonction "bajout" qui ajoute un élément dans un arbre *)

Fixpoint bajout (m: nat) (b: btree) : btree :=
match b with
| F n => N (F m) (F n)
| N l r => N (bajout m l) r
end.


Example ex_bajout_ab1 : bnbf (bajout 10 ab1) = 1 + bnbf ab1.
Proof. cbv. reflexivity. Qed.



