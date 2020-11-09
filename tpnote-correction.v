Require Import Arith.
Require Import List.
Export ListNotations.

(* LANGAGES FORMELS *)

(* EXERCICE *)
(* Écrire la fonction "lgr" qui calcule la longueur d'une liste de nat (et donc de type list nat) *)
Fixpoint lgr (l : list nat) := match l with [] => 0 | _::rl => 1 + (lgr rl) end.

Example ex_lgr : (lgr (1::2::3::4::5::[])) = 5.
Proof. simpl. reflexivity. Qed.

(* EXERCICE *)
(* Écrire la fonction "mir" qui calcule le miroir d'une liste de nat *)
Fixpoint mir (l : list nat) := match l with [] => [] | e::rl => (mir rl) ++ e::[] end.

Example ex_mir : (mir (1::2::3::4::5::[])) = 5::4::3::2::1::[].
Proof. simpl. reflexivity. Qed.


(* EXERCICE *)
(* Exprimer et prouver que le miroir d'une liste à laquelle on a ajouté un élément en tête
   est le miroir de la liste concaténé à la liste constituée de juste cet élément *)
Goal forall l : list nat, forall a : nat, rev (a :: l) = (rev l) ++ a::[].
Proof.
  intro l0.
  intro a0.
  destruct l0. (* pas besoin d'hyp. d'induction *)
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* EXERCICE SUJET A *)
Inductive btree : Type :=
| F : nat -> btree
| N : btree -> btree -> btree
.

(* Écrire la fonction "bnbf" qui calcule le nombre de feuilles d'un tel arbre *)
Fixpoint bnbf t :=
  match t with
  | F e => 1
  | N t1 t2 => (bnbf t1) + (bnbf t2)
  end.

(* Écrire la fonction "bnbn" qui calcule le nombre de noeuds d'un tel arbre *)
Fixpoint bnbn t :=
  match t with
  | F e => 0
  | N t1 t2 => 1 + (bnbn t1) + (bnbn t2)
  end.

(* Écrire la fonction "bsumval" qui calcule la somme des valeurs contenues dans l'arbre *)
Fixpoint bsumval t :=
  match t with
  | F e => e
  | N t1 t2 => (bsumval t1) + (bsumval t2)
  end.

(* Écrire la fonction "bajout" qui ajoute un élément dans un arbre *)
Fixpoint bajout e t : btree :=
  match t with
  | F n => N t (F e)
  | N t1 t2 => N (bajout e t1) t2
  end.

(* exemples *)
(* Définir l'arbre "ab1" :  o
                           / \
                          o   2
                         / \
                        1   o
                           / \
                          o   3
                         / \
                        4   5
*)

Definition ab1 := N (N (F 1) (N (N (F 4) (F 5)) (F 3))) (F 2).

Example ex_bnbf_ab1 : (bnbf ab1) = 5.
Proof. cbv. reflexivity. Qed.

Example ex_bnbn_ab1 : (bnbn ab1) = 4.
Proof. cbv. reflexivity. Qed.

Example ex_bsumval_ab1 : (bsumval ab1) = 15.
Proof. cbv. reflexivity. Qed.

Example ex_bajout_ab1 : bnbf (bajout 10 ab1) = 1 + bnbf ab1.
Proof. cbv. reflexivity. Qed.



(* EXERCICE SUJET B *)
Inductive ctree : Type :=
| V : nat -> ctree
| R : ctree -> ctree -> ctree
| T : ctree -> ctree -> ctree -> ctree
.

(* Ecrire la fonction "cnbf" qui calcule le nombre de feuilles d'un tel arbre *)
Fixpoint cnbf t :=
  match t with
  | V e => 1
  | R t1 t2 => (cnbf t1) + (cnbf t2)
  | T t1 t2 t3 => (cnbf t1) + (cnbf t2) + (cnbf t3)
  end.

(* Ecrire la fonction "cnbn" qui calcule le nombre de noeuds d'un tel arbre *)
Fixpoint cnbn t :=
  match t with
  | V e => 0
  | R t1 t2 => 1 + (cnbn t1) + (cnbn t2)
  | T t1 t2 t3 => 1 + (cnbn t1) + (cnbn t2) + (cnbn t3)
  end.


(* Ecrire la fonction "csumval" qui calcule la somme des valeurs contenues dans l'arbre *)
Fixpoint csumval t :=
  match t with
  | V e => e
  | R t1 t2 => (csumval t1) + (csumval t2)
  | T t1 t2 t3 => (csumval t1) + (csumval t2) + (csumval t3)
  end.


(* Ecrire la fonction "bajout" qui ajoute un élément dans un arbre *)
Fixpoint cajout e t : ctree :=
  match t with
  | V n => R t (V e)
  | R t1 t2 => R (cajout e t1) t2
  | T t1 t2 t3 => T (cajout e t1) t2 t3
  end.

(* exemples *)
(* Définir l'arbre "ac1" : o
                           / \
                          o   7
                         /|\
                        1 2 o
                           /|\
                          o 6 3
                         / \
                        4   5
*)
Definition ac1 := R (T (V 1) (V 2) (T (R (V 4) (V 5)) (V 6) (V 3))) (V 2).

Example ex_cnbf_ab1 : (bnbf ab1) = 5.
Proof. cbv. reflexivity. Qed.

Example ex_cnbn_ab1 : (bnbn ab1) = 4.
Proof. cbv. reflexivity. Qed.

Example ex_csumval_ab1 : (bsumval ab1) = 15.
Proof. cbv. reflexivity. Qed.

Example ex_cajout_ab1 : bnbf (bajout 10 ab1) = 1 + bnbf ab1.
Proof. cbv. reflexivity. Qed.



(* LOGIQUE CLASSIQUE *)

Context (A B C D : Prop).

(* EXERCICE *)
(* Prouver les lemmes suivants (permutation et renommage dans les deux sujets) *)
Lemma LC1 : ((A \/ B) -> C) -> ((A -> C) /\ (B -> C)).
Proof.
  intro Himp.
  split.
  - intro Ha. apply Himp. left. assumption.
  - intro Hb. apply Himp. right. assumption.
Qed.


Lemma LC2 : (A \/ B) -> ((A -> B) -> B).
Proof.
  intro Hou.
  intro Hab.
  destruct Hou. (* on l'a fait 10 fois... *)
  - apply Hab. assumption.
  - assumption.
Qed.


(* EXERCICE *)
(* Exprimer et montrer que la longueur de la concaténation de deux listes de nat est la somme des longueurs des concaténés*)
Lemma concat_compat : forall l1 l2 : list nat, lgr (l1 ++ l2) = (lgr l1) + (lgr l2).
Proof.
  intro l1.
  intro l2.
  induction l1  as [| a l1' IHl1']. (* ou avec noms automatiques *)
  - simpl. reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

(* EXERCICE *)
(* Montrer que la longueur d'une liste c'est la longueur de son miroir *)
(* On pourra avoir besoin de la commutativité de l'addition, donnée par le lemme Nat.add_comm, et dulemme précédent *)

Check Nat.add_comm.

Lemma lgrmir_compat : forall l : list nat,  lgr l = lgr (mir l).
Proof.
  induction l as [| a l' IHl']. (* ou avec noms automatiques  *)
  - simpl. reflexivity.
  - simpl.
    rewrite IHl'.
    rewrite (concat_compat (mir l') (a::[])). (* ou bien avec l'étape intermédiaire "pose" etc. *)
    simpl.
    rewrite (Nat.add_comm (lgr (mir l')) 1). (* oups ça n'est pas dans le bon sens *)
    simpl.
    reflexivity.
Qed.

(* EXERCICE *)
(* Exprimer et montrer que l'addition est associative, c'est-à-dire qu'on a (x + y) + z = x + (y + z) pour x, y et z de type nat. *)
(* rappel : ce qui est noté x + y + z (sans parenthèses) est en fait (x + y) + z *)
Lemma p_assoc : forall x y z : nat, x + y + z = x + (y + z).
  intro x0.
  intro y0.
  intro z0.
  induction x0 as [| x0' IHx0']. (* ou avec noms automatiques *)
  - simpl. reflexivity.
  - simpl. rewrite IHx0'. reflexivity.
Qed.


(* EXERCICE SUJET A *)
(* Exprimer et montrer que la somme des valeurs d'un arbre t à laquelle on additionne un nat e est égale à la somme des valeurs de l'arbre t dans lequel on a ajouté un élément de valeur e. *)

(* On pourra avoir besoin de la commutativité de l'addition, donnée par le lemme Nat.add_comm, et de l'associativité démontrée auparavant. *)

Check Nat.add_comm.

Lemma bsumaj_compat : forall t, forall e, bsumval t + e = bsumval (bajout e t).
  intro t0.
  intro e0. 
  induction t0 as [n | t1 IHt1 t2 IHt2] . (* ou avec noms automatiques *)
  - simpl. reflexivity.
  - simpl. rewrite <- IHt1. (* on a à droite (a + b) + c et on veut (a + c) + b il faut donc 1) déplacer les parenthèses, permuter, replacer les parenthèses *)
    rewrite (p_assoc (bsumval t1) e0 (bsumval t2)).
    rewrite (Nat.add_comm e0 (bsumval t2)).
    rewrite (p_assoc (bsumval t1) (bsumval t2) e0).
    reflexivity.
Qed.

(* EXERCICE SUJET B *)
(* Exprimer et montrer que la somme des valeurs d'un arbre t à laquelle on additionne un nat e est égale à la somme des valeurs de l'arbre t dans lequel on a ajouté un élément de valeur e. *)

(* On pourra avoir besoin de la commutativité de l'addition, donnée par le lemme Nat.add_comm, et de l'associativité démontrée auparavant. *)

Check Nat.add_comm.


(* La même avec une étape en plus puisqu'on a 3 constructeurs pour les arbres *)
Lemma csumaj_compat : forall t, forall e, csumval t + e = csumval (cajout e t).
  intro t0.
  intro e0.
  induction t0 as [n | t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2 t3 IHt3]. (* ou avec noms automatiques *)
  - simpl. reflexivity.
  - simpl. rewrite <- IHt1.
    rewrite (p_assoc (csumval t1) e0 (csumval t2)).
    rewrite (Nat.add_comm e0 (csumval t2)).
    rewrite (p_assoc (csumval t1) (csumval t2) e0).
    reflexivity.
  - simpl. rewrite <- IHt1. (* on a ((a + b) + c) + d et on veut ((a + c )+ d) + b, on déplace les parenthèses et on commute en conséquence *)
    rewrite (p_assoc (csumval t1 + e0) (csumval t2) (csumval t3)). (* (a + b) + (c + d) *)
    rewrite (p_assoc (csumval t1) e0 (csumval t2 + csumval t3)).   (* a + (b + (c + d)) *)
    rewrite (Nat.add_comm e0 (csumval t2 + csumval t3)).           (* on permute *)
    rewrite (p_assoc (csumval t1) (csumval t2) (csumval t3)).      (* on remonte les parenthèses à gauche... *)
    rewrite (p_assoc (csumval t1) (csumval t2 + csumval t3) e0).
    reflexivity.
Qed.


