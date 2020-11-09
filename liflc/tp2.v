Require Import Arith.

(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)





(**********************************************************************)
(* STRUCTURE DE BASE DES LISTES (FINIES) D'ENTIERS                    *)
(**********************************************************************)


(*On rappelle que les objets de type nat sont définis inductivement de façon similaire à 
Inductive entiers : Set :=
  | O : entiers
  | S : entiers -> entiers.
*)
Print nat.

(* On dispose d'un principe d'induction nat_ind, construit à peu près comme vu en cours *)
Check nat_ind.

(* EN COQ : l'application de la tactique "induction" sur un nom
   d'entier produira donc DEUX sous-buts (il y a bien 2 règles de
   construction des entiers...) :
  - Le sous-but correspondant au cas de bas O, 
  - Le sous-but correspondant au cas inductif où l'hypothèse d'induction apparaît
    dans le contexte.  *)



(* On définit les listes de nat *)
Inductive nlist : Set :=
| nnil : nlist                  
| ncons : nat -> nlist -> nlist. 

(* ... avec des notations confortables *)
Infix "::" := ncons.
Notation "[]" := nnil.

(* Vous avez vu la génération des principes d'induction ? elle est tout à fait similaire à ce qui s'est passé pour les entiers. *)
Check nlist_ind.


(* EN COQ :  des CONSTRUCTEURS DIFFÉRENTS donnent des TERMES DIFFÉRENTS. 
Une hypothèse de la forme X = Y où X et Y ont des constructeurs différents est donc absurde,
on peut alors clore le but avec la tactique "discriminate". *)

(* Prouver que pour tout nat x et toute liste de nat l,
la liste vide n'est pas obtenue par l'ajout de x en tête de l. *)
Lemma nil_neq_cons : forall (x:nat) (l:nlist), [] = x :: l -> False.
Proof.
  intro x.
  intro l.
  intro H.
  discriminate.
Qed.


(******************************************************************************)
(* FONCTIONS NON-RECURSIVES SUR LES TYPES INDUCTIFS                           *)
(******************************************************************************)

(* SI ON N'A PAS BESOIN d'hypothèse d'induction, il est en général suffisant de faire une étude par cas, 
   c'est-à-dire un destruct de l'objet étudié *)

Inductive Alphabet : Type :=
| a : Alphabet
| b : Alphabet.

(* Prouvez la correction complète de la fonction comp_alphabet de
votre TP de LIFLF, c'est-à-dire qu'elle retourne true si et seulement
si ses paramètres sont égaux.
 - on procède par cas sur les deux paramètres 
 - on peut être amené à faire des calculs (avec simpl dans le but ou simpl in toto dans
     l'hypothèse toto. *)
Definition comp_alphabet (x : Alphabet) (y : Alphabet) : bool :=
  match x with
  | a =>  match y with  | a =>  true  | b =>  false end
  | b =>  match y with  | a =>  false  | b =>  true end
  end.  
  
Theorem comp_alphabet_ssi : forall (x : Alphabet) (y : Alphabet), comp_alphabet x y = true
  <-> x = y.
Proof.
  split.
  * intro.
    destruct  x.
    - destruct  y.
      + reflexivity.
      + simpl in  H.
        discriminate.
    - destruct y.
      + simpl in  H.
        discriminate.
      + reflexivity.
  * intro.
    rewrite H.
    destruct  y.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
Qed.


(* on rappelle la fonction de comparaison sur les option nat codée en LIFLF *)
Definition comp_option_nat (x : option nat) (y : option nat) : bool :=
match x with
  | None => match y with | None => true | Some toto => false end
  | Some n => match y with | Some m => Nat.eqb n m | None => false end
end.


(* EN COQ : si on a une hypothèse H : forall x, P(x) on peut la
 spécialiser en une nouvelle hypothèse pour une certaine valeur de x,
 disons n. Pour celà on invoque "pose (H n) as nouveauH".  On crée
 alors une nouvelle hypothèse qui s'appelle nouveauH qui est un cas
 particulier de H, celui où x vaut n : nouveauH : P(n)
*)

(* Montrer que (comp_option_nat x y) retourne true SEULEMENT SI x=y. 
   on utilisera le théorème 
   beq_nat_true: forall n m : nat, Nat.eqb n  m = true -> n = m 
   qu'on spécialisera aux bons paramètres n_fixe, m_fixe avec 
   pose (beq_nat_true n_fixe m_fixe) as nom_de_la_nouvelle_hypothèse.
   
   ATTENTION : Nat.eqb e1 e2 s'écrit aussi e1 =? e2

*)
Theorem comp_option_nat_seulement_si : forall (x y : option nat),
  (comp_option_nat x y = true) -> x = y.
Proof.
  intro x.
  intro y.
  destruct x.
  * destruct y.
    + simpl.
      intro H.
      pose (beq_nat_true n n0) as toto.
      pose (toto H) as tutu.
      rewrite tutu.
      reflexivity.
    + intro H.
      discriminate.
  * destruct y.
    + intro H.
      discriminate.
    + simpl.
      intro H.
      reflexivity.
Qed.


(******************************************************************************)
(* FONCTIONS RECURSIVES ET INDUCTION SUR LES ENTIERS                          *)
(******************************************************************************)

(* Exercice : montrer que la fonction plus appliquée à 0 et un x
   quelconque retourne x. *)
(* La définition de plus est récursive sur le paramètre de gauche,
   donc pas de problème ici, c'est juste un calcul (simpl) *)
Lemma plus_Z_l : forall (x : nat), plus 0 x = x.
Proof.
  intro x.
  simpl.
  reflexivity.
Qed.

(* Exercice : montrer que la fonction plus appliquée à un x quelconque
   et 0 retourne x. *)
(* Mmmh là il faut travailler par induction sur x... *)
(* ON UTILISE DONC "induction x". *)
Lemma plus_Z_r : forall x, plus x 0 = x.
Proof.
  intro.
  induction x.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHx.
    reflexivity.
Qed.


(******************************************************************************)
(* FONCTIONS RECURSIVES ET INDUCTION SUR LES LISTES                           *)
(******************************************************************************)


(* Exercice : définir "concat" la fonction de concaténation de deux
   listes l1 et l2 (par récursion sur l1) *)
Fixpoint concat (l1 l2 : nlist) : nlist := 
  match l1 with
   |  []  =>  l2
   | e::sl1  =>  e::(concat sl1 l2)
  end.


(* On note ++ en notation infix pour la concatenation *)
Infix "++" := concat.

(* VU EN COURS : fonction de longueur des listes      *)
Fixpoint length (l : nlist) : nat :=
  match l with
  | []     => 0 
  | x :: l => S(length l) 
  end.

(* Exercice : montrer que la fonction retourne 0 SEULEMENT SI la liste
   est vide *)
Lemma length_zero_seulement_si_vide : forall (l: nlist), (length l) = 0 -> l = [].
Proof.
  intro.
  destruct l.
  * simpl.
    intro.
    reflexivity.
  * simpl.
    intro.
    discriminate.
Qed.                                  



(* Exercice : montrer que la fonction appliquée à la concaténation de
deux listes quelconques l1 l2 retourne la somme des applications de
cette fonction à chacune des deux listes.*)
Lemma length_of_concat : forall l1 l2 : nlist, length (concat l1 l2) = length l1 + length l2.
Proof.
  intros l1 l2.
  induction l1.
  + simpl.
    reflexivity.
  + simpl.
    rewrite <- IHl1.
    reflexivity.
Qed.



(* Exprimer et montrer qu'ajouter un élément x en tête de la
concaténation de deux listes l1 et l2 est la même chose que concaténer
l1 avec x en tête et l2. *)
(* pas de difficulté, c'est juste un pas de calcul (simpl). *)

(*Lemma concat_cons : forall (x : nat) (l l1 l2 : nlist), x::(concat l1 l2) - concat (x::l1) l2.
Proof.
  simpl.
  reflexivity.
Qed.*)
  
(* Montrer maintenant que concaténer à l1 la liste vide renvoie exactement la liste l1. *)
(* Comme on a défini concat par récursion sur le premier paramètre, il va falloir une induction... *)
(*Lemma concat_nil_r : forall l1 : nlist, concat l1 l1 = l1.
Proof.
  induction l1.
  * simpl.
    reflexivity.
  * simpl.
  rewrite <- IHl1.
  reflexivity.
Qed.
*)

(* On reprend la fonction appartient du TP de LIFLF *)
Fixpoint appartient (x : nat) (l : nlist) : bool :=
  match l with
  | [] => false
  | h::rl => (Nat.eqb x h) || (appartient x rl)
  end.

(* Exprimer (cf. TD de LIFLC) et montrer que cette fonction retourne
true sur la donnée de paramètres x de type nat et l de type nlist
seulement si on peut écrire l comme une nlist l1 concaténée à une
nlist l2 commençant par x *)

(* on aura besoin du théorème 
   - Bool.orb_prop 
*)
Check Bool.orb_prop.

(* on aura besoin du théorème 
   - beq_nat_true (déjà vu)
*)
Check beq_nat_true.

(* En hypothèse l'existentiel est éliminé/spécialisé avec destruct de
l'hypothèse *)
(* Rappel : la règle d'introduction de l'existentiel dans le but est : exists objet_specialisé *)
  
Theorem appartient_seulement : forall x l, appartient x l = true -> exists l1 l2, l = l1 ++ (x::l2).
Proof.
intros x l H.
induction l.
- simpl in H.
  discriminate.
- simpl in H.
  apply Bool.orb_prop in H.
  destruct H.
  * apply beq_nat_true in H.
    exists [].
    exists l.
    simpl.
    rewrite <- H.
    reflexivity.
  * apply IHl in H.
    destruct H.
    destruct H.
    rewrite H.
    exists (n::x0).
    exists x1.
    simpl.
    reflexivity.
Qed.

(**********************************************************************)
(**********************************************************************)
(**********************************************************************)
(* À FAIRE CHEZ VOUS                                                  *)
(**********************************************************************)
(**********************************************************************)
(**********************************************************************)

Lemma plus_Succ_r : forall a b, S (plus a b) = plus a (S b). 
Proof.
Admitted.

(* Montrer que l'addition est commutative, on pourra avoir besoin du
lemme plus_Z_r démontré au début du TP. *)
Lemma plus_commute : forall x y, plus x y  = plus y x.
Proof.
Admitted.

(******************************************************************************)
(* Les arbres binaires de nat *)
(******************************************************************************)

(* On définit un type inductif pour les arbres binaires d'entiers *)
Inductive BinTree : Set :=
  | leaf : BinTree 
  | node : BinTree -> nat -> BinTree -> BinTree.

(*
Est-ce que les entiers sont :
  - sur les feuilles
  - sur les noeuds intermédiaires - bonne réponse
  - sur les feuilles ET noeuds intermédiaires
*)
(**********************************************************************)
(* Montrer (par induction bien sûr) qu'un arbre binaire comportant
   n occurrences de l’arbre vide contient n - 1 éléments              *)
(**********************************************************************)
(* On pourra avoir besoin du théorème plus_n_Sm *)
Check plus_n_Sm.

(* Les deux fonctions qui comptent *)
Fixpoint count_leaves (t:BinTree) : nat :=
match t with
  | leaf => 1
  | node l n r => count_leaves l + count_leaves r
end.

Fixpoint count_nodes (t:BinTree) : nat :=
match t with
  | leaf => 0
  | node l n r => 1 + count_nodes l + count_nodes r
end.

(* la propriété *)
Lemma count_leaves_nodes : forall (t:BinTree), 1 + (count_nodes t) = (count_leaves t).
Proof.
  intros t.
  induction t.
  * simpl.
    reflexivity.
  * simpl.
    rewrite <- IHt1.
    rewrite <- IHt2.
    simpl.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

