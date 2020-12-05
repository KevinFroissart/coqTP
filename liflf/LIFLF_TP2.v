(* TP2 Langages formels

   LISEZ BIEN TOUT CE QUI EST PRÉCISÉ EN COMMENTAIRES

   Décommentez les 'Example' pour vérifier que vos fonctions fonctionnent correctement

*)

(******************************************************************************)
(********** programmation fonctionnelle et automates en Coq (partie 1) ********)
(******************************************************************************)

(* L'objectif de LIFLF-TP2 est de définir tout ce dont on a besoin pour définir
   des automates et de les faire s'exécuter dans la partie *programme* de Coq.

   Les composants dont on aura besoin pour les automates :
    - On va définir le type "Alphabet" avec une fonction qui teste l'égalité
    - On va utiliser le type prédéfini "option" pour représenter les fonctions partielles
    - On va utiliser le type prédéfini "prod A B" des paires
    - On va définir la recherche dans une liste d'entiers et dans une liste de paires

   Le quintuplet usuel M = <K, Sigma, delta : K*Sigma -> K, s, F> sera défini en coq
   dans le TP3.
*)



(******************************************************************************)
(* L'alphabet et son égalité calculable *)
(******************************************************************************)

(* On définit un petit alphabet d'exemple : c'est juste une énumération, représentée
   en Coq par un type inductif avec 2 constructeurs sans argument (des constantes). *)
Inductive Alphabet : Type :=
| a : Alphabet
| b : Alphabet.

(* Ici, Alphabet est 'le plus petit ensemble qui contient a, b et rien d'autre', donc
   intuitivement, Alphabet est l'ensemble {a,b} *)

(* EXERCICE *)
(* Définir une fonction comp_alphabet qui teste si deux éléments de l'alphabet sont égaux
   et énoncer son théorème de correction *)

Definition comp_alphabet (a: Alphabet) (b: Alphabet) : bool :=
  match a, b with
  | a,a => true
  | b,b => true
  | _,_ => false
  end.


Theorem comp_alphabet_correct : (comp_alphabet a a) = true  (* Remplacer ici *).
Proof.
cbv.
reflexivity.
Qed.


(* On attend "false" comme résultat *)
Compute (comp_alphabet a b).

(* On peut aussi écrire les exemples précédents comme des tests unitaires

   EXEMPLES À DÉCOMMENTER

   Ici, la 'preuve' est obtenue par calcul :
     - "cbv" (call by value) effectue le calcul
     - la tactique "reflexivity" finit le job. *)
(*
Example comp_alphabet_ex1 : comp_alphabet a a = true.
Proof.
cbv.         (* on effectue le calcul *)
reflexivity. (* c'est bien l'axiome du prédicat d'égalité *)
Qed.

Example comp_alphabet_ex2 : comp_alphabet a b = false.
Proof.
cbv.
reflexivity.
Qed.
*)


(* Le travail de définition d'une fonction déterminant l'égalité qui a été fait
   sur Alphabet existe bien sûr pour les "nat". *)

(* Les entiers *)
Require Import Nat.
Print nat.

(* La fonction qui teste l'égalité de deux entiers. *)
Check Nat.eqb : nat -> nat -> bool.
Print Nat.eqb.


(******************************************************************************)
(* Le type prédéfini "option A" *)
(******************************************************************************)

(* Pour un type A, le type "option A" est
   - Soit un élément de A,
   - Soit rien.
*)

(* tout d'abord la définition (NE PAS DÉCOMMENTER, c'est un type prédéfini) :
   Inductive option (A : Type) : Type := 
     | Some : A -> option A
     | None : option A
*)

Print option.

(* EXERCICE *)
(* Définir une fonction comp_option_nat qui teste si deux "option nat" sont égaux.
   Par convention, comparer 'rien' et 'rien' renverra vrai.
   Comparer 'rien' et 'qqchose' renverra forcément faux.
   Pour le dernier cas, comparer deux 'qqchose' renverra la comparaison effective de ces deux qqchose.
   Vérifier les tests unitaires et énoncer le théorème de correction associé *)

Definition comp_option_nat (a b: option nat) : bool :=
  match a, b with
  | None, None => true
  | None,_ => false
  | Some n, Some m => Nat.eqb n m
  | Some n,_ => false
  end.

(* Tests unitaires avec reflexivity *)
(*
Example comp_option_nat_ex1 : comp_option_nat (Some 1) (Some 2) = false.
Proof.
cbv. reflexivity.
Qed.

Example comp_option_nat_ex2 : comp_option_nat (Some 2) (Some 2) = true.
Proof.
cbv. reflexivity.
Qed.

Example comp_option_nat_ex3 : comp_option_nat (None) (Some 2) = false.
Proof.
cbv. reflexivity.
Qed.

Example comp_option_nat_ex4 : comp_option_nat (Some 2) (None) = false.
Proof.
cbv. reflexivity.
Qed.
*)


(******************************************************************************)
(* Le type prédéfini produit de A et B "prod A B" *)
(******************************************************************************)

(* Le type 'produit de A et B' est définit par "prod A B" dans la bibliothèque Coq
   Inductive prod (A B : Type) : Type := 
     pair : A -> B -> A * B

   En Coq, on écrit "A * B" au lieu de  "prod A B" (c'est juste une notation)
*)
Print prod.

(* Ce type n'a qu'un seul constructeur "pair" qui prend deux arguments : (x:A) et (y:B)
   Prod A B est donc 'le plus petit ensemble qui contient tous les éléments
   de la forme "pair x y" (avec x dans A et y dans B) et rien d'autre'
   donc intuitivement, Prod A B est le produit cartésien de A et B, qui contient
   toutes les paires (x,y) (et rien d'autres).
*)

(* EXERCICE *)
(* Définir les fonctions "fsta" et "snda" de projection sur les couples d'éléments
   de type Alphabet avec "match" : p:A*B correspond au motif (x,y) où x est de type A et
   y de type B *)

Definition fsta (p: Alphabet * Alphabet) : Alphabet :=
  match p with
  | (x,y) => x
  end.

Definition snda (p: Alphabet * Alphabet) : Alphabet :=
  match p with
  | (x,y) => y
  end.

(*
Example fsta_ex1 : (fsta (a,b)) = a.
Proof.
  cbv. reflexivity.
Qed.

Example snda_ex1 : (snda (a,b)) = b.
Proof.
  cbv. reflexivity.
Qed.
*)

(* On peut ré-écrire comp_alphabet en utilisant le pattern matching
   sur la paire (x,y). Attention il y a un "let" caché dans cette
   façon de faire (donc on évitera).  On remarque aussi l'utilisation
   de "_" le joker pour les arguments génériques. *)
Definition comp_alphabet' (x y : Alphabet) : bool :=
  match (x,y) with
  | (a,a) => true
  | (b,b) => true
  | (_,_) => false (* pour tous les autres cas *)
end.

Print comp_alphabet'.

Example comp_alphabet'_ex1 : (comp_alphabet' a a) = true.
Proof.
  cbv. reflexivity.
Qed.

(* EXERCICE *)
(* Définir la fonction comp_pair_nat qui compare deux paires d'entiers.
   L'égalité sur les nat est "Nat.eqb" et le connecteur et sur les bool est "andb". *)

Definition comp_pair_nat (a b: nat * nat) : bool :=
  match a with
  | (xa,ya) => match b with
                | (xb,yb) => andb (Nat.eqb xa xb) (Nat.eqb ya yb)
                end
  end.


(* Tests unitaires avec reflexivity *)
(*
Example comp_pair_nat_ex1 : comp_pair_nat (0,1) (0,0) = false.
Proof.
cbv.
reflexivity.
Qed.
Example comp_pair_nat_ex2 : comp_pair_nat (0,1) (0,1) = true.
Proof.
reflexivity.
Qed.
*)

(* EXERCICE *)
(* Définir une fonction swap qui à la paire d'entiers (a,b) fait correspondre (b,a) *)

Definition swap (n: nat*nat) : nat*nat :=
  match n with
  | (x,y) => (y,x)
  end.


Example swap_ex1 : swap (1,2) = (2,1).
Proof.
  cbv. reflexivity.
Qed.



(******************************************************************************)
(* Recherche dans les listes d'entier  *)
(******************************************************************************)

(* On rappelle ici la définition des listes natives : on aurait pu
   tout faire avec les listes définies dans les TP précédents, comme
   avec nos entiers, mais c'est réinventer la roue

   Inductive list (A : Type) : Type := 
   | nil : list A
   | cons : A -> list A -> list A
*)
Require Export List.
Import ListNotations.

(* à partir d'ici on a
    - []   : la liste vide
    - n::l : le constructeur d'ajout de n en tête de l
    - ++   : la fonction de concaténation en position infixe *)
Print list.

(* EXERCICE *)
(* Définir la fonction "concatene" qui prend en paramètres deux listes d'entiers
   (donc de type "list nat") et renvoie la concaténation de ces deux listes *)

Fixpoint concatene (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => l2
  | n::l' => n::(concatene l' l2) 
  end.


Example concatene_ex1 : concatene [1;2;3] [4;5] = [1;2;3;4;5].
Proof.
cbv. reflexivity.
Qed.


(* EXERCICE *)
(* Définir la fonction "appartient" qui prend en paramètres un entier
   n et une liste d'entiers (donc de type "list nat") et renvoie true
   si et seulement si n est dans la liste *)

Fixpoint appartient (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | n'::l' => if Nat.eqb n n' then true else appartient n l'
  end.

(* Tests unitaires avec reflexivity *)

Example appartient_ex1 : appartient 0 [1;3;0;5] = true.
Proof.
cbv. reflexivity.
Qed.

Example appartient_ex2 : appartient 4 [1;3;0;5] = false.
Proof.
cbv. reflexivity.
Qed.



(******************************************************************************)
(* Recherche dans les listes de paires *)
(******************************************************************************)

(* on peut représenter un dictionnaire comme une liste de paire (clef, valeur) *)

(* La principale fonctionalité que l'on attend d'un dictionnaire est de pouvoir retrouver
   la valeur associée à une clef. Si plusieurs valeurs sont associées, alors on retourne
   la première qu'on trouve.

   On comprend bien que rien ne garantit qu'on trouve toujours une valeur, donc le type
   de retour de cette fonction est de type "option valeur"
*)

(* EXERCICE *)
(* Définir la fonction "trouve" qui prend en paramètres
    - une listes de paires (clef,valeur)
    - une clef k
   et renvoie la première valeur associée à k quand elle existe et None sinon.
   Les clés seront des Alphabet, les valeurs des nat.
*)

Fixpoint trouve (map : list (Alphabet * nat)) (n : Alphabet) : option nat :=
  match map with
  | [] => None
  | h::map' => if comp_alphabet n (fst h) then Some (snd h) else trouve map' n 
  end.


(* Tests unitaires avec reflexivity *)

Example trouve_ex1 :  trouve [(a,1); (b,2)] a = Some 1.
Proof.
cbv. reflexivity.
Qed.
Example trouve_ex2 :  trouve [(a,2); (a,1)] a = Some 2.
Proof.
cbv. reflexivity.
Qed.
Example trouve_ex3 :  trouve [(a,2); (a,1)] b = None.
Proof.
cbv. reflexivity.
Qed.



(* FIN DU TP2 *)

(* ------------------------------------------------------------ *)


(* EXERCICES A FAIRE CHEZ VOUS *)

(* EXERCICE *)
(* On va montrer que (comp_alphabet x y) = true si et seulement si (x = y).
   Autrement dit, comp_alphabet *décide* l'égalité entre deux éléments de alphabet.
   On va utiliser pour cela les tactiques vues dans les TP précédents
   - intros [Id1] [Id2] ...
   - destruct [Hypothèse]
   - discriminate
   - reflexivity
   - cbv (in [Hypothèse])
   - apply [Théorème] (in [Hypothèse])
   - rewrite [Théorème d'égalité] (in [Hypothèse])

   On peut décomposer la preuve :
   - prouver comp_alphabet_correct : si comp_alphabet x y = true alors x = y
   - prouver comp_alphabet_complet : si x = y alors comp_alphabet x y = true
*)

Theorem comp_alphabet_correct_a : forall x y : Alphabet, comp_alphabet x y = true -> x = y.
Proof.
destruct x.
destruct y.
- reflexivity.
- discriminate.
- destruct y.
  + discriminate.
  + reflexivity.
Qed.

Theorem comp_alphabet_complet_a :  forall x y : Alphabet, x = y -> comp_alphabet x y = true.
destruct x.
destruct y.
- reflexivity.
- discriminate.
- destruct y.
  + discriminate.
  + reflexivity.
Qed.


(* EXERCICE *)
(* Enoncer et prouver la propriété que comparer un symbole de l'alphabet avec lui-même renvoie vrai.
   HINT : "comp_alphabet_complet" fait exactement ce dont on a besoin, on peut donc l'utiliser *)

Goal comp_alphabet a a = true.
Proof.
reflexivity.
Qed.

(* EXERCICE *)
(* Compléter la preuve suivante
   HINT : "destruct x", "left" ou "right" pour "\/" *)
Lemma alphabet_a_juste_deux_elements : forall x:Alphabet, x = a \/ x = b.
Proof.
destruct x.
- left. reflexivity.
- right. reflexivity.
Qed.

(* EXERCICE *)
(* Enoncer et prouver la propriété que la fonction "comp_option_nat" est correcte et complète *)
(* HINT : si la tactique "cbv" ne calcule pas 'assez', remplacez le
   nom de fonction par sa valeur avec "unfold", comme par exemple avec le
   "unfold not" qui remplace "~A" par "A -> False". *)

Lemma comp_option_nat_correct : forall x y, comp_option_nat x y = true -> x = y.
Proof.
destruct x.
destruct y.
- intros. simpl in H. rewrite PeanoNat.Nat.eqb_eq in H. apply f_equal_nat. assumption.
- intros. simpl in H. discriminate.
- destruct y.
  + discriminate.
  + reflexivity.
Qed.

Theorem comp_option_nat_correct2 : forall x y, (comp_option_nat x y = true -> x = y) /\ (x = y -> comp_option_nat x y = true).
Proof.
destruct x.
destruct y.
- split.
  + simpl. intros. apply PeanoNat.Nat.eqb_eq in H. apply f_equal_nat. assumption.
  + simpl. intros. apply PeanoNat.Nat.eqb_eq. admit.
- split.
  + simpl. discriminate.
  + simpl. discriminate.
- destruct y.
  + split.
    * simpl. discriminate.
    * simpl. discriminate.
  + split.
    * simpl. reflexivity.
    * reflexivity.
Admitted.

(* EXERCICE *)
(* Prouver le lemme suivant *)
Lemma projection_product (A B : Type) : forall p:A*B, p = (fst p, snd p).
Proof.
destruct p.
simpl.
reflexivity.
Qed.


(* EXERCICE *)
(* Prouver que "swap" est involutive.
   Rappel. Une fonction f est une involution ssi quel que soit x, f(f(x)) = x
   HINT : pour p:A*B une paire, utiliser "destruct p" pour retrouver "(a,b)"
*)

Lemma swap_correct : forall x y, swap (x,y) = (y,x).
Proof. 
destruct x.
destruct y.
- reflexivity.
- reflexivity.
- destruct y.
  + reflexivity.
  + reflexivity.
Qed.

(* EXERCICE *)
(* Enoncer et prouver la propriété que la fonction "comp_pair_nat" est correcte
   HINT : utiliser "Bool.andb_true_iff"
   Bool.andb_true_iff : forall b1 b2 : bool, (b1 && b2)%bool = true <-> b1 = true /\ b2 = true
   Ce théorème lie le *ET* des booléens, la fonction "andb" en Coq (qui se note aussi "&&")
   et le *ET* logique, noté "/\" en Coq (qui se note aussi "and" )
*)
Check Bool.andb_true_iff.
Check PeanoNat.Nat.eqb_eq.

Lemma comp_pair_nat_correct : forall x y, comp_pair_nat x y = true -> x = y.
Proof.
destruct x.
destruct y.
simpl.
rewrite Bool.andb_true_iff.
rewrite PeanoNat.Nat.eqb_eq.
rewrite PeanoNat.Nat.eqb_eq.
intros. apply f_equal2_nat.
destruct H.
assumption.
destruct H.
assumption.
Qed.




(* EXERCICE *)
(* Ennoncer et prouver la propriété que l'appartenance d'un élément à une liste vide
   est fausse *)
   
Lemma appartient_liste_vide : forall n, appartient n [] = false.
Proof.
destruct n.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

(* EXERCICE *)
(* Ennoncer et prouver la propriété que l'appartenance d'un élément à une liste singleton
   est vraie SSI l'élément recherché et celui du singleton sont égaux
   On utilisera les théorèmes suivants
   "Bool.orb_false_r : forall b : bool, (b || false)%bool = b"
   "PeanoNat.Nat.eqb_eq : forall n m : nat, PeanoNat.Nat.eqb n m = true <-> n = m"
*)

Lemma appartient_liste_singleton : forall x y, appartient x [y] = true -> x = y.
Proof.
destruct x.
destruct y.
- simpl. reflexivity.
- simpl. discriminate.
- destruct y.
  + simpl. discriminate.
  + intros.
Admitted. 

(* EXERCICE *)
(* Énoncer et prouver le lemme de correction de "appartient"
   nommé "appartient_correct" qui dit en langue naturelle :
   (appartient x ls) est vrai SI ET SEULEMENT SI il existe une décomposition 
   de ls de la forme ls = l1 ++ x :: l2.

   NOTA BENE : c'est assez ambitieux à prouver à ce stade.
*)

Lemma appartient_correct : forall x ls l1 l2, (appartient x ls) = true <-> ls = l1 ++ x :: l2.
Proof.
destruct x.
destruct ls.
destruct l1.
destruct l2.
- simpl. split.
  + discriminate.
  + discriminate.
- simpl. split.
  + discriminate.
  + discriminate.
- destruct l2.
  + simpl. split.
    * discriminate.
    * discriminate.
  + simpl. split.
    * discriminate.
    * discriminate.
- destruct l1. destruct l2.
  + split.
    * intros. simpl. admit.
    * intros. admit.
  + split.
    * intros. simpl. admit. 
    * intros. simpl in H. admit.
  + destruct l2.
    * split. intros. simpl. admit. intros. simpl in H. admit.
    * split. intros. simpl. admit. intros. simpl in H. rewrite H . simpl. admit.
- destruct ls.
  + destruct l1. destruct l2.
    * split. simpl. discriminate. simpl. discriminate.
    * simpl. split. discriminate. discriminate.
    * destruct l2. simpl. split. discriminate. discriminate. simpl. split. discriminate. discriminate.
  + destruct l1. destruct l2.
    * split. intros. admit.  intros. admit.
    * split. intros. admit.  intros. admit.
    * destruct l2. split. intros. admit. intros. admit. split. intros. admit. intros. admit.
Admitted.


(* EXERCICE *)
(* Enoncer et prouver la propriété "trouve_tete" qui, pour toute liste l,
   toute clé k et toute valeur v, trouve ((k,v)::l) k = Some v.

   HINT : vous pouvez ajouter une nouvelle assertion dans le contexte avec 
   la tactique "assert H", un nouveau sous-but demandant de prouver "H"
   est alors ajouté
*)

Lemma trouve_tete : forall l k v, trouve ((k,v)::l) k = Some v.
Proof.
induction l.
induction k.
induction v.
- simpl. reflexivity.
- simpl. reflexivity.
- induction v.
  + simpl. reflexivity.
  + simpl. reflexivity.
- induction k.
  + induction v.
    * simpl. reflexivity.
    * simpl. reflexivity.
  + induction v.
    * simpl. reflexivity.
    * simpl. reflexivity.
Qed.

(* ------------------------------------------------------------ *)

