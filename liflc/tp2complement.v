
(* Étude de cas.

On se propose de regarder le cas de l'automate qui reconnaît les mots finissant par "aab".
On commence par définir cet automate en utilisant le TP de LIFLF.
 *)

(* inclure ici le TP de LF *)


(* Automate qui reconnaît les mots qui finissent par "aab" *)
Definition gaab := [ ]. (* remplacer ici *)

Definition Aaab := false. (* remplacer ici *)


(* Écrire en commentaire la grammaire régulière produisant le langage de l'automate *)
(* Source : X1
 *)

(* On peut définir le prédicat "être généré par cette grammaire" *)

(* En effet : une règle "N -> c M" signifie qu'un mot généré depuis N
   peut être constitué d'un c suivi par un mot généré depuis M donc
   pour tout mot w, le mot cw est généré par N si w est généré par M.
   Dit autrement : "pour tout mot w, si w est généré depuis M alors cw
   est généré depuis N".  C'est exactement ce qu'on se propose
   d'écrire. *)

(* On va donc définir un prédicat *inductif*, paramétré par un mot et
un état (vu comme un non terminal de la grammaire ), dont chaque
règle de construction caractérise chaque règle de grammaire *)

(* Définir ce prédicat inductif Paab, de type liste Alphabet -> nat -> Prop *)
Inductive Paab : list Alphabet -> nat -> Prop := False (* remplacer ici *)
.


(* Pour montrer qu'un mot est bien généré depuis un état, il suffit
d'appliquer (apply) les règles de construction jusqu'à tomber sur un
cas de base. *)
(* Montrer que le mot abaaab est bien généré depuis le non terminal 1 *)

Lemma exemple :  Paab [a;b;a;a;a;b] 1.
Proof.
Admitted. (* remplacer ici *)

(* CE PRÉDICAT (DÉRIVÉ DE LA GRAMMAIRE) CARACTÉRISE-T-IL BIEN LES MOTS
RECONNUS PAR L'AUTOMATE ? *)

(* Pour le montrer on va poser un lemme intermédiaire *)

(* Ce lemme, appelons-le PmimeA, énonce que pour tout mot généré à
partir d'un état/non terminal, disons q, de la grammaire, la lecture
de ce mot depuis q dans l'automate aboutit à un état, disons e, et cet
état e est acceptant. *)

(* Définir le lemme PmimeA *)
Lemma PmimeA : False. (* remplacer ici *)
Proof.
Admitted. (* remplacer ici *)

(* Pour le montrer une nouvelle tactique va être bien utile :
inversion.
  - La tactique "inversion" appliquée à un nom d'inductif énumère les
  cas *possibles* de règles qui ont pu le produire.
  - Les cas absurdes sont éliminés, en particulier si une hypothèse n'a
  pu apparaître qu'à l'aide de cas absurdes, le but est prouvé.
  - On va se servir de cette tactique pour se placer dans les différents
  cas du prédicat. *)



(* Énoncer et montrer le théorème principal : tout mot généré depuis le non terminal 1 est reconnu par l'automate. *)
Theorem PA : False. (* remplacer ici *)
Proof.
Admitted. (* remplacer ici *)

(*


Bonjour madame,

J'ai eu une absence injustifiée par rapport au cours de Vendredi.
Je ne sais pas comment être présent vu que je n'ai reçu aucun mail concernant l'anglais depuis le confinement.
Pourriez-vous me l'expliquer svp ?

Merci,
Lucas.
*)
