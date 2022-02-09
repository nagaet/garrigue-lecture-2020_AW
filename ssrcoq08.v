From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.

Section sort.
Variable A : eqType.
Variable le : A -> A -> bool.
Variable le_trans: forall x y z, le x y -> le y z -> le x z.
Variable le_total: forall x y, ~~ le x y -> le y x.

Fixpoint insert a (l: seq A) :=
  match l with
  | nil     => (a :: nil)
  | b :: l' => if le a b then a :: l else b :: insert a l'
  end.

Fixpoint isort (l : seq A) : seq A :=
  match l with
  | nil     => nil
  | a :: l' => insert a (isort l')
  end.

Fixpoint sorted l :=
  match l with
  | nil     => true
  | a :: l' => all (le a) l' && sorted l'
  end.

Lemma le_seq_insert a b l :
  le a b -> all (le a) l -> all (le a) (insert b l).
Proof.
  elim: l => /= [-> // | c l IH].
  move=> leab /andP [leac leal].
  case: ifPn => lebc /=.
  - by rewrite leab leac.
  - by rewrite leac IH.
Qed.

Lemma le_seq_trans a b l :
  le a b -> all (le b) l -> all (le a) l.
Proof.
  move=> leab /allP lebl.
  apply/allP => x Hx.
  by apply/le_trans/lebl.
Qed.

Theorem insert_ok a l : sorted l -> sorted (insert a l).
Proof.

Admitted.

Theorem isort_ok l : sorted (isort l).
Proof.

Admitted.

Theorem insert_perm l a : perm_eq (a :: l) (insert a l).
Proof.
  elim: l => //= b l pal.
  case: ifPn => //= leab.
  by rewrite (perm_catCA [:: a] [:: b]) perm_cons.
Qed.

Theorem isort_perm l : perm_eq l (isort l).
Proof.
 
Admitted.
End sort.

Check isort.
Definition isortn := isort _ leq.
Definition sortedn := sorted _ leq.
Lemma leq_total a b : ~~ (a <= b) -> b <= a.
Proof.

Admitted.

Lemma isortn_ok l : sortedn (isortn l) && perm_eq l (isortn l).
Proof.

Admitted.

(* 寄寓、mathcomp式 *)
Section even_odd.
Notation even n := (~~ odd n).

Theorem even_double n : even (n + n).
Proof.
  elim: n => // n.
  by rewrite addSn addnS /= negbK.
Qed.

Theorem even_plus m n : even m -> even n = even (m + n).
Proof.
  elim: n => /= [|n IH] Hm.
  - by rewrite addn0.
  - by rewrite addnS IH.
Qed.

Theorem one_not_even : ~~ even 1.
Proof. reflexivity. Qed.

Theorem even_odd n : even n = odd n.+1.
Proof. done. Qed.

Theorem odd_even n : odd n = even n.+1.
Proof. by rewrite /= negbK. Qed.

Theorem even_not_odd n : even n = ~~ odd n.
Proof. done. Qed.

Theorem even_or_odd n : even n || odd n.
Proof. by case: (odd n). Qed.


Theorem odd_odd_even m n : odd m -> odd n = even (m+n).
Proof.

Admitted.
End even_odd.
