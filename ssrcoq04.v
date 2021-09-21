Require Import ssreflect.

Definition prod_ind (A B:Set) (P:prod A B -> Prop) :=
  fun (f : forall a b, P (pair a b)) =>
    fun p => match p as x return P x with pair a b => f a b end.
Check prod_ind.

Definition sum_ind (A B:Set) (P:sum A B -> Prop) :=
  fun (fl : forall a, P (inl _ a)) (fr : forall b, P (inr _ b)) =>
    fun p => match p as x return P x
             with inl a => fl a | inr b => fr b end.
Check sum_ind.

Fixpoint nat_ind (P:nat -> Prop) (f0:P O) (fn:forall n, P n -> P (S n))
         (n : nat) {struct n} :=
  match n as x return P x
  with O => f0 | S m => fn m (nat_ind P f0 fn m) end.
Check nat_ind.

Lemma plusn0 n : n + 0 = n.
Proof.
  (*
  case: n.
  - done.
  (* forall n : nat, S n + 0 = S n. *)
    Restart.
   *)
    move: n.
    apply: nat_ind. (* elim の意味 *)
  - done.
  (* forall n : nat, n + 0 = n -> S n + 0 = S n *)
  - move=> n /= -> //.
Qed.

(* 偶数の定義 *)
Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).
(* 帰納的述語を証明する定理 *)
Theorem even_double n : even (n + n).
Proof.
  elim: n => /= [|n IH].
  - apply: even_O.
  - rewrite -plus_n_Sm.
      by apply: even_SS.
Qed.

(* 帰納的述語に対する帰納法もできる *)
Theorem even_plus m n : even m -> even n -> even (m + n).
Proof.
  elim: m => //=.
  Restart.
  move=> Hm Hn.
  elim: Hm => //= m' n' IH.
  by apply: even_SS.
Qed.

(* 矛盾を導き出す *)
Theorem one_not_even : ~ even 1.
Proof.
  case.
  Restart.
  move H: 1 => one He. (* move H: exp => pat は H: exp = pat を作る *)
  case: He H => //.
  Restart.
  move=> He.
  inversion He.
  Show Proof. (* 証明が複雑で、SSReflect では様々な理由で避ける *)
Qed.

(* 等式を導き出す *)
Theorem eq_pred m n : S m = S n -> m = n.
Proof.
  case. (* 等式を分解する *)
  done.
Qed.

(*実は Coq の論理結合子のほとんどが帰納的述語として定義されている．*)
(*
Inductive and (A B : Prop) : Prop := conj : A -> B -> A /\ B.
Inductive or (A B : Prop) : Prop :=
  or_introl : A -> A \/ B | or_intror : B -> A \/ B.
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
  ex_intro : forall x : A, P x -> exists x, P x.
Inductive False : Prop := .
 *)

Print False_ind.
 (*fun (P : Prop) (f : False) => match f return P with end
   : forall P : Prop, False -> P *)

(* ちょうど，矛盾の規則に対応している．作戦　 elim でそれが使える．*)
Theorem contradict (P Q : Prop) : P -> ~P -> Q.
Proof. move=> p. elim. exact: p. Qed.

(* 練習問題 3.1 以下の定理を証明しなさい．*)
Module Odd.
  Inductive odd : nat -> Prop :=
  | odd_1 : odd 1
  | odd_SS : forall n, odd n -> odd (S (S n)).
  Theorem even_odd n : even n -> odd (S n). Abort.
  Theorem odd_even n : odd n -> even (S n). Abort.
  Theorem even_not_odd n : even n -> ~odd n. Abort.
End Odd.


Section SystemF.
  Definition Fand P Q := forall X : Prop, (P -> Q -> X) -> X.
  Definition For P Q := forall X : Prop, (P -> X) -> (Q -> X) -> X.
  Definition Ffalse := forall X : Prop, X.
  Definition Ftrue := forall X : Prop, (X -> X).
  Definition Feq T (x y : T) := forall P, Fand (P x -> P y) (P y -> P x).
  Definition Fex T (P : T -> Prop) := forall X : Prop, (forall x, P x -> X) -> X.

  Theorem Fand_ok (P Q : Prop) : Fand P Q <-> P /\ Q.
  Proof.
    split => [pq | [p q] X].
    - split; by apply: pq.
    - by apply.
  Qed.
  Theorem For_ok (P Q : Prop) : For P Q <-> P \/ Q. Abort.
  Theorem Ffalse_ok : Ffalse <-> False. Abort.
  Theorem Ftrue_ok : Ftrue <-> True. Abort.
  Theorem Feq_ok T (x y : T) : Feq x y <-> x = y. Abort.
  Theorem Fex_ok T (P : T -> Prop) : Fex P <-> exists x, P x. Abort.

  Definition Nat := forall X : Prop, (X -> X) -> X -> X.
  Definition Zero : Nat := fun X f x => x.
  Definition Succ (N : Nat) : Nat := fun X f x => f (N X f x).
  Definition Plus (M N : Nat) : Nat := fun X f x => M X f (N X f x).
  Definition Mult (M N : Nat) : Nat := fun X f x => M X (N X f) x.
  (* こちらの定義はより直感的 *)
  Definition Plus' (M N : Nat) : Nat := M Nat Succ N. (* 1 を M 回足す *)
  Definition Mult' (M N : Nat) : Nat := M Nat (Plus' N) Zero. (* N を M 回足す *)
  Fixpoint Nat_of_nat n : Nat := (* 自然数を Nat に変換 *)
    match n with 0 => Zero | S m => Succ (Nat_of_nat m) end.
  (* Nat の元の等価性は適用された物を比較するべき *)
  Definition eq_Nat (M N : Nat) := forall X f x, M X f x = N X f x.
  Definition eq_Nat_fun F f := forall n,
      eq_Nat (F (Nat_of_nat n)) (Nat_of_nat (f n)).
  Definition eq_Nat_op Op op := forall m n,
      eq_Nat (Op (Nat_of_nat m) (Nat_of_nat n)) (Nat_of_nat (op m n)).
  Theorem Succ_ok : eq_Nat_fun Succ S. Proof. by elim. Qed. (* 実は自明 *)
  Theorem Plus_ok : eq_Nat_op Plus plus.
  Proof.
    move=> m n X f x.
    elim: m x => //= m IH x.
      by rewrite Succ_ok /= [in RHS]/Succ -IH.
  Qed.
  
  Theorem Mult_ok : eq_Nat_op Mult mult. Abort.
  Definition Pow (M N : Nat) := fun X => N _ (M X). (* M の N 乗 *)
  Fixpoint pow m n := match n with 0 => 1 | S n => m * pow m n end.
  Lemma Nat_of_nat_eq : forall n X f1 f2 x,
      (forall y, f1 y = f2 y) ->
      Nat_of_nat n X f1 x = Nat_of_nat n X f2 x.
  Abort.
  Theorem Pow_ok : eq_Nat_op Pow pow. Abort.
  
  Section ProdSum. (* 値の対と直和も定義できます *)
    Variables X Y : Prop.
    Definition Prod := forall Z : Prop, (X -> Y -> Z) -> Z.
    Definition Pair (x : X) (y : Y) : Prod := fun Z f => f x y.
    Definition Fst (p : Prod) := p _ (fun x y => x).
    Definition Snd (p : Prod) := p _ (fun x y => y).
    Definition Sum := forall Z : Prop, (X -> Z) -> (Y -> Z) -> Z.
    Definition InL x : Sum := fun Z f g => f x.
    Definition InR x : Sum := fun Z f g => g x.
  End ProdSum.

  Arguments Pair [X Y]. Arguments Fst [X Y]. Arguments Snd [X Y].
  Arguments InL [X] Y. Arguments InR X [Y]. (* 型引数を省略できるようにする *)
  Definition Pred (N : Nat) := (* 前者関数の定義は工夫が必要 *)
    Fst (N _ (fun p : Prod Nat Nat => Pair (Snd p) (Succ (Snd p)))
           (Pair Zero Zero)).
  Theorem Pred_ok : eq_Nat_fun Pred pred. Abort.
  (* Nat が Set で定義されているときだけ証明可能 *)
  Lemma Nat_of_nat_ok : forall n, Nat_of_nat n _ S O = n. Abort.

  (*練習問題 4.1 System F での符号化に関する定理を好きなだけ証明せよ． *)
  
End SystemF.

