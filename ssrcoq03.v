From mathcomp Require Import ssreflect.

Definition one : nat := 1. (* 定義 *)
(* one is defined *)

(* Definition one := 1.
   Error: one already exists. (* 再定義はできない *) *)

Definition one' := 1. (* 型を書かなくてもいい *)
Print one'. (* 定義の確認 *)
(* one' = 1 
        : nat *) (* nat は自然数の型 *) 

Definition double x := x + x. (* 関数の定義 *)
Print double.
(* double = fun x : nat => x + x (* 関数も値 *)
        : nat -> nat *) (* 関数の型 *)

Eval compute in double 2. (* 式を計算する *)
(* = 4
   : nat *)
Definition double' := fun x => x + x. (* 関数式で定義 *)
Print double'.
(* double' = fun x : nat => x + x
        : nat -> nat *)

Definition quad x := let y := double x in 2 * y. (* 局所的な定義 *)
Eval compute in quad 2.
(* = 8
   : nat *)

Definition quad' x := double (double x). (* 関数適用の入れ子 *)
Eval compute in quad' 2.
(* = 8
   : nat *)

Definition triple x :=
  let double x := x + x in (* 局所的な関数定義。上書きもできる *)
  double x + x.
Eval compute in triple 3.
(* = 9
   : nat *)

(* データ型の定義 *)
Inductive janken : Set := (* じゃんけんの手 *)
  | gu
  | choki
  | pa.

Definition weakness t := (* 弱点を返す *)
  match t with (* 簡単な場合分け *)
  | gu => pa
  | choki => gu
  | pa => choki
  end.
Eval compute in weakness pa.
(* = choki
   : janken *)

Print bool.
(* Inductive bool : Set := true : bool | false : bool *)

Print janken.
(*Inductive janken : Set := gu : janken | choki : janken | pa : janken *)

Definition wins t1 t2 := (* 「t1 は t2 に勝つ」という関係 *)
  match t1, t2 with (* 二つの値で場合分け *)
  | gu, choki => true
  | choki, pa => true
  | pa, gu => true
  | _, _ => false (* 残りは全部勝たない *)
  end.

Check wins.
(* wins : janken -> janken -> bool *) (* 関係は bool への多引数関数 *)
Eval compute in wins gu pa.
(*= false
  : bool  *)

(* 場合分けによる証明 *)
Lemma weakness_wins t1 t2 :
wins t1 t2 = true <-> weakness t2 = t1.
Proof.
  split.
  - by case: t1; case: t2. (* 全ての場合を考える *)
  - move=> <-; by case: t2. (* t2 の場合分けで十分 *)
    Restart.
    case: t1; case: t2; by split. (* 最初から全ての場合でも OK *)
Qed.

(*
(* 再帰データ型と再帰関数*)
Module MyNat. (* nat を新しく定義する *)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Module MyNat. (* nat を新しく定義する *)
Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(*
Fixpoint plus (m n : nat) {struct m} : nat := (* 帰納法の対象を明示する *)
  match m with (* 減らないとエラーになる *)
  | O => n
  | S m’ => S (plus m n)
end.
Error: Recursive definition of plus is ill-formed.
In environment ...
Recursive call to plus has principal argument equal to m instead of m’.
 *)

Fixpoint plus (m n : nat) {struct m} : nat := (* 同じ型の引数をまとめる *)
  match m with
  | O => n
  | S m' => S (plus m' n) (* 正しい定義 *)
  end.

Print plus.

Check plus (S (S O)) (S O).

Eval compute in plus (S (S O)) (S O). (* 式を評価する *)
(* = S (S (S O))
   : nat *)

Fixpoint mult (m n : nat) {struct m} : nat := O.
Eval compute in mult (S (S O)) (S O).
(* = S (S O) (* 期待している値 *)
   : nat   *)

End MyNat.

(* 練習問題 1.1 mult を正しく定義せよ．*)
*)

From mathcomp Require Import ssreflect.

Check nat_ind.
Lemma plusnS m n : m + S n = S (m + n). (* m, n は仮定 *)
Proof.
  elim: m => /=. (* nat_ind を使う *)
  - done. (* O の場合 *)
  - move => m IH. (* S の場合 *)
      by rewrite IH. (* 帰納法の仮定で書き換える *)
      Restart.
      elim: m => /= [|m ->] //. (* 一行にまとめた *)
Qed.

Check plusnS. (* ∀ m n : nat, m + S n = S (m + n) *)

Lemma plusSn m n : S m + n = S (m + n).
Proof. rewrite /=. done. Show Proof. Qed. (* 簡約できるので帰納法は不要 *)

Lemma plusn0 n : n + 0 = n.
Admitted. (* 定理を認めて証明を終わらせる *)

Lemma plusC m n : m + n = n + m.
Admitted.

Lemma plusA m n p : m + (n + p) = (m + n) + p.
Admitted.

Lemma multnS m n : m * S n = m + m * n.
Proof.
  elim: m => /= [|m ->] //.
    by rewrite !plusA [n + m]plusC.
Qed.

Lemma multn0 n : n * 0 = 0.
Admitted.

Lemma multC m n : m * n = n * m.
Admitted.

Lemma multnDr m n p : (m + n) * p = m * p + n * p.
Admitted.

Lemma multA m n p : m * (n * p) = (m * n) * p.
Admitted.

Fixpoint sum n :=
if n is S m then n + sum m else 0.
Print sum. (* if .. is は match .. with に展開される *)

Lemma double_sum n : 2 * sum n = n * (n + 1).
Admitted.

Lemma square_eq a b : (a + b) * (a + b) = a * a + 2 * a * b + b * b.
Admitted. (* 帰納法なしで証明できる *)

(* 練習問題 2.1 上の Admitted を全て証明せよ．*)
