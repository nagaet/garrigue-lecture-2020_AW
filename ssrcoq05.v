From mathcomp Require Import all_ssreflect.

Module Test_ssrnat.
  Fixpoint sum n :=
    if n is m.+1 then n + sum m else 0.
  
  Theorem double_sum n : 2 * sum n = n * n.+1.
  Proof.
    elim: n => [|n IHn] //=.
    rewrite -[n.+2]addn2 !mulnDr.
    rewrite addnC !(mulnC n.+1).
    by rewrite IHn.
  Qed.
End Test_ssrnat.

Print reflect.

Module Test_ssrbool.
  Variables a b c : bool.
  Print andb.
  
  Lemma andb_intro : a -> b -> a && b.
  Proof.
    move=> a b.
    rewrite a.
    move=> /=.
    done.
    Restart.
    by move ->.
  Qed.

  Lemma andbC : a && b -> b && a.
  Proof.
    case: a => /=.
      by rewrite andbT.
      done.
      Restart.
      by case: a => //= ->.
      Restart.
      by case: a; case: b.
  Qed.
  
  Lemma orbC : a || b -> b || a.
  Proof.
    case: a => /=.
      by rewrite orbT.
      by rewrite orbF.
      Restart.
      move/orP => H.
      apply/orP.
      move: H => [Ha|Hb].
      by right.
      by left.
      Restart.
        by case: a; case: b.
  Qed.

  Lemma test_if x : if x == 3 then x*x == 9 else x !=3.
  Proof.
    case Hx: (x == 3).
    by rewrite (eqP Hx).
    done.
    Restart.
    case: ifP.
    by move/eqP ->.
    move/negbT. done.
  Qed.
End Test_ssrbool.

(* 自己反映があると自然数の証明もスムーズになる．*)
Theorem avg_prod2 m n p : m+n = p+p -> (p - n) * (p - m) = 0.
Proof.
  move=> Hmn.
  have Hp0 q: p <= q -> p-q = 0.
  rewrite -subn_eq0. by move/eqP.
  suff /orP[Hpm|Hpn]: (p <= m) || (p <= n).
  - by rewrite (Hp0 m) // muln0.
  - by rewrite (Hp0 n).
    case: (leqP p m) => Hpm //=.
    case: (leqP p n) => Hpn //=.
    suff: m + n < p + p.
    by rewrite Hmn ltnn.
    by rewrite -addnS leq_add // ltnW.
Qed.

(* 練習問題 1.1 以下の等式を証明しなさい．タクティクは rewrite のみでできる．
  ssrnat_doc.v の補題でほぼ足りるが, leq_mul も便利．*)
Module Equalities.
  Theorem square_sum a b : (a + b)^2 = a^2 + 2 * a * b + b^2.
  Abort.

  Theorem diff_square m n : m >= n -> m^2 - n^2 = (m+n) * (m-n).
  Abort.

  Theorem square_diff m n : m >= n -> (m-n)^2 = m^2 + n^2 - 2 * m * n.
  Abort.
End Equalities.


Lemma test x : 1 + x = x + 1.
  Check [eta addnC].
  (*: ∀ x y : nat, x + y = y + x *)
  apply: addnC.
Abort.      (* 定理を登録せずに証明を終わらせる *)

(* Coq 本来の apply で変数が定まらないと，エラーになる．しかし，SSReflect の apply: や
apply/ を使えば，変数が残せる．*)
Lemma test x y z : x + y + z = z + y + x.
  Check etrans.
  (* : ∀ (A : Type) (x y z : A), x = y -> y = z -> x = z *)
  (* apply etrans.
     Error: Unable to find an instance for the variable y. *)
  apply: etrans. (* y が結論に現れないので，apply: に変える *)
  (* x + y + z = ?Goal *)
  apply: addnC.
  apply: etrans.
  Check f_equal.
  (* : ∀ (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y *)
  apply: f_equal. (* x + y = ?Goal0 *)
  apply: addnC.
  apply: addnA.
  Restart. (* 証明を元に戻す *)
  rewrite addnC. (* rewrite も単一化を使う *)
  rewrite (addnC x).
  apply: addnA.
Abort.

Goal
  (forall P : nat -> Prop, P 0 -> (forall n, P n -> P (S n)) -> forall n, P n) ->
forall n m, n + m = m + n.
  move=> H n m. (* 全ての変数を仮定に *)
  apply: H. (* n + m = 0 *)
  Restart.
  move=> H n m.
  pattern n. (* pattern で正しい述語を構成する *)
  apply: H. (* 0 + m = m + 0 *)
  Restart.
  move=> H n. (* forall n を残すとうまくいく *)
  apply: H. (* n + 0 = 0 + n *)
Abort.
