Require Import Wf_nat Recdef.
Require Import ssreflect.

Check lt_wf.

Check lt_wf_ind.

Function gcd (m n : nat) {wf lt m} : nat :=
if m is 0 then n else gcd (modn n m) m.   (* modn not found *)
Proof.
  - move=> m n m0 _. apply/ltP.
      by rewrite ltn_mod.
  - exact: lt_wf.
Qed.

Check gcd_equation.
Check gcd_ind.
Print gcd_terminate.

Require Import Extraction.
Extraction gcd. (* wf が消える *)
(*
let rec gcd m n =
    match m with
    | O -> n
    | S n0 -> gcd (modn n (S n0)) (S n0)  *)

(* では，これから正しさを証明する．*)
Search (_ %| _) "dvdn". (* 割り切ることに関する補題を表示 *)
Check divn_eq.
(*: ∀ m d : nat, m = m %/ d * d + m %% d *)

Theorem gcd_divides m n : (gcd m n %| m) && (gcd m n %| n).
Proof.
  functional induction (gcd m n).
    by rewrite dvdn0 dvdnn.
Admitted.

Check addKn.
(* : ∀ x y : nat, x + y - x = y *)
Theorem gcd_max g m n : g %| m -> g %| n -> g %| gcd m n.
Admitted.

(*
odd_mul : ∀ m n : nat, odd (m * n) = odd m && odd n
odd_double : ∀ n : nat, odd n.*2 = false
odd_double_half : ∀ n : nat, odd n + (n./2).*2 = n
andbb : ∀ x : bool, x && x = x
negbTE : ∀ b : bool, ~~ b -> b = false
double_inj : ∀ x x2 : nat, x.*2 = x2.*2 -> x = x2
divn2 : ∀ m : nat, m %/ 2 = m./2
ltn_Pdiv : ∀ m d : nat, 1 < d -> 0 < m -> m %/ d < m
muln2 : ∀ m : nat, m * 2 = m.*2
esym : ∀ (A : Type) (x y : A), x = y -> y = x
 *)

Lemma odd_square n : odd n = odd (n*n). Admitted.
Lemma even_double_half n : ~~odd n -> n./2.*2 = n. Admitted.

(* 本定理 *)
Theorem main_thm (n p : nat) : n * n = (p * p).*2 -> p = 0.
Proof.
  elim/lt_wf_ind: n p => n. (* 清楚帰納法 *)
  case: (posnP n) => [-> _ [] // | Hn IH p Hnp].
Admitted.

(* 無理数 *)
Require Import Reals Field. (* 実数とそのための field タクティク *)
Definition irrational (x : R) : Prop :=
  forall (p q : nat), q <> 0 -> x <> (INR p / INR q)%R.

Theorem irrational_sqrt_2: irrational (sqrt (INR 2)).
Proof.
  move=> p q Hq Hrt.
  apply /Hq /(main_thm p) /INR_eq.
  rewrite -mul2n !mult_INR -(sqrt_def (INR 2)) ?{}Hrt; last by auto with real.
  have Hqr : INR q <> 0%R by auto with real.
  by field.
Qed.

(* 練習問題 2.1 Admitted を Qed に変え, 証明を完成せよ.*)
