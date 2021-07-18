Require Import ssreflect.

Section Socrates.

  Variable A : Set.
  Variables human mortal : A -> Prop.
  Variable socrates : A.

  Hypothesis hm : forall x, human x -> mortal x.
  Hypothesis hs : human socrates.

  Theorem ms : mortal socrates.
  Proof.
    apply: (hm socrates).
    assumption.
  Qed.

  Print ms. (* 定義を表示する *)

End Socrates.


Section Eq.

  Variable T : Type.

  Lemma symmetry : forall x y : T, x = y -> y = x.
  Proof.
    move=> x y exy.
    rewrite exy. (* x を y に書き換える *)
    done. (* 反射率で終わらせる *)
    Restart. by move=> x y ->. (* => の後ろなら -> で書き換えられる *)
  Qed.

  Lemma transitivity : forall x y z : T, x = y -> y = z -> x = z.
  Abort.

End Eq.


Section Group.

  Variable G : Set.
  Variable e : G.
  Variable op : G -> G -> G.
  Notation "a * b" := (op a b). (* op を * と書けるようにする *)
  Variable inv : G -> G.

  Hypothesis associativity : forall a b c, (a * b) * c = a * (b * c).
  Hypothesis left_identity : forall a, e * a = a.
  Hypothesis right_identity : forall a, a * e = a.
  Hypothesis left_inverse : forall a, inv a * a = e.
  Hypothesis right_inverse : forall a, a * inv a = e.

  Lemma unit_unique : forall e', (forall a, a * e' = a) -> e' = e.
  Proof.
    move=> e' He'.
    rewrite -[RHS]He'. (* 右辺を書き換える *)
    rewrite (left_identity e'). (* 公理をの引数を指定する *)
    done.
  Qed.

  Lemma inv_unique : forall a b, a * b = e -> a = inv b.
  Proof.
    move=> a b.
    Check f_equal. (* (f_equal f) が等式の両辺に f を適用する *)
    move/(f_equal (fun x => x * inv b)).
    rewrite associativity right_inverse left_identity right_identity.
    done. (* 書き換えはまとめて書ける *)
  Qed.

  Lemma inv_involutive : forall a, inv (inv a) = a.
  Abort.

End Group.

Check unit_unique.


(* 練習問題 3.1 transitivity と inv involutive を証明に変えよ．*)


Section Laws.
  
  Variables (A:Set) (P Q : A->Prop).

  Lemma DeMorgan2 : (~ exists x, P x) -> forall x, ~ P x.
  Proof.
    move=> N x Px. elim: N. by exists x.
  Qed.

  Theorem exists_or :
    (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x).
  Proof.
    move=> [x [Px | Qx]]; [left|right]; by exists x.
  Qed.

  Hypothesis EM : forall P, P \/ ~P.   (* <- ?? *)

  Lemma DeMorgan2' : ~ (forall x, P x) -> exists x, ~ P x.
  Proof.
    move=> nap.
    case: (EM (exists x, ~ P x)) => //. (* 背理法 *)
    move=> nnpx.
    elim: nap => x. (* (forall x, P x) を証明する *)
    case: (EM (P x)) => //. (* 背理法 *)
    move=> npx.
    elim: nnpx. by exists x.
  Qed.

End Laws.

(* 練習問題 4.1 以下の定理を Coq で証明せよ．*)
Section Coq3.
  
  Variable A : Set.
  Variable R : A -> A -> Prop.
  Variables P Q : A -> Prop.
  
  Theorem exists_postpone :
    (exists x, forall y, R x y) -> (forall y, exists x, R x y).
  Proof.
  Admitted.
  
  Theorem exists_mp : (forall x, P x -> Q x) -> ex P -> ex Q.
  Proof.
  Admitted.
  
  Theorem or_exists :
    (exists x, P x) \/ (exists x, Q x) -> exists x, P x \/ Q x.
  Proof.
  Admitted.
  
  Hypothesis EM : forall P, P \/ ~P. (* 残りは排中律を使う *)

  Variables InPub Drinker : A -> Prop.

  Theorem drinkers_paradox :
    (exists consumer, InPub consumer) ->
    exists man, InPub man /\ Drinker man ->
                forall other, InPub other -> Drinker other.
  Proof.
  Admitted.
  
  Theorem remove_c : forall a,
      (forall x y, Q x -> Q y) ->
      (forall c, ((exists x, P x) -> P c) -> Q c) -> Q a.
  Proof.
  Admitted.

End Coq3.
