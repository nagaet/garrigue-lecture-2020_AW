Section Koushin.
  Variables P Q : Prop.
  
  Theorem modus_ponens : P -> (P -> Q) -> Q.
  Proof.
    intros p pq.
    apply pq.
    assumption.
  Qed.

  Reset modus_ponens. (* module_ponens 以降の定義を忘れる *)
  Require Import ssreflect. (* ssreflect のタクティック言語を使う *)
  Theorem modus_ponens : P -> (P -> Q) -> Q.
  Proof.
    move=> p.
    move/(_ p).
    done.
  Qed.

  Theorem modus_ponens2 : P -> (P -> Q) -> Q.
  Proof.
      by move => p /(_ p). (* 全てを一行にまとめる *)
  Qed.

  Theorem and_comm : P /\ Q -> Q /\ P.
  Proof.
    move=> [] p q. (* ∧-L, Intro, Intro *)
    split.
    done. done.
  Qed.
  
  Theorem and_comm2 : P /\ Q -> Q /\ P.
  Proof.
      by move=> [p q]; split.
  Qed.

  Theorem or_comm : P \/ Q -> Q \/ P.
  Proof.
    move=> [p|q]. (* (∨-L; 証明木が分岐するとき，縦棒「|」で分ける *)
      by right. (* ∨-R2 *) by left. (* ∨-R1 *)
  Qed.
  
  Theorem DeMorgan : ~ (P \/ Q) -> ~ P /\ ~ Q.
  Proof.
    rewrite /not. (* 定義を展開する *)
    move=> npq.
    split=> [p|q]. (* 全てのタクティックで「=>」が使える *)
    apply: npq. (* (Apply-R) *) by left.
    apply: npq. by right.
  Qed.
End Koushin. (* Section を閉じる *)


Section Classic.
  Definition Classic := forall P : Prop, ~ ~ P -> P. (* ¬¬ 除去の定義 *)
  Definition EM := forall P : Prop, P \/ ~ P. (* 排中律の定義 *)

  Lemma Classic_is_EM : Classic <-> EM. (* ¬¬ 除去と排中律が同値 *)
  Proof.
    rewrite /Classic /EM. (* 定義の展開 *)
    split => [classic | em] P. (* A <-> B := A -> B /\ B -> A *)
    - apply: (classic) => nEM. (* classic を仮定から消さずに焦点におく *)
      have p : P. (* (カット) *)
      apply: classic => np.
      apply: nEM. by right.
      apply: nEM. by left.
    - move: (em P) => []. (* P についての排中律で場合分けをする *)
      + done.
      + move => np /(_ np). done.
  Qed.

  Variables P Q : Prop.
  Theorem DeMorgan' : Classic -> ~ (P /\ Q) -> ~ P \/ ~ Q.
  Proof.
    move=> /Classic_is_EM em npq. (* Apply-L1, Intro, Intro *)
    move: (em P) => [p|np]. (* 排中律で場合分け *)
    - move: (em Q) => [q|nq].
      + elim: npq. (* 矛盾 *)  by split.
      + by right.
    - by left.
  Qed.

End Classic. (* Section を閉じる *)
Check DeMorgan'. (* 命題の言明を確認する *)

(*練習問題 2.1 以下の定理を Coq で証明せよ．*)
Section Coq1.
  Variables P Q R : Prop.
  Theorem imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
  Admitted.
  
  Theorem not_false : ~False.
  Proof.
  Admitted.
    
  Theorem double_neg : P -> ~~P.
  Proof.
  Admitted.
  
  Theorem contraposition : (P -> Q) -> ~Q -> ~P.
  Proof.
  Admitted.
      
  Theorem and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
  Proof.
  Admitted.
    
  Theorem and_distr : P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
  Proof.
  Admitted.
  
  Theorem absurd : P -> ~P -> Q.
  Proof.
  Admitted.
  
  Definition DM_rev := forall P Q, ~ (~P /\ ~Q) -> P \/ Q.
  Theorem DM_rev_is_EM : DM_rev <-> EM.
  Proof.
  Admitted.
End Coq1.

