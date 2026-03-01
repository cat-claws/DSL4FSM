From Coq Require Import List Bool Arith Lia.
Import ListNotations.

Inductive ltl : Type :=
| Atom : nat -> ltl
| LTrue : ltl
| LFalse : ltl
| LNot : ltl -> ltl
| LAnd : ltl -> ltl -> ltl
| LImp : ltl -> ltl -> ltl
| LNext : ltl -> ltl
| Glob : ltl -> ltl.

Scheme Equality for ltl.

Definition trace := nat -> nat -> Prop.

Fixpoint sat (tr : trace) (i : nat) (phi : ltl) : Prop :=
  match phi with
  | Atom a => tr i a
  | LTrue => True
  | LFalse => False
  | LNot p => ~ sat tr i p
  | LAnd p q => sat tr i p /\ sat tr i q
  | LImp p q => sat tr i p -> sat tr i q
  | LNext p => sat tr (S i) p
  | Glob p => forall j, i <= j -> sat tr j p
  end.

Definition all_sat (tr : trace) (i : nat) (l : list ltl) : Prop :=
  forall p, In p l -> sat tr i p.

Definition is_true (p : ltl) : bool := ltl_beq p LTrue.
Definition is_false (p : ltl) : bool := ltl_beq p LFalse.

Definition simplify_conj (l : list ltl) : list ltl :=
  if existsb is_false l
  then [LFalse]
  else nodup ltl_eq_dec (filter (fun p => negb (is_true p)) l).

Lemma ltl_beq_true_eq : forall x y, ltl_beq x y = true -> x = y.
Proof.
  intros x y H.
  pose proof (internal_ltl_dec_bl x y H) as E.
  exact E.
Qed.

Lemma in_nodup_iff : forall x l,
  In x (nodup ltl_eq_dec l) <-> In x l.
Proof.
  intros x l.
  apply nodup_In.
Qed.

Lemma all_sat_nodup_iff : forall tr i l,
  all_sat tr i (nodup ltl_eq_dec l) <-> all_sat tr i l.
Proof.
  intros tr i l.
  unfold all_sat.
  split; intros H p Hin.
  - apply H. apply in_nodup_iff. exact Hin.
  - apply H. apply in_nodup_iff. exact Hin.
Qed.

Lemma all_sat_filter_drop_true_iff : forall tr i l,
  all_sat tr i (filter (fun p => negb (is_true p)) l) <-> all_sat tr i l.
Proof.
  intros tr i l.
  unfold all_sat.
  split.
  - intros H p Hin.
    destruct (is_true p) eqn:Ht.
    + apply ltl_beq_true_eq in Ht. subst p. simpl. trivial.
    + apply H. apply filter_In. split.
      * exact Hin.
      * rewrite Ht. simpl. reflexivity.
  - intros H p Hin.
    apply filter_In in Hin as [Hin _].
    apply H. exact Hin.
Qed.

Lemma all_sat_with_false_iff_false : forall tr i l,
  existsb is_false l = true -> (all_sat tr i l <-> False).
Proof.
  intros tr i l Hex.
  unfold all_sat.
  apply existsb_exists in Hex.
  destruct Hex as [p [Hin Hp]].
  unfold is_false in Hp.
  apply ltl_beq_true_eq in Hp.
  subst p.
  split.
  - intros H.
    specialize (H LFalse Hin).
    simpl in H.
    exact H.
  - intros HFalse p0 _. contradiction.
Qed.

Theorem simplify_conj_sound : forall tr i l,
  all_sat tr i (simplify_conj l) <-> all_sat tr i l.
Proof.
  intros tr i l.
  unfold simplify_conj.
  destruct (existsb is_false l) eqn:Hex.
  - split.
    + intros Hs.
      exfalso.
      exact (Hs LFalse (or_introl eq_refl)).
    + intros Hl.
      pose proof (proj1 (all_sat_with_false_iff_false tr i l Hex) Hl) as F.
      intros p Hin.
      simpl in Hin.
      destruct Hin as [Hin | Hin].
      * subst p. exfalso. exact F.
      * contradiction.
  - rewrite all_sat_nodup_iff.
    apply all_sat_filter_drop_true_iff.
Qed.

Definition conj_to_ltl (l : list ltl) : ltl :=
  fold_right LAnd LTrue l.

Theorem conj_to_ltl_sound : forall tr i l,
  sat tr i (conj_to_ltl l) <-> all_sat tr i l.
Proof.
  intros tr i l.
  induction l as [|h t IH].
  - simpl. unfold all_sat. split.
    + intros _. intros p Hin. inversion Hin.
    + intros _. trivial.
  - simpl. rewrite IH.
    unfold all_sat.
    split.
    + intros [Hh Ht] p Hin.
      destruct Hin as [Hin | Hin].
      * subst p. exact Hh.
      * apply Ht. exact Hin.
    + intros Hall. split.
      * apply Hall. left. reflexivity.
      * intros p Hin. apply Hall. right. exact Hin.
Qed.

Theorem simplify_conj_to_ltl_sound : forall tr i l,
  sat tr i (conj_to_ltl (simplify_conj l)) <-> sat tr i (conj_to_ltl l).
Proof.
  intros tr i l.
  rewrite !conj_to_ltl_sound.
  apply simplify_conj_sound.
Qed.
