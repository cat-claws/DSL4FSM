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

Definition simplify_base (l : list ltl) : list ltl :=
  nodup ltl_eq_dec (filter (fun p => negb (is_true p)) l).

Definition complement (a b : ltl) : bool :=
  match a, b with
  | Glob x, Glob (LNot y) => ltl_beq x y
  | Glob (LNot x), Glob y => ltl_beq x y
  | _, _ => false
  end.

Definition has_conflict (l : list ltl) : bool :=
  existsb (fun a => existsb (fun b => complement a b) l) l.

Definition imp_conflict (gp gnq gimp : ltl) : bool :=
  match gp, gnq, gimp with
  | Glob p, Glob (LNot q), Glob (LImp p' q') =>
      andb (ltl_beq p p') (ltl_beq q q')
  | _, _, _ => false
  end.

Definition has_imp_conflict (l : list ltl) : bool :=
  existsb (fun gp =>
    existsb (fun gnq =>
      existsb (fun gimp => imp_conflict gp gnq gimp) l
    ) l
  ) l.

Definition infer_from_imp (l : list ltl) (f : ltl) : list ltl :=
  match f with
  | Glob (LImp p q) =>
      if existsb (fun x => ltl_beq x (Glob p)) l
      then [Glob q]
      else []
  | _ => []
  end.

Definition infer_step (l : list ltl) : list ltl :=
  fold_right (fun f acc => infer_from_imp l f ++ acc) [] l.

Definition dedup (l : list ltl) : list ltl := nodup ltl_eq_dec l.

Definition infer_closure_once (l : list ltl) : list ltl :=
  dedup (l ++ infer_step l).

Fixpoint infer_closure_fuel (fuel : nat) (l : list ltl) : list ltl :=
  match fuel with
  | O => l
  | S n =>
      let l' := infer_closure_once l in
      if Nat.leb (length l') (length l) then l else infer_closure_fuel n l'
  end.

Definition simplify_conj (l : list ltl) : list ltl :=
  if existsb is_false l then [LFalse]
  else
    let l0 := simplify_base l in
    let l1 := infer_closure_fuel (length l0 + length l0 + 4) l0 in
    if orb (has_conflict l1) (has_imp_conflict l1) then [LFalse] else l1.

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

Lemma simplify_base_sound : forall tr i l,
  all_sat tr i (simplify_base l) <-> all_sat tr i l.
Proof.
  intros tr i l.
  unfold simplify_base.
  rewrite all_sat_nodup_iff.
  apply all_sat_filter_drop_true_iff.
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

Lemma has_conflict_exists_pair : forall l,
  has_conflict l = true -> exists a b, In a l /\ In b l /\ complement a b = true.
Proof.
  intros l H.
  unfold has_conflict in H.
  apply existsb_exists in H.
  destruct H as [a [Ha Hinner]].
  apply existsb_exists in Hinner.
  destruct Hinner as [b [Hb Hc]].
  exists a, b. repeat split; assumption.
Qed.

Lemma has_imp_conflict_exists_triple : forall l,
  has_imp_conflict l = true ->
  exists gp gnq gimp, In gp l /\ In gnq l /\ In gimp l /\ imp_conflict gp gnq gimp = true.
Proof.
  intros l H.
  unfold has_imp_conflict in H.
  apply existsb_exists in H.
  destruct H as [gp [Hgp Hrest]].
  apply existsb_exists in Hrest.
  destruct Hrest as [gnq [Hgnq Hrest2]].
  apply existsb_exists in Hrest2.
  destruct Hrest2 as [gimp [Hgimp Hc]].
  exists gp, gnq, gimp.
  repeat split; assumption.
Qed.

Lemma complement_true_cases : forall a b,
  complement a b = true ->
  (exists x, a = Glob x /\ b = Glob (LNot x)) \/
  (exists x, a = Glob (LNot x) /\ b = Glob x).
Proof.
  intros a b Hc.
  unfold complement in Hc.
  destruct a as [na| | |a0|a1 a2|a1 a2|a0|a0]; try discriminate.
  destruct b as [nb| | |b0|b1 b2|b1 b2|b0|b0].
  - destruct a0; cbn in Hc; inversion Hc.
  - destruct a0; cbn in Hc; inversion Hc.
  - destruct a0; cbn in Hc; inversion Hc.
  - destruct a0; cbn in Hc; inversion Hc.
  - destruct a0; cbn in Hc; inversion Hc.
  - destruct a0; cbn in Hc; inversion Hc.
  - destruct a0; cbn in Hc; inversion Hc.
  - destruct b0 as [n| | |y|u v|u v|y|y].
    + destruct a0 as [x| | |x|x1 x2|x1 x2|x|x]; cbn in Hc; try discriminate.
      apply ltl_beq_true_eq in Hc. subst.
      right. exists (Atom n). split; reflexivity.
    + destruct a0 as [x| | |x|x1 x2|x1 x2|x|x]; cbn in Hc; try discriminate.
      apply ltl_beq_true_eq in Hc. subst.
      right. exists LTrue. split; reflexivity.
    + destruct a0 as [x| | |x|x1 x2|x1 x2|x|x]; cbn in Hc; try discriminate.
      apply ltl_beq_true_eq in Hc. subst.
      right. exists LFalse. split; reflexivity.
    + assert (Hbeq : ltl_beq a0 y = true).
      { destruct a0; cbn in Hc; exact Hc. }
      apply ltl_beq_true_eq in Hbeq. subst.
      left. exists y. split; reflexivity.
    + destruct a0 as [x| | |x|x1 x2|x1 x2|x|x]; cbn in Hc; try discriminate.
      apply ltl_beq_true_eq in Hc. subst.
      right. exists (LAnd u v). split; reflexivity.
    + destruct a0 as [x| | |x|x1 x2|x1 x2|x|x]; cbn in Hc; try discriminate.
      apply ltl_beq_true_eq in Hc. subst.
      right. exists (LImp u v). split; reflexivity.
    + destruct a0 as [x| | |x|x1 x2|x1 x2|x|x]; cbn in Hc; try discriminate.
      apply ltl_beq_true_eq in Hc. subst.
      right. exists (LNext y). split; reflexivity.
    + destruct a0 as [x| | |x|x1 x2|x1 x2|x|x]; cbn in Hc; try discriminate.
      apply ltl_beq_true_eq in Hc. subst.
      right. exists (Glob y). split; reflexivity.
Qed.

Lemma complement_sat_false : forall tr i a b,
  complement a b = true -> sat tr i a -> sat tr i b -> False.
Proof.
  intros tr i a b Hc Ha Hb.
  apply complement_true_cases in Hc.
  destruct Hc as [[x [HaEq HbEq]] | [x [HaEq HbEq]]].
  - subst.
    specialize (Ha i (le_n i)).
    specialize (Hb i (le_n i)).
    simpl in Hb.
    exact (Hb Ha).
  - subst.
    specialize (Ha i (le_n i)).
    specialize (Hb i (le_n i)).
    simpl in Ha.
    exact (Ha Hb).
Qed.

Lemma existsb_ltl_beq_in : forall l a,
  existsb (fun x => ltl_beq x a) l = true -> In a l.
Proof.
  intros l a H.
  apply existsb_exists in H.
  destruct H as [x [Hin Hx]].
  apply ltl_beq_true_eq in Hx.
  subst. exact Hin.
Qed.

Lemma all_sat_app_iff : forall tr i l1 l2,
  all_sat tr i (l1 ++ l2) <-> (all_sat tr i l1 /\ all_sat tr i l2).
Proof.
  intros tr i l1 l2.
  unfold all_sat.
  split.
  - intros H. split.
    + intros p Hin. apply H. apply in_or_app. left. exact Hin.
    + intros p Hin. apply H. apply in_or_app. right. exact Hin.
  - intros [H1 H2] p Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply H1. exact Hin.
    + apply H2. exact Hin.
Qed.

Lemma infer_from_imp_sound : forall tr i l f,
  all_sat tr i l -> In f l -> all_sat tr i (infer_from_imp l f).
Proof.
  intros tr i l f Hall Hinf.
  destruct f as [n| | |p|p q|p q|p|p]; simpl; try (unfold all_sat; intros x H; inversion H).
  destruct p as [n| | |p1|p1 p2|p1 p2|p1|p1]; simpl; try (unfold all_sat; intros x H; inversion H).
  destruct (existsb (fun x : ltl => ltl_beq x (Glob p1)) l) eqn:Hex.
  - unfold all_sat. intros x Hx.
    simpl in Hx. destruct Hx as [Hx | Hx]; [|inversion Hx].
    subst x.
    assert (Hp1 : In (Glob p1) l).
    { apply existsb_ltl_beq_in. exact Hex. }
    pose proof (Hall (Glob (LImp p1 p2)) Hinf) as Himp.
    pose proof (Hall (Glob p1) Hp1) as Hp.
    intros j Hj.
    specialize (Himp j Hj).
    specialize (Hp j Hj).
    simpl in Himp.
    apply Himp.
    exact Hp.
  - unfold all_sat. intros x Hx. inversion Hx.
Qed.

Lemma infer_fold_sound : forall tr i base cur,
  (forall f, In f cur -> In f base) ->
  all_sat tr i base ->
  all_sat tr i (fold_right (fun f acc => infer_from_imp base f ++ acc) [] cur).
Proof.
  intros tr i base cur Hsub Hall.
  induction cur as [|h t IH].
  - unfold all_sat. intros p Hin. inversion Hin.
  - simpl.
    rewrite all_sat_app_iff.
    split.
    + apply infer_from_imp_sound.
      * exact Hall.
      * apply Hsub. left. reflexivity.
    + eapply IH; eauto.
      intros f Hin. apply Hsub. right. exact Hin.
Qed.

Lemma infer_step_sound : forall tr i l,
  all_sat tr i l -> all_sat tr i (infer_step l).
Proof.
  intros tr i l Hall.
  unfold infer_step.
  apply infer_fold_sound.
  - intros f Hin. exact Hin.
  - exact Hall.
Qed.

Lemma infer_closure_once_sound : forall tr i l,
  all_sat tr i (infer_closure_once l) <-> all_sat tr i l.
Proof.
  intros tr i l.
  unfold infer_closure_once.
  rewrite all_sat_nodup_iff.
  rewrite all_sat_app_iff.
  split.
  - intros [Hl _]. exact Hl.
  - intros Hl. split.
    + exact Hl.
    + apply infer_step_sound. exact Hl.
Qed.

Lemma infer_closure_fuel_sound : forall fuel tr i l,
  all_sat tr i (infer_closure_fuel fuel l) <-> all_sat tr i l.
Proof.
  induction fuel as [|n IH]; intros tr i l.
  - simpl. tauto.
  - simpl.
    set (l' := infer_closure_once l).
    destruct (Nat.leb (length l') (length l)) eqn:Hleb.
    + tauto.
    + rewrite IH with (l := l').
      unfold l'.
      apply infer_closure_once_sound.
Qed.

Lemma all_sat_conflict_false : forall tr i l,
  has_conflict l = true -> all_sat tr i l -> False.
Proof.
  intros tr i l Hc Hall.
  apply has_conflict_exists_pair in Hc.
  destruct Hc as [a [b [Ha [Hb Hcomp]]]].
  eapply complement_sat_false.
  - exact Hcomp.
  - apply Hall. exact Ha.
  - apply Hall. exact Hb.
Qed.

Lemma imp_conflict_sat_false : forall tr i gp gnq gimp,
  imp_conflict gp gnq gimp = true ->
  sat tr i gp -> sat tr i gnq -> sat tr i gimp -> False.
Proof.
  intros tr i gp gnq gimp Hc Hgp Hgnq Hgimp.
  unfold imp_conflict in Hc.
  destruct gp as [na| | |n|n1 n2|n1 n2|n|p]; try discriminate.
  destruct gnq as [na| | |n|n1 n2|n1 n2|n|gnq0]; try discriminate.
  destruct gnq0 as [na| | |q|n1 n2|n1 n2|n|n]; try discriminate.
  destruct gimp as [na| | |n|n1 n2|n1 n2|n|gimp0]; try discriminate.
  destruct gimp0 as [na| | |n|n1 n2|p' q'|n|n]; try discriminate.
  simpl in Hc.
  apply andb_true_iff in Hc as [Hp Hq].
  apply ltl_beq_true_eq in Hp.
  apply ltl_beq_true_eq in Hq.
  subst.
  specialize (Hgp i (le_n i)).
  specialize (Hgnq i (le_n i)).
  specialize (Hgimp i (le_n i)).
  simpl in Hgnq.
  simpl in Hgimp.
  apply Hgnq.
  apply Hgimp.
  exact Hgp.
Qed.

Lemma all_sat_imp_conflict_false : forall tr i l,
  has_imp_conflict l = true -> all_sat tr i l -> False.
Proof.
  intros tr i l Hc Hall.
  apply has_imp_conflict_exists_triple in Hc.
  destruct Hc as [gp [gnq [gimp [Hgp [Hgnq [Hgimp Himp]]]]]].
  eapply imp_conflict_sat_false.
  - exact Himp.
  - apply Hall. exact Hgp.
  - apply Hall. exact Hgnq.
  - apply Hall. exact Hgimp.
Qed.

Theorem simplify_conj_sound : forall tr i l,
  all_sat tr i (simplify_conj l) <-> all_sat tr i l.
Proof.
  intros tr i l.
  unfold simplify_conj.
  destruct (existsb is_false l) eqn:Hexf.
  - rewrite all_sat_with_false_iff_false with (l := l); [|exact Hexf].
    assert (Hsingle : all_sat tr i [LFalse] <-> False).
    { unfold all_sat.
      split.
      - intros H.
        specialize (H LFalse (or_introl eq_refl)).
        simpl in H. exact H.
      - intros HFalse p Hin.
        destruct Hin as [Hin | Hin].
        + subst p. contradiction.
        + inversion Hin.
    }
    rewrite Hsingle.
    tauto.
  - set (l0 := simplify_base l).
    set (l1 := infer_closure_fuel (length l0 + length l0 + 4) l0).
    destruct (orb (has_conflict l1) (has_imp_conflict l1)) eqn:Horb.
    + split.
      * intros H.
        exfalso.
        unfold all_sat in H.
        specialize (H LFalse (or_introl eq_refl)).
        simpl in H.
        exact H.
      * intros Hl.
        assert (Hl0 : all_sat tr i l0).
        { subst l0. apply simplify_base_sound. exact Hl. }
        assert (Hl1 : all_sat tr i l1).
        { subst l1.
          apply (proj2 (infer_closure_fuel_sound (length l0 + length l0 + 4) tr i l0)).
          exact Hl0. }
        apply orb_true_iff in Horb.
        destruct Horb as [Hc | Hic].
        { exfalso. eapply all_sat_conflict_false; eauto. }
        { exfalso. eapply all_sat_imp_conflict_false; eauto. }
    + split.
      * intros Hl1.
        assert (Hl0 : all_sat tr i l0).
        { subst l1.
          apply (proj1 (infer_closure_fuel_sound (length l0 + length l0 + 4) tr i l0)).
          exact Hl1. }
        subst l0.
        apply simplify_base_sound.
        exact Hl0.
      * intros Hl.
        assert (Hl0 : all_sat tr i l0).
        { subst l0. apply simplify_base_sound. exact Hl. }
        subst l1.
        apply (proj2 (infer_closure_fuel_sound (length l0 + length l0 + 4) tr i l0)).
        exact Hl0.
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
  repeat rewrite conj_to_ltl_sound.
  apply simplify_conj_sound.
Qed.
