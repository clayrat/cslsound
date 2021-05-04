From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat ssrint eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.

Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x),
               (forall x, f1 x = f2 x) -> f1 = f2.

Ltac exploit x :=
    refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _) _)
 || refine ((fun x y => y x) (x _ _) _)
 || refine ((fun x y => y x) (x _) _).

(** ** Miscellaneous useful lemmas *)

Lemma ex_iff : forall A p q (EQ: forall x : A, p x <-> q x),
(exists x, p x) <-> (exists x, q x).
Proof. firstorder. Qed.

Lemma all_iff : forall A p q (EQ: forall x : A, p x <-> q x),
(forall x, p x) <-> (forall x, q x).
Proof. firstorder. Qed.

(** ** The heap model *)

Definition loc  := int.
Definition heap := loc -> option int.

Definition hemp : heap := fun => None.

Definition singl k v : heap := fun a => if a == k then v else None.

Definition upd A (f: loc -> A) x y a := if a == x then y else f a.

Definition hdef (h1 h2 : heap) := forall x, h1 x = None \/ h2 x = None.

Definition hplus (h1 h2 : heap) : heap :=
  fun x => match h1 x with None => h2 x | Some y => Some y end.

Lemma hdefC : forall h1 h2, hdef h1 h2 -> hdef h2 h1.
Proof.
by rewrite /hdef=>?? H x; case: (H x); [right|left].
Qed.

Lemma hdefC' : forall h1 h2, hdef h1 h2 <-> hdef h2 h1.
Proof.
by move=>??; split; apply/hdefC.
Qed.

Lemma hdefU h : hdef hemp h.
Proof. by rewrite /hdef=>?; left. Qed.

Lemma hdefU2 h : hdef h hemp.
Proof. by rewrite /hdef=>?; right. Qed.

Lemma hdef_hplus :
  forall h1 h2 h3, hdef (hplus h1 h2) h3 <-> hdef h1 h3 /\ hdef h2 h3.
Proof.
rewrite /hdef /hplus=>h1 ??; split.
- by move=>H; split=>x; case: (H x); try by [right]; case: (h1 x)=>//; left.
case=>H1 H2 x; case: (H1 x)=>->; last by right.
by case: (H2 x)=>->; [left|right].
Qed.

Lemma hdef_hplus2 :
  forall h1 h2 h3, hdef h1 (hplus h2 h3) <-> hdef h1 h2 /\ hdef h1 h3.
Proof.
by move=>?? h3; rewrite hdefC' hdef_hplus hdefC' [hdef h3 _]hdefC'.
Qed.

Corollary hdef_hplus_a :
  forall h1 h2 h3, hdef h1 h3 -> hdef h2 h3 -> hdef (hplus h1 h2) h3.
Proof.
by move=>*; apply/hdef_hplus.
Qed.

Corollary hdef_hplus_b :
  forall h1 h2 h3, hdef h1 h2 -> hdef h1 h3 -> hdef h1 (hplus h2 h3).
Proof. by move=>*; apply/hdef_hplus2. Qed.

Lemma hdef_upd :
  forall h h' x v, h x <> None -> hdef h h' ->
  hdef (upd h x v) h'.
Proof.
move=>???? H0; rewrite /hdef /upd => H x; case: (H x); last by right.
move: H0; case: eqP; last by left.
by move=>->/[swap]->.
Qed.

Lemma hdef_upds :
  forall h h' x v v', hdef (upd h x (Some v)) h' ->
  hdef (upd h x (Some v')) h'.
Proof.
move=>?????; rewrite /hdef /upd => H x; case: (H x); last by right.
by case: eqP=>//; left.
Qed.

Hint Resolve hdef_hplus_a hdef_hplus_b : core.
Hint Immediate hdefC : core.

Lemma hplusA :
 forall h1 h2 h3, hplus (hplus h1 h2) h3 = hplus h1 (hplus h2 h3).
Proof.
by rewrite /hplus=>h1 h2 h3; apply: fext=>x; case: (h1 x).
Qed.

Lemma hplusC :
 forall h1 h2, hdef h1 h2 -> hplus h2 h1 = hplus h1 h2.
Proof.
rewrite /hplus=>h1 h2 H; apply: fext=>x.
case: (H x)=>->; by [case: (h2 x)| case: (h1 x)].
Qed.

Lemma hplusU h : hplus hemp h = h.
Proof. by []. Qed.

Lemma hplusU2 h : hplus h hemp = h.
Proof. rewrite hplusC //; apply: hdefU. Qed.

Lemma hplusAC :
 forall h1 h2 h3,
   hdef h1 h2 ->
   hplus h2 (hplus h1 h3) = hplus h1 (hplus h2 h3).
Proof.
rewrite /hplus=>h1 h2 h3 H; apply: fext=>x.
by case: (H x)=>->.
Qed.

Lemma hplusKl :
  forall h h1 h2,
    hplus h h1 = hplus h h2 -> hdef h h1 -> hdef h h2 ->
    h1 = h2.
Proof.
rewrite /hdef /hplus=>h h1 h2 H H1 H2; apply: fext=>x.
move/(f_equal (@^~ x)): H (H1 x) (H2 x).
by case: (h x)=>// a _; do 2![case=>//->].
Qed.

Lemma hplusKr :
  forall h h1 h2,
    hplus h1 h = hplus h2 h -> hdef h1 h -> hdef h2 h ->
    h1 = h2.
Proof.
rewrite /hdef /hplus=>h h1 h2 H H1 H2; apply: fext=>x.
move/(f_equal (@^~ x)): H (H1 x) (H2 x).
by case: (h1 x); case: (h2 x)=>// a ->; case=>// _; case.
Qed.

Section SeqStuff.
Variable (A : eqType).

Definition disjoint (p q : seq A) := ~~ has (mem p) q.

Definition remove a (p : seq A) := filter (predC1 a) p.

Definition lminus (p q : seq A) := filter (predC (mem q)) p.

Lemma inNotin (p : seq A) a b : a \in p -> b \notin p -> a != b.
Proof.
by move=>Ha Hb; apply/eqP=>He; rewrite -He Ha in Hb.
Qed.

Lemma remove_irr y (l : seq A) : y \notin l -> remove y l = l.
Proof.
move=>H; rewrite /remove; apply/all_filterP/allP=>x; move: H=>/[swap] /=; exact: inNotin.
Qed.

Lemma remove_lminus y (l l' : seq A) : remove y (lminus l l') = lminus (remove y l) l'.
Proof.
by rewrite /lminus /remove -!filter_predI /predI; apply/eq_in_filter=>x H /=; rewrite andbC.
Qed.

Lemma lminus_remove2 a (l l' : seq A) :
    lminus (remove a l) (remove a l') = remove a (lminus l l').
Proof.
rewrite /lminus /remove => /=.
rewrite -!filter_predI; apply/eq_in_filter=>x Hx /=.
by rewrite mem_filter negb_and andb_orl andNb andbC /=.
Qed.

Lemma lminus_remove y (l l' : seq A) : y \notin l -> lminus l (remove y l') = lminus l l'.
Proof.
by move=>H; rewrite -{1}(remove_irr H) lminus_remove2 remove_lminus (remove_irr H).
Qed.

Lemma cat_lminus (p q r : seq A) : lminus p (q ++ r) = lminus (lminus p q) r.
Proof.
by rewrite /lminus -filter_predI /predI; apply/eq_in_filter=>x H /=; rewrite mem_cat negb_or andbC.
Qed.

Lemma canc_lminus (p q r : seq A) : disjoint p r ->
    lminus (p++r) (q++r) = lminus p q.
Proof.
move=>H; rewrite cat_lminus /lminus -filter_predI filter_cat.
have E : [seq x <- r | predI [predC r] [predC q] x] = [::]
  by rewrite -(filter_pred0 r); apply/eq_in_filter=>x Hx /=; rewrite Hx.
rewrite E cats0; apply/eq_in_filter=>x Hx /=.
move: H; rewrite /disjoint => /hasPn /(_ x) /=; rewrite Hx.
by case: (x \in r) =>// /(_ erefl).
Qed.

(* repetition *)
Lemma cancr_lminus (p q r : seq A) : disjoint r p ->
    lminus (r++p) (r++q) = lminus p q.
Proof.
move=>H; rewrite cat_lminus /lminus -filter_predI filter_cat.
have E : [seq x <- r | predI [predC q] [predC r] x] = [::]
  by rewrite -(filter_pred0 r); apply/eq_in_filter=>x Hx /=; rewrite Hx andbC.
rewrite E /=; apply/eq_in_filter=>x Hx /=.
move: H; rewrite /disjoint => /hasPn /(_ x) /=; rewrite Hx.
by case: (x \in r) =>// /(_ erefl); rewrite andbC.
Qed.

Lemma sub_cat : forall (p q r : seq A), {subset p <= q} -> {subset p++r <= q++r}.
Proof.
by move=>p q r H x; rewrite !mem_cat=>/orP [/H ->|->] //; rewrite orbC.
Qed.

Lemma sub_cat_l : forall (p q r : seq A), {subset p <= q} -> {subset r++p <= r++q}.
Proof.
by move=>p q r H x; rewrite !mem_cat=>/orP [->|/H ->]//; rewrite orbC.
Qed.

Lemma sub_ctr : forall (p : seq A), {subset p++p <= p}.
Proof.
by move=>p x; rewrite mem_cat orbb.
Qed.

Lemma sub_filt : forall p (q r : seq A), {subset q <= r} -> {subset filter p q <= filter p r}.
Proof.
by move=>p q r H x; rewrite !mem_filter=>/andP [-> /H].
Qed.

End SeqStuff.
