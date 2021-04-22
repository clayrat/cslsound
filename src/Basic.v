(*Require Import HahnBase ZArith List.*)
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat ssrint eqtype seq path.

Set Implicit Arguments.
Unset Strict Implicit.

Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x),
               (forall x, f1 x = f2 x) -> f1 = f2.

(** ** The heap model *)

Definition heap  := int -> option int.

Definition upd A (f: int -> A) x y a := if a == x then y else f a.

Definition hdef (h1 h2 : heap) := forall x, h1 x = None \/ h2 x = None.

Definition hplus (h1 h2 : heap) : heap :=
  (fun x => match h1 x with None => h2 x | Some y => Some y end).

Lemma hdefC : forall h1 h2, hdef h1 h2 -> hdef h2 h1.
Proof.
by rewrite /hdef=>?? H x; case: (H x); [right|left].
Qed.

Lemma hdefU h : hdef (fun _ => None) h.
Proof. by rewrite /hdef=>x; left. Qed.

Lemma hdefU2 h : hdef h (fun _ => None).
Proof. by rewrite /hdef=>x; right. Qed.

Lemma hdef_hplus :
  forall h1 h2 h3, hdef (hplus h1 h2) h3 <-> hdef h1 h3 /\ hdef h2 h3.
Proof.
rewrite /hdef /hplus=>h1 h2 h3; split.
- by move=>H;split=>x; case: (H x); try by [right]; case: (h1 x)=>//; left.
case=>H1 H2 x; case: (H1 x)=>->; last by right.
by case: (H2 x)=>->; [left|right].
Qed.

Lemma hdef_hplus2 :
  forall h1 h2 h3, hdef h1 (hplus h2 h3) <-> hdef h1 h2 /\ hdef h1 h3.
Proof.
rewrite /hdef /hplus=>h1 h2 h3; split.
- by move=>H; split=>x; case: (H x); try by [left]; case: (h2 x)=>//; right.
case=>H1 H2 x; case: (H1 x)=>->; first by left.
by case: (H2 x)=>->; [left|right].
Qed.

Corollary hdef_hplus_a :
  forall h1 h2 h3, hdef h1 h3 -> hdef h2 h3 -> hdef (hplus h1 h2) h3.
Proof.
by move=>*; apply/hdef_hplus.
Qed.

Corollary hdef_hplus_b :
  forall h1 h2 h3, hdef h1 h2 -> hdef h1 h3 -> hdef h1 (hplus h2 h3).
Proof. by move=>*; apply/hdef_hplus2. Qed.

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

Lemma hplusU h : hplus (fun _ => None) h = h.
Proof. by []. Qed.

Lemma hplusU2 h : hplus h (fun _ => None) = h.
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

Definition disjoint {A : eqType} (p q : seq A) := ~~ has (mem p) q.

Definition lminus {A : eqType} (p q : seq A) := filter (predC (mem q)) p.

Lemma remove_lminus {A : eqType} y (l l' : seq A) : filter (predC1 y) (lminus l l') = lminus (filter (predC1 y) l) l'.
Proof.
by rewrite /lminus -!filter_predI /predI; apply/eq_in_filter=>x H /=; rewrite andbC.
Qed.

Lemma cat_lminus {A : eqType} (p q r : seq A) : lminus p (q ++ r) = lminus (lminus p q) r.
Proof.
by rewrite /lminus -filter_predI /predI; apply/eq_in_filter=>x H /=; rewrite mem_cat negb_or andbC.
Qed.

Lemma canc_lminus {A : eqType} (p q r : seq A) : disjoint p r ->
    lminus (p ++ r) (q ++ r) = lminus p q.
Proof.
move=>H; rewrite cat_lminus /lminus -filter_predI filter_cat.
have E : [seq x <- r | predI [predC r] [predC q] x] = [::]
  by rewrite -(filter_pred0 r); apply/eq_in_filter=>x Hx /=; rewrite Hx.
rewrite E cats0; apply/eq_in_filter=>x Hx /=.
move: H; rewrite /disjoint => /hasPn /(_ x) /=; rewrite Hx.
by case: (x \in r) =>// /(_ erefl).
Qed.

(* repetition *)
Lemma cancr_lminus {A : eqType} (p q r : seq A) : disjoint r p ->
    lminus (r++p) (r++q) = lminus p q.
Proof.
move=>H; rewrite cat_lminus /lminus -filter_predI filter_cat.
have E : [seq x <- r | predI [predC q] [predC r] x] = [::]
  by rewrite -(filter_pred0 r); apply/eq_in_filter=>x Hx /=; rewrite Hx andbC.
rewrite E /=; apply/eq_in_filter=>x Hx /=.
move: H; rewrite /disjoint => /hasPn /(_ x) /=; rewrite Hx.
by case: (x \in r) =>// /(_ erefl); rewrite andbC.
Qed.

Lemma sub_cat {A : eqType} : forall (p q r : seq A), {subset p <= q} -> {subset p++r <= q++r}.
Proof.
by move=>p q r H x; rewrite !mem_cat=>/orP [/H ->|->] //; rewrite orbC.
Qed.

Lemma sub_cat_l {A : eqType} : forall (p q r : seq A), {subset p <= q} -> {subset r++p <= r++q}.
Proof.
by move=>p q r H x; rewrite !mem_cat=>/orP [->|/H ->]//; rewrite orbC.
Qed.

Lemma sub_ctr {A : eqType} : forall (p : seq A), {subset p++p <= p}.
Proof.
by move=>p x; rewrite mem_cat orbb.
Qed.

Lemma sub_filt {A : eqType} : forall p (q r : seq A), {subset q <= r} -> {subset filter p q <= filter p r}.
Proof.
by move=>p q r H x; rewrite !mem_filter=>/andP [-> /H].
Qed.

(** ** Basic list operations *)
(*
Fixpoint disjoint_list A (l : seq A) :=
  match l with
    | nil => True
    | x :: l => ~ (x \in l) /\ disjoint_list l
  end.

Definition disjoint A (xl yl : list A) :=
  forall x (IN: In x xl) (IN': In x yl), False.

Fixpoint removeAll A (eq_dec : forall x y : A, {x = y} + {x <> y}) l y :=
  match l with
    | nil => nil
    | x :: l =>
      if eq_dec x y then removeAll eq_dec l y
      else x :: removeAll eq_dec l y
  end.

Fixpoint list_minus A eq_dec (xl yl : list A) :=
  match yl with
    | nil => xl
    | y :: yl => list_minus eq_dec (removeAll eq_dec xl y) yl
  end.

Lemma removeAll_notin :
 forall A dec (x : A) l (NIN: ~ In x l),
   removeAll dec l x = l.
Proof.
  by induction l; ins; desf; [exfalso | f_equal]; eauto.
Qed.

Lemma removeAllK : forall A dec l (x : A),
  removeAll dec (removeAll dec l x) x = removeAll dec l x.
Proof.
  induction l; ins; desf; ins; desf; f_equal; auto.
Qed.

Lemma removeAllC : forall A dec l (x y : A),
  removeAll dec (removeAll dec l y) x = removeAll dec (removeAll dec l x) y.
Proof.
  induction l; ins; desf; ins; desf; f_equal; auto.
Qed.

Lemma removeAll_list_minus : forall A dec l l' (y : A),
  removeAll dec (list_minus dec l l') y =
  list_minus dec (removeAll dec l y) l'.
Proof.
  by ins; revert l; induction l'; ins; rewrite IHl', removeAllC.
Qed.

Lemma In_removeAll : forall A dec l (x y : A),
  In x (removeAll dec l y) <-> In x l /\ x <> y.
Proof.
  induction l; ins; desf; simpl; rewrite ?IHl;
    split; ins; des; clarify; auto.
Qed.

Lemma In_list_minus A dec l l' (x : A) :
  In x (list_minus dec l l') <-> In x l /\ ~ In x l'.
Proof.
  by revert l; induction l'; ins; desf; rewrite ?IHl', ?In_removeAll; intuition.
Qed.

Lemma disjoint_nil A (l : list A) : disjoint nil l.
Proof. by unfold disjoint. Qed.

Lemma disjoint_nil2 A (l : list A) : disjoint l nil.
Proof. by unfold disjoint. Qed.

Hint Resolve disjoint_nil disjoint_nil2.

Lemma disjoint_list_app :
  forall A (l1 l2 : list A), disjoint_list l1 -> disjoint_list l2 -> disjoint l1 l2 ->
    disjoint_list (l1 ++ l2).
Proof.
  unfold disjoint; induction l1; ins; rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma disjoint_list_removeAll : forall A dec l (y : A),
  disjoint_list l -> disjoint_list (removeAll dec l y).
Proof.
  induction l; ins; desf; simpl; try rewrite In_removeAll; intuition.
Qed.

Lemma disjoint_list_list_minus A dec (l l' : list A) :
  disjoint_list l -> disjoint_list (list_minus dec l l').
Proof.
  revert l; induction l'; ins; desf; auto using disjoint_list_removeAll.
Qed.

Lemma removeAll_irr: forall A dec l (x: A) (NIN: ~ In x l),
  removeAll dec l x = l.
Proof.
  induction l; ins; desf; [exfalso|f_equal]; eauto.
Qed.

Lemma removeAll_app A dec l l' (x: A) :
  removeAll dec (l ++ l') x = removeAll dec l x ++ removeAll dec l' x.
Proof.
  by induction l; ins; desf; rewrite IHl.
Qed.

Lemma list_minus_app A dec (x y z: list A) :
    list_minus dec x (y ++ z) = list_minus dec (list_minus dec x y) z.
Proof.
  by revert x; induction y; ins.
Qed.

Lemma list_minusC A dec (x y z: list A) :
    list_minus dec (list_minus dec x z) y = list_minus dec (list_minus dec x y) z.
Proof.
  by revert x; induction y; ins; rewrite removeAll_list_minus, IHy.
Qed.

Lemma list_minus1:
  forall A (x z: list A) (D: disjoint x z) dec w,
    list_minus dec (x ++ list_minus dec z w) z = x.
Proof.
  induction z; ins; [by induction w; ins; apply app_nil_r|].
  rewrite removeAll_app, removeAll_list_minus; simpl; desf.
  rewrite <- removeAll_list_minus, <- removeAll_app, <- removeAll_list_minus, IHz.
  by apply removeAll_irr; intro; eapply D; eauto using in_eq.
  by red; intros; eapply D; eauto using in_cons.
Qed.

Lemma list_minus2:
  forall A (x z: list A) (D: disjoint z x) dec w,
    list_minus dec (list_minus dec z w ++ x) z = x.
Proof.
  induction z; ins; [by induction w; ins|].
  rewrite removeAll_app, removeAll_list_minus; simpl; desf.
  rewrite <- removeAll_list_minus, <- removeAll_app, <- removeAll_list_minus, IHz; try done.
  by apply removeAll_irr; intro; eapply D; eauto using in_eq.
  by red; intros; eapply D; eauto using in_cons.
Qed.

Lemma list_minus_appr:
  forall A dec (x y z : list A), disjoint x z ->
    list_minus dec (x ++ z) (y ++ z) = list_minus dec x y.
Proof.
  ins; rewrite list_minus_app, list_minusC; f_equal.
  apply (list_minus1 H dec nil).
Qed.

Lemma list_minus_appl:
  forall A dec (x y z : list A), disjoint z x ->
    list_minus dec (z ++ x) (z ++ y) = list_minus dec x y.
Proof.
  ins; rewrite list_minus_app; f_equal; apply (list_minus2 H dec nil).
Qed.

Lemma list_minus_removeAll2 A dec x y (a: A) :
    list_minus dec (removeAll dec x a) (removeAll dec y a)
    = removeAll dec (list_minus dec x y) a.
Proof.
  revert x; induction y; ins; desf; simpls.
  by rewrite IHy, <- !removeAll_list_minus, removeAllK.
  by rewrite removeAllC, IHy.
Qed.

Lemma list_minus_removeAll_irr A dec (a: A) x (NIN: ~ In a x) y :
    list_minus dec x (removeAll dec y a) = list_minus dec x y.
Proof.
  revert x NIN; induction y; ins; desf; simpls; try rewrite IHy; eauto.
  by rewrite removeAll_irr.
  rewrite In_removeAll; intuition.
Qed.

(** ** Miscellaneous useful lemmas *)

Lemma ex_iff : forall A p q (EQ: forall x : A, p x <-> q x),
  (exists x, p x) <-> (exists x, q x).
Proof. firstorder. Qed.

Lemma all_iff : forall A p q (EQ: forall x : A, p x <-> q x),
  (forall x, p x) <-> (forall x, q x).
Proof. firstorder. Qed.

Lemma Eq_in_map:
  forall (T1 T2 : Type) (f1 f2 : T1 -> T2) (s : list T1),
  (forall x (IN: In x s), f1 x = f2 x) -> map f1 s = map f2 s.
Proof.
  induction s; ins; f_equal; auto.
Qed.
*)