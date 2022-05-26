From Coq Require Import ssreflect ssrbool ssrfun List.
From mathcomp Require Import ssrnat ssrint eqtype seq path.
From cslsound Require Import Basic Lang.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Assertions and the meaning of CSL judgments *)

(** ** Separation logic assertions

  We represent separation logic assertions as the Coq [assn] (i.e., a
  deep embedding). Here is the syntax of assertions: *)

Inductive assn : Set :=
    Aemp
  | Apure (b: bexp)
  | Aconj (p1: assn) (p2: assn)
  | Adisj (p1: assn) (p2: assn)
  | Astar (p1: assn) (p2: assn)
  | Awand (p1 p2: assn)
  | Anot (p : assn)
  | Apointsto (e1 e2: exp)
  | Aex (pp: nat -> assn).

(** Separating conjunction of a finite list of assertions is just a
  derived assertion. *)

Fixpoint Aistar ps :=
  match ps with
    | nil => Aemp
    | p :: ps => Astar p (Aistar ps)
  end.

(** The semantics of assertions is given by the following function
  indicating whether a state [ss] satisfies an assertion [p]. *)

Fixpoint sat ss p :=
  match p with
    | Aemp            => ss.2 = hemp
    | Apure b         => bdenot b ss.1
    | Aconj p q       => sat ss p /\ sat ss q
    | Adisj p q       => sat ss p \/ sat ss q
    | Astar p q       => exists h1 h2, sat (ss.1, h1) p /\ sat (ss.1, h2) q
                          /\ hdef h1 h2 /\ hplus h1 h2 = ss.2
    | Awand p q       => forall h (SAT: sat (ss.1, h) p) (HD: hdef ss.2 h),
                          sat (ss.1, hplus ss.2 h) q
    | Apointsto e1 e2 => ss.2 = singl (edenot e1 ss.1)
                                      (Some (edenot e2 ss.1))
    | Anot p          => not (sat ss p)
    | Aex pp          => exists v, sat ss (pp v)
  end.

(** We can derive the following unfolding lemma for iterated
  separating conjunction. *)

Lemma sat_istar_map_expand :
  forall r l ss (f : int -> assn) (IN: r \in l) (DL: uniq l),
    sat ss (Aistar (map f l))
    <-> exists h1 h2, sat (ss.1, h1) (f r)
      /\ sat (ss.1, h2) (Aistar (map f (remove r l)))
      /\ hdef h1 h2 /\ hplus h1 h2 = ss.2.
Proof.
move=>? l [? h] ?.
elim: l h=>//= a l H ?; rewrite inE=>/orP H1 /andP [Ha Hu]; case: H1.
- move/eqP=>->; rewrite /remove eq_refl=>/=; suff: all (predC1 a) l by move/all_filterP=>->.
  by apply/allP=>? /=; case: eqP Ha=>//->/[swap]->.
move=>Hr; case: eqP=>/=; first by move: Ha=>/[swap]->; rewrite Hr.
move=>Hn; split.
- move=>[h1][h2][?][H1][H2]<-.
  move: ((H h2 Hr Hu).1 H1)=>[h3][h4][?][?][?]HH4.
  move: H1 H2; rewrite -{}HH4=> _ /hdef_hplus2 [??].
  exists h3, (hplus h1 h4); do!split=>//.
  exists h1, h4; do!split=>//.
  - by apply/hdef_hplus2; split; [apply/hdefC|].
  by rewrite hplusAC.
move=>[h1][?][?][[h3][h4][?][?][?<-]][H6<-].
move/hdef_hplus2: H6=>[H5 H6].
exists h3, (hplus h1 h4); do!split=>//.
- by apply: (H (hplus h1 h4) Hr Hu).2; exists h1, h4; do!split.
- by apply/hdef_hplus2; split; [apply/hdefC|].
by rewrite hplusAC.
Qed.

(** ** Precision

  We say that a assertion is precise if for any given heap, there is
  at most one subheap that satisfies the formula. (The formal
  definition below says that if there are two such subheaps, they must
  be equal.) *)

Definition precise p :=
  forall h1 h2 h1' h2' s
    (SAT: sat (s, h1) p)
    (SAT': sat (s, h1') p)
    (EQ: hplus h1 h2 = hplus h1' h2')
    (D : hdef h1 h2)
    (D': hdef h1' h2'),
    h1 = h1'.

(*Ltac inss := ins; desf; unnw; intuition; desf.*)

(** The empty assertion, emp, is precise. *)

Lemma precise_emp: precise Aemp.
Proof. by move=>/= ?????->->. Qed.

(** Star conjunction of precise assertions is precise. *)

Lemma precise_star p q: precise p -> precise q -> precise (Astar p q).
Proof.
rewrite /precise=>/= H1 H2 ? h01 ? h02 ? [h1][h2][Hs1][Hs2][H12]<-[h3][h4][Hs3][Hs4][H34]<-HE /hdef_hplus [HD1 HD2] /hdef_hplus [HD3 HD4].
rewrite !hplusA in HE.
have H13 : h1 = h3 by eauto.
move: H12 HD1 HE; rewrite H13 => H12 HD1 HE; f_equal.
rewrite (hplusAC h01) in HE; last by apply hdefC.
rewrite (hplusAC h02) in HE; last by apply hdefC.
by eauto.
Qed.

(* Can't have eqType on assn because it has functions *)

Lemma precise_istar:
  forall (l : seq assn) (P: forall x, In x l -> precise x), precise (Aistar l).
Proof.
elim=>/=.
- by move=> _; apply: precise_emp.
move=>?? H H2; apply: precise_star.
- by apply: H2; left.
by apply: H=>x Hx; apply: H2; right.
Qed.

(** ** Auxiliary definitions for resource invariants *)

Definition assn_lift po := match po with None => Aemp | Some p => p end.

Definition envs G (l l' : seq rname) :=
  (Aistar (map (fun x => assn_lift (G x)) (lminus l l'))).

Lemma sat_envs_expand:
  forall r l l' (IN: r \in l) (NIN: r \notin l')
    (LD: uniq l) J ss,
    sat ss (envs J l l')
    <-> exists h1 h2, sat (ss.1, h1) (assn_lift (J r))
              /\ sat (ss.1, h2) (envs J (remove r l) l')
              /\ ss.2 = hplus h1 h2 /\ hdef h1 h2.
Proof.
rewrite /envs=>/= r ?? Hi Hn ???.
rewrite (sat_istar_map_expand (r:=r)).
- by rewrite remove_lminus; split; move=>[h1][h2][?][?][?]?; exists h1, h2; do!split.
- by rewrite /lminus mem_filter Hi /= Hn.
by rewrite /lminus; apply/filter_uniq.
Qed.

Lemma envs_app1 :
  forall x z (D: disjoint x z) J y, envs J (x ++ z) (y ++ z) = envs J x y.
Proof. by rewrite /envs=>/= ?????; rewrite canc_lminus. Qed.

Lemma envs_app2 :
  forall x z (D: disjoint z x) J y, envs J (z ++ x) (z ++ y) = envs J x y.
Proof. by rewrite /envs=>/= ?????; rewrite cancr_lminus. Qed.

Lemma envs_removeAll_irr:
  forall r l (NIN: r \notin l) J l', envs J l (remove r l') = envs J l l'.
Proof.
by rewrite /envs=>/= ?????; rewrite lminus_remove.
Qed.

Lemma envs_removeAll2:
  forall r l' (IN: r \in l') J l,
    envs J (remove r l) (remove r l') = envs J l l'.
Proof.
rewrite /envs=>/= ? l' ???; rewrite lminus_remove2.
do 2!f_equal; rewrite /remove; apply/all_filterP/allP=>? Hy /=.
rewrite eq_sym; apply/(inNotin (p:=l'))=>//.
by move: Hy; rewrite mem_filter /= =>/andP [].
Qed.

Lemma envs_cons2_irr:
  forall r l (NIN: r \notin l) J l', envs J (r :: l) (r :: l') = envs J l l'.
Proof.
rewrite /envs=>r ? H ?? /=; do 2!f_equal; rewrite inE eq_refl /=.
rewrite /lminus; apply/eq_in_filter=>x Hx /=; rewrite inE negb_or.
by suff: (x!=r); [move=>->| move: Hx H; apply/inNotin].
Qed.

Lemma envs_upd_irr : forall J r v l l',
   r \notin l \/ r \in l' -> envs (upd J r v) l l' = envs J l l'.
Proof.
rewrite /envs /upd=>????? H.
f_equal; apply/eq_in_map=>x; rewrite mem_filter=> /andP /= [].
case: ifP=>// /eqP -> H1 H2.
by case: H; [rewrite H2|move:H1=>/[swap]->].
Qed.

(** ** Meaning of CSL judgments *)

(** First, we define configuration safety (cf. Definitions 3 and 4 in paper).
Intuitively, any configuration is safe for zero steps. For n + 1 steps, it better
(i) satisfy the postcondition if it is a terminal configuration, (ii) not abort,
(iii) access memory only inside its footprint, and
(iv) after any step it does, re-establish the resource invariant and be safe for
another n steps.  *)

Fixpoint safe (n : nat) (c: cmd) (s: stack) (h: heap) (gamma : rname -> option assn) (q: assn) :=
  match n with O => True
    | S n =>
(* Condition (i) END *)
          (c = Cskip -> sat (s, h) q)
(* Condition (ii) NAB *)
       /\ (forall hF (D: hdef h hF) (ABORT: aborts c (s, hplus h hF)), False)
(* Condition (iii) AOK *)
       /\ (forall a (ACC: a \in (accesses c s)), h a <> None)
(* Condition (iv) SOK *)
       /\ (forall hJ hF c' ss'
             (STEP: red c (s, hplus h (hplus hJ hF)) c' ss')
             (SAT: sat (s, hJ) (envs gamma (locked c') (locked c)))
             (D1: hdef h hJ)
             (D2: hdef h hF)
             (D3: hdef hJ hF),
             exists h' hJ',
                     ss'.2 = hplus h' (hplus hJ' hF)
                  /\ hdef h' hJ'
                  /\ hdef h' hF
                  /\ hdef hJ' hF
                  /\ sat (ss'.1, hJ') (envs gamma (locked c) (locked c'))
                  /\ safe n c' ss'.1 h' gamma q)
  end.

(** Now, the meaning of triples (cf. Definitions 2 and 5 in paper) *)

Definition CSL gamma p c q :=
  user_cmd c /\ forall n s h, sat (s, h) p -> safe n c s h gamma q.

(** ** Free variables and substitutions *)

(** The free variables of an assertion [p] are given as a predicate
[fvA p]. *)

Fixpoint fvA p :=
  match p with
    | Aemp                  => fun => False
    | Apure B               => fun v => v \in fvB B
    | Apointsto e1 e2       => fun v => v \in fvE e1 ++ fvE e2
    | Anot P                => fvA P
    | Astar P Q | Awand P Q
    | Aconj P Q | Adisj P Q => fun v => fvA P v \/ fvA Q v
    | Aex P                 => fun v => exists x, fvA (P x) v
  end.

Definition fvAs gamma v := exists x : rname, fvA (assn_lift (gamma x)) v.

(** Substitution of an expression for a free variable in an assertion: *)

Fixpoint subA x e p :=
  match p with
    | Aemp            => Aemp
    | Apure B         => Apure (subB x e B)
    | Apointsto e1 e2 => Apointsto (subE x e e1) (subE x e e2)
    | Anot P          => Anot (subA x e P)
    | Astar P Q       => Astar (subA x e P) (subA x e Q)
    | Awand P Q       => Awand (subA x e P) (subA x e Q)
    | Aconj P Q       => Aconj (subA x e P) (subA x e Q)
    | Adisj P Q       => Adisj (subA x e P) (subA x e Q)
    | Aex PP          => Aex (fun n => subA x e (PP n))
  end.

Lemma fvA_istar :
  forall Ps v, fvA (Aistar Ps) v <-> (exists P, fvA P v /\ In P Ps).
Proof.
elim=>/=.
- by move=>?; split=>//; case=>? [].
move=>a ? IH v; split.
- case=>H.
  - by exists a; split=>//; left.
  by move: ((IH v).1 H); case=>x [??]; exists x; split=>//; right.
case=>x [H]; case.
- by move=>->; left.
move=>?; right.
by apply/((IH v).2); exists x; split.
Qed.

Lemma subA_assign:
  forall x e p s h, sat (s,h) (subA x e p) <-> sat (upd s x (edenot e s), h) p.
Proof.
move=>??; elim=>? //=.
- by move=>??; rewrite subB_assign.
- by move=>H1 ? H2 ??; rewrite H1 H2.
- by move=>H1 ? H2 ??; rewrite H1 H2.
- by move=>H1 ? H2 ??; do 2![apply/ex_iff=>?]; rewrite H1 H2.
- by move=>H1 ? H2 ??; apply/all_iff=>?; rewrite H1 H2.
- by move=>H ??; rewrite H.
- by move=>???; rewrite !subE_assign.
by move=>H ??; apply/ex_iff=>?; rewrite H.
Qed.

(** * Soundness proof *)

(** ** Basic properties of the semantics *)

(** 1. Assertions depend only on the values of their free variables. *)

Lemma prop1_A: forall p s s' (A: forall v (FV: fvA p v), s v = s' v) h,
  sat (s, h) p <-> sat (s', h) p.
Proof.
elim=>//=.
- by move=>?? s' H ?; rewrite (prop1_B (s':=s')).
- move=>? H1 ? H2 ?? H ?.
  by rewrite (H1 _ _ (fun v => H v \o (@or_introl _ _))) (H2 _ _ (fun v => H v \o (@or_intror _ _))).
- move=>? H1 ? H2 ?? H ?.
  by rewrite (H1 _ _ (fun v => H v \o (@or_introl _ _))) (H2 _ _ (fun v => H v \o (@or_intror _ _))).
- move=>? H1 ? H2 ?? H ?; do 2![apply/ex_iff=>?].
  by rewrite (H1 _ _ (fun v => H v \o (@or_introl _ _))) (H2 _ _ (fun v => H v \o (@or_intror _ _))).
- move=>? H1 ? H2 ?? H ?; apply/all_iff=>?.
  by rewrite (H1 _ _ (fun v => H v \o (@or_introl _ _))) (H2 _ _ (fun v => H v \o (@or_intror _ _))).
- by move=>? H1 ?? H ?; rewrite (H1 _ _ H).
- by move=>???? H ?; rewrite (prop1_E (agrees_app1 H)) (prop1_E (agrees_app2 H)).
by move=>? H1 ?? H ?; apply/ex_iff=>x; rewrite H1; last by move=>??; apply/H; exists x.
Qed.

Lemma prop1_As :
  forall J s s' (A: forall v (FV: fvAs J v), s v = s' v) h l1 l2,
    sat (s, h) (envs J l1 l2) <-> sat (s', h) (envs J l1 l2).
Proof.
rewrite /envs=>??? H ???; apply/prop1_A=>? H2.
apply/H; move: H2; rewrite fvA_istar; case=>? [H2 /in_map_iff [x [H3 _]]].
by exists x; rewrite H3.
Qed.

Corollary prop1_AsE :
  forall s h J l1 l2 s'
    (SAT: sat (s, h) (envs J l1 l2))
    (A: forall v (FV: fvAs J v), s v = s' v),
  sat (s',h) (envs J l1 l2).
Proof.
by move=>??????? H2; rewrite -prop1_As; last by apply: H2.
Qed.

Corollary prop1_A2 :
  forall x P (NIN: ~ fvA P x) s v h, sat (upd s x v, h) P <-> sat (s, h) P.
Proof. by move=>??????; apply/prop1_A=>?; rewrite /upd; case: eqP=>// ->. Qed.

Corollary prop1_As2 :
  forall x J (NIN: ~ fvAs J x) s v h l l',
  sat (upd s x v, h) (envs J l l') <-> sat (s, h) (envs J l l').
Proof. by move=>????????; apply/prop1_As=>?; rewrite /upd; case: eqP=>// ->. Qed.

(** 2. Safety is monotone with respect to the step number (Proposition 3 in paper). *)

Lemma safe_mon :
  forall n C s h J Q (OK: safe n C s h J Q) m (LEQ: m <= n),
    safe m C s h J Q.
Proof.
move=>n C s h ?? H m; elim: m C s n h H=>// m IH ?? n ?; case: n=>// n; rewrite ltnS=>H Hl.
rewrite /= in H *; move: H; do![case=>?]; move=>H; do!split=>//; move=>???? STEP SAT D1 D2 D3.
move: (H _ _ _ _ STEP SAT D1 D2 D3); move=>[hJ1][hF1]; do!(case=>?); move=>?; exists hJ1, hF1; do!split=>//.
by apply/IH; last by apply: Hl.
Qed.

(** 3. Safety depends only on the values of the free variables of the program, the
postcondition and the resource invariants (Proposition 4 in the paper). To establish
this property, we need the following auxiliary lemmas.
*)

Lemma agrees_upd :
  forall A s s' y (EQs: s y = s' y) x x' (EQx: x = x') v v' (EQv: v = v'),
    upd (A:=A) s x v' y = upd s' x' v' y.
Proof. by rewrite /upd=> ???? -> ?? ->. Qed.

Lemma red_agrees :
  forall c ss c' ss' (STEP: red c ss c' ss')
    X s (A: forall x, X x -> ss.1 x = s x)
        (S_FV: forall x, x \in (fvC c) -> X x),
    exists s' h', red c (s, ss.2) c' (s', h')
      /\ (forall x, X x -> ss'.1 x = s' x) /\ ss'.2 = h'.
Proof.
move=>????; elim=>//=.
  (* red_Seq1 *)
- by move=>? [? h] ? s ??; exists s, h; do!split=>//; constructor.
  (* red_Seq2 *)
- move=>?????? H ?? H2 H3.
  case: (H _ _ H2); first by move=>??; apply/H3; rewrite mem_cat; apply/orP; left.
  by move=>s1[h1][?][?]?; exists s1, h1; do!split=>//; constructor.
  (* red_If1 *)
- move=>??? [a h] /= ?? s H H2; exists s, h; do!split=>//; constructor=>/=.
  by rewrite (prop1_B (s':=a)) //; apply/agreesC=>??; apply/H/H2; rewrite mem_cat; apply/orP; left.
  (* red_If2 *)
- move=>??? [a h] /= ?? s H H2; exists s, h; do!split=>//; constructor=>/=.
  by rewrite (prop1_B (s':=a)) //; apply/agreesC=>??; apply/H/H2; rewrite mem_cat; apply/orP; left.
  (* red_Par1 *)
- move=>?????? H ??? H2 H3.
  case: (H _ _ H2); first by move=>??; apply/H3; rewrite mem_cat; apply/orP; left.
  by move=>s1[h1][?][?]?; exists s1, h1; do!split=>//; constructor.
  (* red_Par2 *)
- move=>?????? H ??? H2 H3.
  case: (H _ _ H2); first by move=>??; apply/H3; rewrite mem_cat; apply/orP; right.
  by move=>s1[h1][?][?]?; exists s1, h1; do!split=>//; constructor.
  (* red_Par3 *)
- by move=>[? h] ? s ??; exists s, h; do!split=>//; constructor.
  (* red_Loop *)
- by move=>?? [? h] ? s ??; exists s, h; do!split=>//; constructor.
  (* red_Res1 *)
- move=>?????? H ?? H2 H3.
  by case: (H _ _ H2 H3)=>s1[h1][?][?]?; exists s1, h1; do!split=>//; constructor.
  (* red_Res2 *)
- by move=>? [? h] ? s ??; exists s, h; do!split=>//; constructor.
  (* red_With1 *)
- move=>??? [a h] /= ?? s H H2; exists s, h; do!split=>//; constructor=>/=.
  by rewrite (prop1_B (s':=a)) //; apply/agreesC=>??; apply/H/H2; rewrite mem_cat; apply/orP; left.
  (* red_With2 *)
- move=>?????? H ??? H2 H3.
  by case: (H _ _ H2 H3)=>s1[h1][?][?]?; exists s1, h1; do!split=>//; constructor.
  (* red_With3 *)
- by move=>? [? h] ? s ??; exists s, h; do!split=>//; constructor.
  (* red_Assign *)
- move=>x e ?? s0 h ->-> ? s /= H1 H2; exists (upd s x (edenot e s)), h; do!split=>//=; first by apply: red_Assign.
  move=>??; rewrite (prop1_E (s':=s)); first by rewrite /upd; case: eqP=>//; rewrite H1.
  by apply/(agrees_tl (X:=x))=>??; apply/H1/H2.
  (* red_Read *)
- move=>x ??? s0 h v -> H -> ? s /= H1 H2; exists (upd s x v), h; do!split=>//.
  - by apply: red_Read=>//; rewrite -H (prop1_E (s':=s)) //; apply/(agrees_tl (X:=x))=>??; apply/H1/H2.
  by move=>??; rewrite /upd; case: eqP =>//; rewrite H1.
  (* red_Write *)
- move=>e1 e2 ?? s0 h ->-> ? s /= H1 H2; exists s, (upd h (edenot e1 s) (Some (edenot e2 s))); do!split=>//; first by apply: red_Write.
  by rewrite !(prop1_E (s':=s)) // =>??; apply/H1/H2; rewrite mem_cat; apply/orP; [right|left].
  (* red_Alloc *)
- move=>x e ?? s0 h v -> H -> ? s /= H1 H2; exists (upd s x v), (upd h v (Some (edenot e s))); do!split=>//; first by apply: red_Alloc=>//.
  - by move=>y Hy; rewrite /upd; case: eqP=>//; rewrite H1.
  by rewrite (prop1_E (s':=s)) //; apply/(agrees_tl (X:=x))=>??; apply/H1/H2.
(* red_Free *)
move=>e ?? s0 h ->-> ? s /= H1 H2; exists s, (upd h (edenot e s) None); do!split=>//; first by apply: red_Free.
by rewrite (prop1_E (s':=s)) // =>??; apply/H1/H2.
Qed.

Lemma aborts_agrees :
  forall c ss (ABORT: aborts c ss)
    s' (A: agrees (fvC c) ss.1 s') h' (EQ: ss.2 = h'),
    aborts c (s', h').
Proof.
move=>??; elim=>/=.
(* aborts_Seq *)
- by move=>???? H1 ? H2 ??; constructor; apply/H1=>//; apply/(agrees_app1 H2).
(* aborts_Par1 *)
- by move=>???? H1 ? H2 ??; constructor; apply/H1=>//; apply/(agrees_app1 H2).
(* aborts_Par2 *)
- by move=>???? H1 ? H2 ??; constructor; apply/H1=>//; apply/(agrees_app2 H2).
(* aborts_Race1 *)
- move=>?? ss ?? H ??; apply: aborts_Race1=>/=.
  by rewrite (accesses_agrees (s':=ss.1)) ?(writes_agrees (s':=ss.1)) //;
  apply/agreesC; [apply/(agrees_app2 H)|apply/(agrees_app1 H)].
(* aborts_Race2 *)
- move=>?? ss ?? H ??; apply: aborts_Race2=>/=.
  by rewrite (accesses_agrees (s':=ss.1)) ?(writes_agrees (s':=ss.1)) //;
  apply/agreesC; [apply/(agrees_app1 H)|apply/(agrees_app2 H)].
(* aborts_Res *)
- by move=>???? H1 ? H2 ??; constructor; apply/H1=>//; apply/(agrees_app1 H2).
(* aborts_Atom *)
- by move=>???? H1 ? H2 ??; constructor; apply/H1=>//; apply/(agrees_app1 H2).
(* aborts_Read *)
- by move=>?? ss ?? H ? <-; apply: aborts_Read=>/=; rewrite (prop1_E (s':=ss.1)) //; apply/agreesC/(agrees_tl H).
(* aborts_Write *)
- by move=>?? ss ?? H2 ? <-; constructor=>/=; rewrite (prop1_E (s':=ss.1)) //; apply/agreesC/(agrees_app1 H2).
(* aborts_Free *)
by move=>? ss ???? <-; constructor=>/=; rewrite (prop1_E (s':=ss.1)) //; apply/agreesC.
Qed.

(** With these lemmas, we can show Proposition 4. *)

Lemma safe_agrees :
  forall n C s h J Q (OK: safe n C s h J Q) s'
    (A: forall v, v \in fvC C \/ fvA Q v \/ fvAs J v -> s v = s' v),
    safe n C s' h J Q.
Proof.
elim=>// n IH ????? /= [H1][H2][H3]H4 s1 H; do!split.
- by move/H1=>?; apply/prop1_A; first by move=>??; apply/esym/H; right; left.
- by move=>?? H0; apply/H2=>//; apply/(aborts_agrees H0) =>//= ??; apply/esym/H; left.
- by move=>a Ha; apply/H3; rewrite (accesses_agrees (s':=s1)) // /agrees =>??; apply/H; left.
move=>???? Hr Hs Hd1 Hd2 Hd3; move: (prop2 Hr)=>[M1][M2][M3]M.
exploit (red_agrees Hr).
- by move=>? Hx /=; apply/esym/H; exact: Hx.
- by move=>?? /=; left.
move=>[s0][h0][Hr2][H5]EQ; rewrite -{}EQ /= in Hr2.
exploit (H4 _ _ _ _ Hr2)=>//.
- by apply/prop1_As; first by move=>??; apply/H; right; right.
move=>[h2][hJ2]; do!(case=>/= ?); move=>b; exists h2, hJ2; do!split=>//.
- by apply/prop1_As; first by move=>??; apply/H5; right; right.
apply/IH; first by exact: b.
by move=>? Hx; apply/esym/H5; case: Hx; [move/(M1 _); left | right].
Qed.


(* -------------------------------------------------------------------------- *)
(** ** Soundness of the proof rules *)
(* -------------------------------------------------------------------------- *)

(** We now show the soundness of each proof rule of CSL separately. *)

Definition disjoint A (X Y: A -> Prop) := forall x, X x -> Y x -> False.

Definition pr {A : eqType} (l: seq A) (x: A) : Prop := x \in l.

Lemma disjoint_conv :
  forall {A : eqType} (l1 l2 : seq A), disjoint (pr l1) (pr l2) -> Basic.disjoint l1 l2.
Proof.
by move=>??? H; apply/hasP; case=>x ??; apply/(H x).
Qed.

(** *** Skip *)

Lemma safe_skip :
  forall n s h J Q, sat (s,h) Q -> safe n Cskip s h J Q.
Proof.
elim=>//= *; do!split=>//.
- by move=>??; case EQ : _ _ /.
by move=>>; case EQ : _ _ _ _/.
Qed.
Hint Resolve safe_skip : core.

Theorem rule_skip J P : CSL J P Cskip P.
Proof.
by split=>// *; apply: safe_skip.
Qed.

(** *** Parallel composition *)

Lemma safe_par:
 forall n C1 s h1 J Q1 (OK1: safe n C1 s h1 J Q1)
   C2 h2 Q2 (OK2: safe n C2 s h2 J Q2)
   (WF: wf_cmd (Cpar C1 C2))
   (HD: hdef h1 h2)
   (FV1: disjoint (pr (fvC C1)) (pr (wrC C2)))
   (FV2: disjoint     (fvA Q1)  (pr (wrC C2)))
   (FV3: disjoint     (fvAs J)  (pr (wrC C2)))
   (FV4: disjoint (pr (fvC C2)) (pr (wrC C1)))
   (FV5: disjoint     (fvA Q2)  (pr (wrC C1)))
   (FV6: disjoint     (fvAs J)  (pr (wrC C1))),
  safe n (Cpar C1 C2) s (hplus h1 h2) J (Astar Q1 Q2).
Proof.
elim=>//= ? IH C1 s h1 ?? [S1][AB1][AC1] H1 C2 h2 ? [S2][AB2][AC2] H2 /and3P [???] HD FV1 FV2 FV3 FV4 FV5 FV6; do!split=>//.
- move=>hF; rewrite hdef_hplus hplusA; case=>?? HH.
  case: {-2}_ {-2}_ /HH (erefl (Cpar C1 C2)) (erefl (s, hplus h1 (hplus h2 hF)))=>//??? A; case=>E1 E2 EQ; rewrite ?E1 ?E2 EQ in A.
  (* No aborts *)
  - by apply/AB1; last by [exact:A]; rewrite hdef_hplus2.
  - by rewrite hplusAC in A; last by [apply/hdefC];
       apply/AB2; last by [exact:A]; rewrite hdef_hplus2; split=>//; apply/hdefC.
  (* No races *)
  - 1,2: apply/A/disjoint_conv=>/= x; rewrite /pr; case: (HD x)=>HN ??; [apply/AC1|apply/AC2]; try by [exact: HN].
    1-4: by [|apply/writes_accesses|apply/writes_accesses|].
- (* accesses *)
  move=>x; rewrite mem_cat=>/orP; case.
  - by move/AC1; rewrite /hplus; case: (h1 x).
  - by move/AC2; rewrite hplusC /hplus; last by [apply/hdefC]; case: (h2 x).
(* Step *)
move=>hJ hF c' ss'; rewrite !hdef_hplus hplusA=>ST HS[?]?[?]??.
case: {-2}_ {-2}_ {-1}_ {-1}_ /ST (erefl (Cpar C1 C2)) (erefl (s, hplus h1 (hplus h2 (hplus hJ hF)))) (erefl c') (erefl ss')=>//.
(* C1 does a step *)
- move=>????? A DI; case=>E1 E2 EQ E3 _; rewrite E1 EQ in A; rewrite E2 in DI.
  rewrite E3 /= E2 envs_app1 // in HS.
  rewrite (hplusAC hF) in A; last by apply/hdefC.
  exploit H1; first by [exact: A]; try by [|rewrite hdef_hplus2; split=>//; apply/hdefC].
  move=>[h'][hJ']; rewrite !hdef_hplus2; case=>[->][?][[??]][[??]][?]?.
  exists (hplus h' h2), hJ'; do!split=>//=.
  - by rewrite hplusA [hplus hJ' _]hplusAC //; apply/hdefC.
  - by rewrite hdef_hplus; split=>//; apply/hdefC.
  - by rewrite hdef_hplus; split=>//; apply/hdefC.
  - by rewrite E2 envs_app1.
  move: (prop2 A)=>[B1][B2][_] /= B3.
  apply/IH; rewrite ?E2 //; first last.
  - by move=>? Hx ?; apply/FV6; [exact: Hx|apply/B2].
  - by move=>? Hx ?; apply/FV5; [exact: Hx|apply/B2].
  - by move=>? Hx ?; apply/FV4; [exact: Hx|apply/B2].
  - by move=>??  Hx; apply/FV1; [apply/B1|exact: Hx].
  - by apply/and3P; split=>//; apply/red_wf_cmd; first by exact:A.
  apply/(safe_agrees (s:=s)); first by apply/safe_mon; last by exact: leqnSn.
  by move=>? Hv; apply/esym/B3; case: Hv; [|case] => [/FV4|/FV5|/FV6] /negP.
(* C2 does a step *)
- move=>????? A DI; case=>E1 E2 EQ E3 _; rewrite E2 EQ in A; rewrite E1 in DI.
  rewrite E3 /= E1 envs_app2 // in HS.
  rewrite (hplusAC (hplus hJ hF)) in A; last by apply/hdefC.
  rewrite (hplusAC hF) in A; last by apply/hdefC.
  exploit H2; first by [exact: A]; try by [|rewrite hdef_hplus2; split=>//; apply/hdefC].
  move=>[h'][hJ']; rewrite !hdef_hplus2; case=>[->][?][[??]][[??]][?]?.
  exists (hplus h1 h'), hJ'; do!split=>//=.
  - by rewrite hplusA [hplus hJ' _]hplusAC 1?hplusAC //; apply/hdefC.
  - by rewrite hdef_hplus; split=>//; apply/hdefC.
  - by rewrite hdef_hplus; split=>//; apply/hdefC.
  - by rewrite E1 envs_app2.
  move: (prop2 A)=>[B1][B2][_] /= B3.
  apply/IH; rewrite ?E1 //; first last.
  - by move=>??  Hx; apply/FV4; [apply/B1|exact: Hx].
  - by move=>? Hx ?; apply/FV3; [exact: Hx|apply/B2].
  - by move=>? Hx ?; apply/FV2; [exact: Hx|apply/B2].
  - by move=>? Hx ?; apply/FV1; [exact: Hx|apply/B2].
  - by apply/hdefC.
  - by apply/and3P; split=>//; apply/red_wf_cmd; first by exact: A.
  apply/(safe_agrees (s:=s)); first by apply/safe_mon; last by exact: leqnSn.
  by move=>? Hv; apply/esym/B3; case: Hv; [|case] => [/FV1|/FV2|/FV3] /negP.
(* Par skip skip *)
- move=>?; case=>EQ1 EQ2 -> EQ _; rewrite EQ /= in HS; rewrite -EQ1 -EQ2 in S1 S2 *.
  exists (hplus h1 h2), hJ; rewrite hplusA /=; do!split=>//.
  - by rewrite hdef_hplus.
  - by rewrite hdef_hplus.
  by apply/safe_skip=>/=; exists h1, h2; do!split=>//; [apply/S1|apply/S2].
Qed.

Theorem rule_par J P1 P2 C1 C2 Q1 Q2 :
  CSL J P1 C1 Q1 -> CSL J P2 C2 Q2 ->
  disjoint (pr (fvC C1)) (pr (wrC C2)) ->
  disjoint     (fvA Q1)  (pr (wrC C2)) ->
  disjoint     (fvAs J)  (pr (wrC C2)) ->
  disjoint (pr (fvC C2)) (pr (wrC C1)) ->
  disjoint     (fvA Q2)  (pr (wrC C1)) ->
  disjoint     (fvAs J)  (pr (wrC C1)) ->
  CSL J (Astar P1 P2) (Cpar C1 C2) (Astar Q1 Q2).
Proof.
rewrite /CSL; move=>[?]H1[?]H2 ??????; split=>/=; first by apply/andP.
move=>???[?][?][?][?][?]<-; apply/safe_par=>//=; [apply/H1|apply/H2|]=>//.
by apply/and3P; rewrite !user_cmd_locked //; do!split=>//; apply/user_cmd_wf.
Qed.

(** *** Resource declaration *)

Lemma safe_resource:
 forall n C s h J r R Q (OK: safe n C s h (upd J r (Some R)) Q) (WF: wf_cmd C)
   (DISJ: disjoint (fvA R) (pr (wrC C))),
     (forall hR (NIN: r \notin locked C) (HD: hdef h hR)
       (SAT_R: sat (s,hR) R),
       safe n (Cresource r C) s (hplus h hR) J (Astar Q R))
   /\ (r \in locked C -> safe n (Cresource r C) s h J (Astar Q R)).
Proof.
elim=>//= ? IH C s h ? r ?? [H1][H2][H3]H4 ? DJ; do!split=>//.
- move=>hF D AB.
  case: {-2}_ {-2}_ /AB (erefl (Cresource r C)) (erefl (s, hplus (hplus h hR) hF))=>// ??? A; case=>? E2 EQ; rewrite E2 EQ hplusA in A.
  by apply/H2; last by [exact:A]; move: D; rewrite hdef_hplus hdef_hplus2; case.
- by rewrite /hplus=>? /H3; case: (h _).
- move=>hJ hF c' ss' ST SAT HD1 HD2.
  case: {-2}_ {-2}_ {-1}_ {-2}_ /ST (erefl (Cresource r C)) (erefl (s, hplus (hplus h hR) (hplus hJ hF))) (erefl c') (erefl ss')=>//;
  rewrite remove_irr // in SAT *.
  (* normal step *)
  move=>??? c'' ? R; case=>EQ1 EQ2 EQ3 EQ4 EQ5 ?.
  rewrite EQ1 EQ2 EQ3 EQ5 hplusA /= in R *. rewrite EQ4 /= EQ1 in SAT.
  move: (prop2 R)=>/= [?][SU2][?]B.
  case/boolP: (r \in locked c'')=>RIN.
  - rewrite -(hplusA hR) in R.
    exploit H4; first by [exact:R].
    - rewrite (sat_envs_expand RIN) //=.
      - exists hR, hJ; do!split=>//.
        - by rewrite /upd eq_refl.
        - by rewrite envs_upd_irr //; left; rewrite /remove mem_filter RIN /= eq_refl.
        by move: HD1; rewrite hdef_hplus; case.
      by apply/disjoint_locked/red_wf_cmd; first by exact: R.
    - by move: HD1; rewrite hdef_hplus hdef_hplus2; case.
    - by move: HD2; rewrite hdef_hplus; case.
    - by move: HD2; rewrite !hdef_hplus; case.
    case=>HH1[HH2][?][?][?][?][SA] S.
    exploit IH; first by exact: S.
    - by apply/red_wf_cmd; first by exact: R.
    - by move=>? Hx ?; apply/DJ; [exact: Hx|apply/SU2].
    move=>[? FU]; rewrite envs_upd_irr in SA; last by left.
    by exists HH1, HH2; do!split=>//; [rewrite envs_removeAll_irr|apply/FU].
  rewrite (hplusAC hF) in R; last by move: HD1; rewrite hdef_hplus; case=>_ /hdefC.
  rewrite remove_irr // in SAT *.
  exploit H4; first by [exact:R].
  - by rewrite envs_upd_irr; last by left.
  - by move: HD1; rewrite hdef_hplus; case.
  - by move: HD2; rewrite hdef_hplus hdef_hplus2; case.
  - by move: HD1; rewrite hdef_hplus hdef_hplus2; case=>_ /hdefC.
  case=>HH1[HH2][a1][?][a2][a3][SA] S.
  exploit IH; first by exact: S.
  - by apply/red_wf_cmd; first by exact: R.
  - by move=>? Hx ?; apply/DJ; [exact: Hx|apply/SU2].
  move=>[FU ?]; rewrite envs_upd_irr in SA; last by left.
  rewrite (hplusAC hF) -1?hplusA in a1; last by move: a3; rewrite hdef_hplus2; case=>/hdefC.
  move: SAT_R; rewrite (prop1_A (s':=ss'.1)) => SAT_R.
  - exists (hplus HH1 hR), HH2; do!split=>//.
    - by move: a3; rewrite hdef_hplus hdef_hplus2; case=>/hdefC.
    - by move: a2; rewrite hdef_hplus hdef_hplus2; case; move: HD2; rewrite hdef_hplus; case.
    - by move: a3; rewrite hdef_hplus2; case.
    by apply/FU=>//; move: a2; rewrite hdef_hplus2; case.
  by move=>Hx; apply/esym/B; move/DJ: Hx => /idP.
(* exit *)
- move=>?? [? EQ] -> EQ2 ??; rewrite -EQ EQ2 /= in SAT *.
  exists (hplus h hR), hJ; do!split=>//=.
  by apply/safe_skip=>/=; exists h, hR; do!split=>//; apply/H1/esym.
- move=>hF D AB.
  case: {-2}_ {-2}_ /AB (erefl (Cresource r C)) (erefl (s, hplus h hF))=>// ??? A; case=>E1 E2 EQ; rewrite E2 EQ in A.
  by apply/H2; first by exact: D.
(* normal step *)
move=>hJ hF c' ss' R /= SAT ???.
case: {-2}_ {-2}_ {-1}_ {-2}_ /R (erefl (Cresource r C)) (erefl (s, hplus h (hplus hJ hF))) (erefl c') (erefl ss')=>//=.
- move=>??? c'' ? R; case=>EQ1 EQ2 EQ3 EQ4 EQ5; rewrite EQ1 EQ2 EQ3 EQ5 in R *; rewrite EQ4 /= EQ1 in SAT.
  move: (prop2 R)=>/= [?][SU2][?]?.
  rewrite envs_removeAll2 // in SAT.
  exploit (H4 _ _ _ _ R)=>//; first by rewrite envs_upd_irr; last by right.
  move=>[h'][hJ'][X0][HD1][?][HD3][X3]X4.
  exploit (IH _ _ _ _ _ _ _ X4).
  - by apply/red_wf_cmd; first by exact:R.
  - by move=>? Hx ?; apply/DJ; [exact:Hx|apply/SU2].
  move=>[Y Y0]; case/boolP: (r \in locked c'')=>RIN.
  - rewrite envs_upd_irr in X3; last by right.
    rewrite envs_removeAll2 //.
    by exists h', hJ'; do!split=>//; apply/Y0.
  rewrite envs_removeAll_irr; last by rewrite mem_filter /= eq_refl.
  move: X3; rewrite (sat_envs_expand (r:=r)) //; last by apply/disjoint_locked.
  rewrite envs_upd_irr; last by left; rewrite mem_filter /= eq_refl H.
  rewrite /upd /= eq_refl /=; case => [h1][h2][?][?][EQ']?.
  rewrite EQ' hplusA -hplusA in X0.
  rewrite EQ' in HD1 HD3.
  exists (hplus h' h1), h2; do!split=>//.
  - by move: HD1; rewrite hdef_hplus hdef_hplus2; case.
  - by move: HD3; rewrite !hdef_hplus; case.
  - by move: HD3; rewrite hdef_hplus; case.
  by apply/Y=>//; move: HD1; rewrite hdef_hplus2; case.
by move=>?? [? EQ]; rewrite -EQ /= in_nil in H.
Qed.

Theorem rule_resource J P R r C Q:
  CSL (upd J r (Some R)) P C Q ->
  disjoint (fvA R) (pr (wrC C)) ->
  CSL J (Astar P R) (Cresource r C) (Astar Q R).
Proof.
rewrite /CSL /=; case=>/[dup]/user_cmdD/andP [? /eqP LC]? B ?; do!split=>// ???[?][?][S1][?][?]<-.
exploit safe_resource; first by [apply/B; exact: S1]; move=>// [H _].
by apply/H=>//; rewrite LC.
Qed.

(** *** Frame rule *)

Lemma safe_frame:
 forall n C s h J Q
   (OK: safe n C s h J Q) hR
   (HD: hdef h hR) R
   (DISJ: disjoint (fvA R) (pr (wrC C)))
   (SAT_R: sat (s,hR) R),
 safe n C s (hplus h hR) J (Astar Q R).
Proof.
elim=>//= ? IH ?? h ?? [SQ][A][AC]OK hR ?? DJ SAT; do!split=>//.
- by move=>?; exists h, hR; do!split=>//; apply/SQ.
- move=>?; rewrite !hplusA=> HD AB; apply/A; last by exact:AB.
  by move: HD; rewrite hdef_hplus hdef_hplus2; case.
- move=>? Ha Hp; apply/AC; first by exact:Ha.
  by move: Hp; rewrite /hplus; case: (h _).
move=>? hF ?? ST ? D1 D2 ?.
rewrite hplusA (hplusAC hF) in ST; last by move: D1; rewrite hdef_hplus; case=>_ /hdefC.
exploit OK; first by [exact:ST]; try by done.
- by move: D1; rewrite hdef_hplus; case.
- by move: D2; rewrite hdef_hplus hdef_hplus2; case.
- by move: D1; rewrite hdef_hplus hdef_hplus2; case=>_ /hdefC.
move=>[h'][hJ'][?][?][A2][A3][?]?.
exists (hplus h' hR), hJ'; rewrite hplusA (hplusAC hF); last by move: A3; rewrite hdef_hplus2; case.
do!split=>//.
- by move: A3; rewrite hdef_hplus hdef_hplus2; case=>/hdefC.
- by move: A2; rewrite hdef_hplus hdef_hplus2; case; move: D2; rewrite hdef_hplus; case.
- by move: A3; rewrite hdef_hplus2; case.
move: (prop2 ST)=> [B1][B2][B3] /= B4.
apply/IH=>//.
- by move: A2; rewrite hdef_hplus2; case.
- by move=>? Hx ?; apply/DJ; [exact: Hx|apply/B2].
apply/prop1_A; last by exact: SAT.
by move=>? FV; apply/B4; move/DJ: FV =>/idP.
Qed.

Theorem rule_frame J P C Q R:
  CSL J P C Q -> disjoint (fvA R) (pr (wrC C)) ->
  CSL J (Astar P R) C (Astar Q R).
Proof.
rewrite /CSL; case=>? S ?; split=>//= ???[?][?][?][?][?]<-; apply/safe_frame=>//.
by apply: S.
Qed.

(** *** Conditional critical regions *)

Lemma safe_inwith:
  forall n C s h J Q r
    (OK : safe n C s h J (Astar Q (assn_lift (J r))))
    (WF: wf_cmd (Cinwith r C)),
  safe n (Cinwith r C) s h J Q.
Proof.
elim=>//= ? IH C s h ?? r [END][A2][?] SOK /andP [??]; do!split=>//.
- move=>hF ? AB.
  case: {-2}_ {-2}_ /AB (erefl (Cinwith r C)) (erefl (s, hplus h hF))=>// ??? A; case=>_ EQ2 EQ.
  by rewrite EQ2 EQ in A; apply/A2; last by exact:A.
- move=>hJ hF c' ss' ST SAT D1 D2 ?.
  case: {-2}_ {-2}_ {-1}_ {-2}_ /ST (erefl (Cinwith r C)) (erefl (s, hplus h (hplus hJ hF))) (erefl c') (erefl ss')=>//=.
  - move=>????? R NIN; case=>EQ1 EQ2 EQ EQC EQSS.
    rewrite EQSS EQ1 EQ2 EQ in R NIN *.
    exploit SOK; first by [exact:R]; try done.
    - by rewrite EQC EQ1 /= envs_cons2_irr in SAT.
    move=>[h'][hJ']; do![case=>?].
    exists h',hJ'; do!split=>//.
    - by rewrite envs_cons2_irr.
    by apply/IH=>//; apply/andP; split=>//; apply/red_wf_cmd; first by exact:R.
move=>??; case=>_ EQ2 EQ EQC _.
rewrite EQ /=; rewrite EQC /= in SAT.
exploit END; first by move/esym: EQ2.
move=>[h1][h2][?][?][?]HH; rewrite -HH in D1 D2 *.
exists h1, h2; rewrite SAT; do!split=>//.
- by rewrite hplusU hplusA.
- 1,2: by move: D2; rewrite hdef_hplus; case.
- by exists h2, hemp; do!split=>//; [rewrite -EQ2|apply: hdefU2|apply: hplusU2].
by apply/safe_skip.
Qed.

Theorem rule_with J P r B C Q:
  CSL J (Aconj (Astar P (assn_lift (J r))) (Apure B)) C (Astar Q (assn_lift (J r))) ->
  CSL J P (Cwith r B C) Q.
Proof.
rewrite /CSL; case=>U SA /=; split=>// n s h ?.
elim: n=>//= n ?; do!split=>//.
- move=>hF ? AB.
  by case: {-2}_ {-2}_ /AB (erefl (Cwith r B C)) (erefl (s, hplus h hF)).
move=>hJ hF c' ss' ST SAT D1 D2 D3.
case: {-2}_ {-2}_ {-1}_ {-2}_ /ST (erefl (Cwith r B C)) (erefl (s, hplus h (hplus hJ hF))) (erefl c') (erefl ss')=>//=.
move=>???? Bd; case=>EQ1 EQ2 EQ3 EQSS EQC ?; move: SAT. rewrite EQC EQ1 EQ3 EQSS /= (user_cmd_locked U) /=.
case=>h1[?][?][->][?] EQJ; move: D1 D3; rewrite -EQJ hdef_hplus hdef_hplus2; case=>??[??].
exists (hplus h h1), hemp; rewrite !hplusA; do!split=>//.
- 1,2: by rewrite hdef_hplus.
apply/safe_inwith=>/=.
- apply/SA=>/=; rewrite EQ2 EQSS /= in Bd; split=>//.
  by exists h, h1.
by move: (user_cmd_wf U); rewrite (user_cmd_locked U) andbC.
Qed.

(** *** Sequential composition *)

Lemma safe_seq :
  forall n C s h J Q (OK : safe n C s h J Q) C2 (U: user_cmd C2) R
    (NEXT: forall m s' h', m <= n -> sat (s', h') Q -> safe m C2 s' h' J R),
  safe n (Cseq C C2) s h J R.
Proof.
elim=>//= ? IH C s h ??[A1][A2][?] SOK C2 U2 ? NX; do!split=>//.
- move=>hF ? AB.
  case: {-2}_ {-2}_ /AB (erefl (Cseq C C2)) (erefl (s, hplus h hF))=>// ??? A; case=>EQ1 EQ2 EQ.
  by rewrite EQ1 EQ in A; apply/A2; last by exact:A.
move=>hJ hF c' ss' ST SAT ???.
case: {-2}_ {-2}_ {-1}_ {-2}_ /ST (erefl (Cseq C C2)) (erefl (s, hplus h (hplus hJ hF))) (erefl c') (erefl ss')=>//=.
- move=>??; case=>EQ1 EQ2 EQ3 EQ4 ?; rewrite EQ3 EQ2 /=.
  exists h, hJ; do!split=>//.
  - by move: SAT; rewrite EQ4 -EQ1 EQ2 (user_cmd_locked U2).
  by apply/NX=>//; apply/A1/esym.
move=>????? ST; case=>EQ1 EQ2 EQ EQC EQSS; rewrite EQ1 EQ EQSS EQ2 in ST *; rewrite EQC /= in SAT.
exploit SOK; first by [exact:ST]; try done.
case=>h1[h2][->][?][?][?][?] S.
exists h1,h2; do!split=>//; apply/IH=>//; first by exact: S.
by move=>?????; apply/NX=>//; apply/leqW.
Qed.

Theorem rule_seq J P C1 Q C2 R :
  CSL J P C1 Q -> CSL J Q C2 R -> CSL J P (Cseq C1 C2) R.
Proof.
rewrite /CSL; case=>? S1 [?]S2 /=; do!split; first by apply/andP.
move=>????; apply/safe_seq=>//; first by apply: S1.
by move=>?????; apply: S2.
Qed.

(** *** Conditionals (if-then-else) *)

Theorem rule_if J P B C1 C2 Q:
  CSL J (Aconj P (Apure B)) C1 Q ->
  CSL J (Aconj P (Apure (Bnot B))) C2 Q ->
  CSL J P (Cif B C1 C2) Q.
Proof.
rewrite /CSL; case=>U1 S1[U2]S2 /=; do!split; first by apply/andP.
move=>n s h ?; elim: n=>//= ??; do!split=>//.
- move=>hF ? AB.
  by case: {-2}_ {-2}_ / AB (erefl (Cif B C1 C2)) (erefl (s, hplus h hF)).
move=>hJ hF c' ss' ST SAT ???.
case: {-2}_ {-2}_ {-1}_ {-2}_ /ST (erefl (Cif B C1 C2)) (erefl (s, hplus h (hplus hJ hF))) (erefl c') (erefl ss')=>//=;
move=>???? BD; case=>EQ1 EQ2 EQ3 EQ EQC _.
- rewrite EQ EQ2 /=; rewrite EQ1 EQ /= in BD; rewrite EQC EQ2 (user_cmd_locked U1) /= in SAT.
  by exists h, hJ; do!split=>//; apply/S1.
rewrite EQ EQ3 /=; rewrite EQ1 EQ /= in BD; rewrite EQC EQ3 (user_cmd_locked U2) /= in SAT.
exists h, hJ; do!split=>//.
by apply/S2=>/=; rewrite BD.
Qed.

(** *** While *)

Lemma safe_while:
  forall J P B C (OK: CSL J (Aconj P (Apure B)) C P) s h (SAT_P: sat (s, h) P) n,
    safe n (Cwhile B C) s h J (Aconj P (Apure (Bnot B))).
Proof.
move=>?? B C [UC SC] +++ n; move: n {1 3}n (leqnn n).
elim=>// n IH m leq; first by case: n IH.
move=>s h ?; case: m leq=>// m; rewrite ltnS=>leq /=.
do!split=>//.
- move=>hF ? AB.
  by case: {-2}_ {-2}_ / AB (erefl (Cwhile B C)) (erefl (s, hplus h hF)).
move=>hJ hF c' ss' ST SAT ???.
case: {-2}_ {-2}_ {-1}_ {-2}_ /ST (erefl (Cwhile B C)) (erefl (s, hplus h (hplus hJ hF))) (erefl c') (erefl ss')=>//.
move=>???; case=>EQ1 EQ2 EQ EQC EQSS.
rewrite EQ EQ1 EQ2 /=; rewrite EQC /= in SAT.
exists h, hJ; do!split=>//.
case: m leq=>//= m le; do!split=>//.
- move=>hF0 ? AB.
  by case: {-2}_ {-2}_ / AB (erefl (Cif B (Cseq C (Cwhile B C)) Cskip)).
move=>hJ0 hF0 c0' ss0' ST0 SAT0 ???.
case: {-2}_ {-2}_ {-1}_ {-2}_ /ST0 (erefl (Cif B (Cseq C (Cwhile B C)) Cskip)) (erefl (s, hplus h (hplus hJ0 hF0))) (erefl c0') (erefl ss0')=>//;
move=>???? B0; case=>EQ01 EQ02 EQ03 EQ0 EQ0C EQ0SS; rewrite EQ0 /=; rewrite EQ01 EQ0 /= in B0;
exists h, hJ0; do!split=>//.
- by move: SAT0; rewrite EQ0C EQ02 /= user_cmd_locked.
- rewrite EQ02; apply/safe_seq=>//=; first by apply/SC=>/=; split.
  by move=>??? leq0 ?; apply/IH=>//; apply/(leq_trans leq0); apply/ltnW.
- by rewrite EQ0C EQ03 /= in SAT0.
by rewrite EQ03; apply/safe_skip=>/=; split=>//; rewrite B0.
Qed.

Theorem rule_while J P B C :
  CSL J (Aconj P (Apure B)) C P ->
  CSL J P (Cwhile B C) (Aconj P (Apure (Bnot B))).
Proof.
rewrite /CSL /=; case=>??; split=>// ????.
by apply/safe_while.
Qed.

(** *** Basic commands (Assign, Read, Write, Alloc, Free) *)

Theorem rule_assign J x E Q:
  ~ fvAs J x -> CSL J (subA x E Q) (Cassign x E) Q.
Proof.
rewrite /CSL=>?; split=>// n s h ?; elim: n=>// n IH /=; do!split=>//.
- move=>hF0 ? AB.
  by case: {-2}_ {-2}_ / AB (erefl (Cassign x E)).
move=>hJ hF c' ss' ST SAT ??.
case: {-2}_ {-2}_ {-1}_ {-2}_ /ST (erefl (Cassign x E)) (erefl (s, hplus h (hplus hJ hF))) (erefl c') (erefl ss')=>//.
move=>?????? EQ01 EQ02; case=>EQ1 EQ2 EQ EQC EQSS ?.
rewrite EQC /= in SAT; rewrite EQ01 in EQ; case: EQ=>EQS EQH; rewrite EQ02 /= EQH SAT.
exists h, hemp; do!split=>//.
- by apply: hdefU2.
- by apply: hdefU.
by rewrite EQS EQ1 EQ2; apply safe_skip; rewrite -subA_assign.
Qed.

Theorem rule_read J x E E' :
  x \notin fvE E ->
  x \notin fvE E' ->
  ~ fvAs J x ->
  CSL J (Apointsto E E') (Cread x E) (Aconj (Apointsto E E') (Apure (Beq (Evar x) E'))).
Proof.
move=>???; rewrite /CSL; split=>//= n s h EQH; elim: n=>// n IH /=; do!split=>//.
- move=>hF ? AB.
  case: {-2}_ {-2}_ / AB (erefl (Cread x E)) (erefl (s, hplus h hF)) =>//.
  by move=>??? NIN; case=>_ EQ2; rewrite EQH; move: NIN=>/[swap]-> /=; rewrite /hplus /singl EQ2 eq_refl.
- by move=>?; rewrite EQH /singl mem_seq1 =>/eqP ->; rewrite eq_refl.
move=>hJ hF c' ss' ST SAT ???.
case: {-2}_ {-2}_ {-1}_ {-2}_ /ST (erefl (Cread x E)) (erefl (s, hplus h (hplus hJ hF))) (erefl c') (erefl ss')=>//.
move=>??????? EQ01 RD EQ02; case=>EQ1 EQ2 EQ EQC EQSS.
rewrite EQ01 in EQ; case: EQ=>EQS0 EQH0; rewrite EQ02 EQH0 /=; rewrite EQC /= in SAT.
exists h, hJ; do!split=>//.
apply/safe_skip; rewrite EQH EQS0 EQ1 /= !prop1_E2 //; split=>//.
by rewrite EQH0 SAT EQ2 EQS0 /hplus EQH /singl eq_refl in RD; case: RD=><-; rewrite /upd !eq_refl.
Qed.

Theorem rule_write J E E0 E':
  CSL J (Apointsto E E0) (Cwrite E E') (Apointsto E E').
Proof.
rewrite /CSL; split=>//= n s h EQH; elim: n=>//= n IH; do!split=>//.
- move=>hF ? AB.
  case: {-2}_ {-2}_ / AB (erefl (Cwrite E E')) (erefl (s, hplus h hF)) =>//.
  move=>??? NIN; case=>EQ1 _; rewrite EQH; move: NIN=>/[swap]->/=.
  by rewrite EQ1 /hplus /singl eq_refl.
- by move=>?; rewrite EQH /singl mem_seq1=>/eqP->; rewrite eq_refl.
move=>hJ hF c' ss' ST SAT ? D2 ?.
case: {-2}_ {-2}_ {-1}_ {-2}_ /ST (erefl (Cwrite E E')) (erefl (s, hplus h (hplus hJ hF))) (erefl c') (erefl ss')=>//.
move=>???? s0 ? EQ0 EQ; case=>EQ1 EQ2 EQ00 EQC ?; rewrite EQ0 in EQ00; case: EQ00=>EQ01 EQ02.
rewrite EQC /= in SAT; rewrite EQ EQ1 EQ2 EQ02 SAT /=.
exists (singl (edenot E s0) (Some (edenot E' s0))), hemp; do!split=>//.
- by rewrite EQH EQ01 /singl /upd /hplus; apply/fext=>?; case: eqP.
- by apply/hdefU2.
- by move: D2; rewrite EQH EQ01; apply: hdef_upds.
- by apply/hdefU.
by apply/safe_skip.
Qed.

Theorem rule_alloc J x E:
  x \notin fvE E ->
  ~ fvAs J x ->
  CSL J Aemp (Calloc x E) (Apointsto (Evar x) E).
Proof.
move=>??; rewrite /CSL; split=>// n s h /= EQH; elim: n=>//= n IH; do!split=>//.
- move=>hF ? AB.
  by case: {-2}_ {-2}_ / AB (erefl (Calloc x E)).
move=>hJ hF c' ss' ST SAT ???.
case: {-2}_ {-2}_ {-1}_ {-2}_ /ST (erefl (Calloc x E)) (erefl (s, hplus h (hplus hJ hF))) (erefl c') (erefl ss')=>//.
move=>?????? v EQ0 NIN EQS; case=>EQ1 EQ2 EQ00 EQC ?.
rewrite EQC /= in SAT; rewrite {}EQ0 in EQ00; case: EQ00=>EQ01 EQ02; rewrite EQS EQ1 EQ2 EQ01 EQ02 EQH /=.
exists (singl v (Some (edenot E s))), hemp; do!split.
- by rewrite SAT /upd /singl /hplus; apply/fext=>?; case: eqP.
- by apply/hdefU2.
- by move: NIN; rewrite EQ02 EQH SAT !hplusU /hdef /singl => H ?; case: eqP; [move=>->; right|left].
- by apply/hdefU.
by apply/safe_skip=>/=; rewrite prop1_E2 // /upd eq_refl.
Qed.

Theorem rule_free J E E':
  CSL J (Apointsto E E') (Cdispose E) Aemp.
Proof.
rewrite /CSL; split=>// n s h /= EQH; elim: n=>//=n IH; do!split=>//.
- move=>hF ? AB.
  case: {-2}_ {-2}_ / AB (erefl (Cdispose E)) (erefl (s, hplus h hF))=>//.
  by move=>?? NIN; case=>EQ EQS; move: NIN; rewrite EQ EQS EQH /= /hplus /singl eq_refl.
- by move=>?; rewrite EQH /singl mem_seq1=>/eqP->; rewrite eq_refl.
move=>hJ hF c' ss' ST SAT ? D2 ?.
case: {-2}_ {-2}_ {-1}_ {-2}_ /ST (erefl (Cdispose E)) (erefl (s, hplus h (hplus hJ hF))) (erefl c') (erefl ss')=>//.
move=>????? EQ0 EQS0; case=>EQ1 EQ EQC ?; rewrite EQ0 in EQ; case: EQ=>EQ01 EQ02.
rewrite EQC /= in SAT; rewrite EQS0 EQ1 EQ01 EQ02 EQH SAT /=.
exists hemp, hemp; do!split; try by apply/hdefU.
- rewrite EQH /hdef in D2; case: (D2 (edenot E s)); rewrite /upd /singl /hplus =>HD; apply/fext=>?; case: eqP=>//.
  - by rewrite eq_refl in HD.
  by move=>->; rewrite HD.
by apply/safe_skip.
Qed.

(** *** Simple structural rules (Conseq, Disj, Ex) *)

Notation "P '|=' Q" := (forall x, sat x P -> sat x Q)  (at level 100).

Lemma safe_conseq:
  forall n C s h J Q (OK: safe n C s h J Q) Q' (IMP: Q |= Q'),
  safe n C s h J Q'.
Proof.
elim=>//= ? IH ?????[A][?][?]SOK ? IMP; do!split=>//; first by move/A/IMP.
move=>???? ST ????; exploit SOK; first by [exact:ST]; try done.
case=>h'[hJ'][->][?][?][?][?]S.
exists h', hJ'; do!split=>//.
by apply/IH; first by exact: S.
Qed.

Theorem rule_conseq J P C Q P' Q':
  CSL J P C Q ->
  (P' |= P) ->
  (Q |= Q') ->
  CSL J P' C Q'.
Proof.
rewrite /CSL; case=>? IH HP HQ; split=>// ????.
apply/safe_conseq; last by exact: HQ.
by apply/IH/HP.
Qed.

Theorem rule_disj J P1 P2 C Q1 Q2:
  CSL J P1 C Q1 ->
  CSL J P2 C Q2 ->
  CSL J (Adisj P1 P2) C (Adisj Q1 Q2).
Proof.
rewrite /CSL; case=>? H1 [_]H2; split=>//= ???.
by case=>H; apply/safe_conseq=>/=; [apply/H1|left|apply/H2|right].
Qed.

Theorem rule_ex J P C Q:
  (forall x, CSL J (P x) C (Q x)) ->
  CSL J (Aex P) C (Aex Q).
Proof.
rewrite /CSL=>H; split; first by move: (H 0)=>[].
move=>??? /= [v Sv]; apply/safe_conseq; first by move/snd: (H v); apply.
by move=>?? /=; exists v.
Qed.

(** *** Conjunction rule *)

Lemma safe_conj:
  forall n C s h J Q1 (OK1: safe n C s h J Q1)
     Q2 (OK2: safe n C s h J Q2)
        (PREC: forall r, precise (assn_lift (J r))),
  safe n C s h J (Aconj Q1 Q2).
Proof.
elim=>//= ? IH C ?? J ? [S1][AB][A]OK1 ? [S2][_][_]OK2 PREC; do!split=>//.
- by apply/S1.
- by apply/S2.
move=>?? c' ss' ST SAT D1 D2 D3.
case: (OK1 _ _ _ _ ST SAT D1 D2 D3)=>h0[hJ0][SS0][?][?][?][?]?.
case: (OK2 _ _ _ _ ST SAT D1 D2 D3)=>h1[hJ1][SS1][?][?][?][?]?.
have P : precise (envs J (locked C) (locked c'))
  by apply/precise_istar=>? /in_map_iff /= [?][<-]?; apply/PREC.
rewrite SS0 in SS1.
have EQ01 : hJ0 = hJ1.
- rewrite hplusAC in SS1; last by apply/hdefC.
  rewrite [hplus _ (hplus hJ1 _)]hplusAC in SS1; last by apply/hdefC.
  by apply/(P _ _ _ _ ss'.1); try by [exact: SS1]; try by [done];
  rewrite hdef_hplus2; split=>//; apply/hdefC.
have EQ02 : h0 = h1
  by rewrite EQ01 in SS1; apply/hplusKr; first by [exact: SS1]; rewrite hdef_hplus2; split=>//; rewrite -EQ01.
rewrite SS0; exists h0, hJ0; do!split=>//.
by apply/IH=>//; rewrite EQ02.
Qed.

Theorem rule_conj J P1 P2 C Q1 Q2:
  CSL J P1 C Q1 ->
  CSL J P2 C Q2 ->
  (forall r, precise (assn_lift (J r))) ->
  CSL J (Aconj P1 P2) C (Aconj Q1 Q2).
Proof.
rewrite /CSL; case=>? S1 [_] S2 ?; split=>//= ???[??].
by apply/safe_conj=>//; [apply/S1|apply/S2].
Qed.
