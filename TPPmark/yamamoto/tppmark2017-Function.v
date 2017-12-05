(* TPPmark 2017 Function version by Mitsuharu Yamamoto *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Recdef.

Section LongestCommonSubsequence.

Definition argmax (X : Type) f (x y : X) := if f x < f y then y else x.

Lemma argmax_maxn (X : Type) f (x y : X) : f (argmax f x y) = maxn (f x) (f y).
Proof.  by rewrite /argmax fun_if.  Qed.

Variable T : eqType.

Function LCS p {measure (fun p => size p.1 + size p.2) p} : seq T :=
  if p is (x :: s, y :: t) then if x == y then x :: LCS (s, t)
                                else argmax size (LCS (s, p.2)) (LCS (p.1, t))
  else [::].
  - by move=> _ _ _ x s _ y t _ _ _; apply: ltP; rewrite addnS.
  - by move=> _ _ _ x s _ y t _ _ _; apply: ltP; rewrite addnS.
  - by move=> _ _ _ x s _ y t _ _ _; apply: ltP.
Defined.

Lemma lcs_subseq p : subseq (LCS p) p.1 /\ subseq (LCS p) p.2.
Proof.
  (* functional induction (LCS p) *)
  elim/LCS_ind: p / _; last by move=> ? ?; rewrite !sub0seq.
  - by move=> _ x s _ t _ /eqP <- /=; rewrite eqxx.
  - move=> [_ _] x s y t [-> ->] [] // _ _; rewrite /argmax.
    case: ifP => _ [H1 H2] [H3 H4]; split => // {H2 H3}.
    + by rewrite (subseq_trans H4) // subseq_cons.
    + by rewrite (subseq_trans H1) // subseq_cons.
Qed.

Lemma lcs_longest p u :
  subseq u p.1 -> subseq u p.2 -> size u <= size (LCS p).
Proof.
  rewrite [subseq]lock; elim/LCS_ind: p / _ u => /=.
  - move=> _ x s _ t _ /eqP <-; rewrite -lock => IH; case=> // z u Hs Ht.
    by move: (IH _ Hs Ht); case: ifP => _ // /leqW.
  - move=> [_ _] x s y t [-> ->] [] // Hxy _ /= IHs IHt.
    rewrite -lock in IHs IHt *; case=> // z u /=; rewrite argmax_maxn leq_max.
    case: ifP => [/eqP -> | Hzx] Hs.
    + by rewrite Hxy => Ht; rewrite (IHt (x :: u)) ?orbT //= eqxx.
    + by move=> Ht; rewrite (IHs (z :: u)).
  - move=> [s t] [_ _] [<- <-]; rewrite -lock.
    case: s => [|x s] /=; first by move=> _ _ /eqP ->.
    by case: t => [|y t] //= => _ _ _ /eqP ->.
Qed.

End LongestCommonSubsequence.

Require Program.

Section LongestCommonSubsequenceForList.

Fixpoint argmaxl (X : Type) f (x : X) ys :=
  if ys is y :: ys' then argmaxl f (if f x < f y then y else x) ys'
  else x.

Lemma argmaxl_sup (X : Type) f (x : X) ys m :
  (m <= f x) || has (fun y => m <= f y) ys -> m <= f (argmaxl f x ys).
Proof.
  elim: ys => [| y ys IHys] /= in x *; first by rewrite orbF.
  move=> H; case: ifP => Hxy.
  - by apply IHys; case/orP: H => // H; rewrite (ltnW (leq_ltn_trans H Hxy)).
  - apply IHys; rewrite orbCA in H; case/orP: H => // H.
    by rewrite (leq_trans H) // leqNgt Hxy.
Qed.

Lemma argmaxl_mem (X : eqType) f (x : X) ys :
  (argmaxl f x ys == x) || (argmaxl f x ys \in ys).
Proof.
  elim: ys => [| y ys IHys] in x *; first by rewrite eqxx.
  rewrite /=; case: ifP => H; first by rewrite inE (IHys y) orbT.
  move/predU1P: (IHys x) => [-> | H']; first by rewrite eqxx.
  by rewrite inE H' !orbT.
Qed.

Variable T : eqType.

Definition LCSL_spec s ts (lcsl : seq T) :=
  [/\ subseq lcsl s, all (subseq lcsl) ts &
      forall u, subseq u s -> all (subseq u) ts -> size u <= size lcsl].

Program Fixpoint LCSL_strong s ts {measure (size s + (\sum_(t <- ts) size t))}
  : {lcsl : seq T | LCSL_spec s ts lcsl} :=
  if s is x :: s' then
    let hds := map ohead ts in
    match None \in hds with
    | true => [::]
    | false =>
      if all (pred1 (Some x)) hds then
        x :: LCSL_strong s' (map behead ts)
      else
        argmaxl size (LCSL_strong s' ts)
                [tuple LCSL_strong s (set_nth [::] ts i
                                              (behead (nth [::] ts i)))
                | i < size ts]
    end
  else [::].
Next Obligation.
Proof.
  split=> //; first by apply/allP => *; rewrite sub0seq.
  move/esym/mapP: Heq_anonymous => [t].
  by case: t => // Ht _ u _ /allP /(_ [::]) /(_ Ht); rewrite subseq0 => /eqP ->.
Qed.
Next Obligation.
Proof.
  apply: ltP; rewrite /= -addSn leq_add // big_map leq_sum // => t.
  by rewrite size_behead leq_pred.
Qed.
Next Obligation.
Proof.
  apply: ltP; rewrite -addnS leq_add //; set ts' := set_nth _ _ _ _.
  have Hsize: size ts' = size ts by rewrite size_set_nth; apply/maxn_idPr.
  have Hts' i0 : i0 != i :> nat -> nth [::] ts' i0 = nth [::] ts i0
    by move=> Hi0; rewrite nth_set_nth /= (negPf Hi0).
  rewrite !(big_nth [::]) (@big_cat_nat _ _ _ i.+1) //= Hsize //.
  rewrite [X in _ < X](@big_cat_nat _ _ _ i.+1) //=.
  rewrite !big_nat_recr //= -addSn -addnS !big_nat !leq_add //.
  - apply: eq_leq; apply: eq_bigr => i0 Hi0; rewrite Hts' //.
    by apply/negP => /eqP Hi0i; rewrite Hi0i ltnn andbF in Hi0.
  - rewrite nth_set_nth /= eqxx size_behead prednK //.
    case E: nth => //; case/negP: (esym Heq_anonymous).
    by apply/mapP; exists [::] => //; apply/(nthP [::]); exists i.
  - apply: eq_leq; apply: eq_bigr => i0 Hi0; rewrite Hts' //.
    by apply/negP => /eqP Hi0i; rewrite Hi0i ltnn in Hi0.
Qed.
Next Obligation.
Proof.
  set lx := LCSL_strong _ _ _; set ls := LCSL_strong _ _ _.
  set lts' := [seq sval _ | _ <- _]; split.
  - case: ifP; first by rewrite /= eqxx; case: (svalP lx).
    move=> Hhds {lx}; move/predU1P: (argmaxl_mem size (sval ls) lts') => [-> |].
    + by case: (svalP ls) => H _ _; rewrite (subseq_trans H) ?subseq_cons.
    + by case/mapP => i Hi ->; set lt := LCSL_strong _ _ _; case: (svalP lt).
  - case: ifP => Hx.
    + apply/allP => t Ht; case: (svalP lx) => _ /allP /(_ (behead t)).
      rewrite map_f // => /(_ isT) Hbht _; case: t Ht Hbht => [Hnil | y t Hyt].
      * by case/negP: (esym Heq_anonymous); apply/mapP; exists [::].
      * move/allP/(_ (ohead (y :: t))): Hx.
        by rewrite map_f //= => /(_ isT) /eqP [] ->; rewrite eqxx.
    + move/predU1P: (argmaxl_mem size (sval ls) lts') => [-> |] {lx}.
      * by case: (svalP ls).
      * case/mapP => i Hi ->; set ts' := set_nth _ _ _ _.
        set lt' := LCSL_strong _ _ _.
        have Hts' : size ts' = size ts
          by rewrite size_set_nth; apply: maxn_idPr.
        apply/allP => _ /(nthP [::]) [j Hj <-].
        case: (svalP lt') => _ /allP /(_ (nth [::] ts' j)).
        rewrite mem_nth ?Hts' // nth_set_nth => /(_ isT) H _.
        rewrite /= in H; case: ifP H => // /eqP ->.
        case: (nth [::] ts i) => // y t /subseq_trans -> //.
        by rewrite subseq_cons.
  - case=> // z u Hzuxs' Hzuts; case: ifP => Hx.
    + case: (svalP lx) => _ _ /(_ _ Hzuxs'); case: ifP => [/eqP |] Hzx.
      * apply; apply/allP => _ /mapP [t Ht ->]; move/allP/(_ (ohead t)): Hx.
        rewrite map_f //= => /(_ isT) H; case: t H Ht => // _ t /eqP [] ->.
        by move/(allP Hzuts); rewrite Hzx /= eqxx.
      * move=> H; apply: ltnW; apply: H.
        apply/allP => _ /mapP [t Ht ->]; move/allP/(_ (ohead t)): Hx.
        rewrite map_f //= => /(_ isT) H; case: t H Ht => // _ t /eqP [] ->.
        by move/(allP Hzuts); rewrite /= Hzx.
    + apply: argmaxl_sup; move: Hzuxs' => /= {lx}.
      case: ifP => [/eqP {z}-> | Hzx] in Hzuts *.
      * { move=> Hus'; case/allPn: Hx => _ /mapP [t Ht ->] /=.
          case: t Ht => [Hnil | y t Hyt].
          - by case/negP: (esym Heq_anonymous); apply/mapP; exists [::].
          - rewrite /eq_op /= => Hyx; case/(nthP [::]): (Hyt) => i Hi Hnthi.
            apply/orP; right; apply/(has_nthP [::]).
            exists i; first by rewrite size_map size_enum_ord.
            have Hpos: 0 < size ts by rewrite (leq_ltn_trans _ Hi).
            rewrite (nth_map (cast_ord (prednK Hpos) ord0)) ?size_enum_ord //.
            set lt' := LCSL_strong _ _ _.
            case: (svalP lt') => _ _ /(_ (x :: u)) -> // {lt'}.
            + by rewrite /= eqxx.
            + apply/allP => t'; rewrite nth_enum_ord // => /(nthP [::]) [j].
              rewrite size_set_nth (maxn_idPr Hi) nth_set_nth /= => Hj <-.
              case: ifP => [_ | Hij].
              * move/allP/(_ (nth [::] ts i)): Hzuts.
                by rewrite Hnthi /= eq_sym (negPf Hyx) => ->.
              * move/allP/(_ (nth [::] ts j)): Hzuts => -> //.
                by rewrite mem_nth.
        }
      * by move=> Hzus'; case: (svalP ls) => _ _ /(_ (z :: u)) ->.
Qed.
Next Obligation.
Proof.
  split; [by rewrite sub0seq | by apply/allP => *; rewrite sub0seq |].
  move=> u {LCSL_strong}; case: s H; last by move => x s /(_ x s).
  by rewrite subseq0 => _ /eqP ->.
Qed.

End LongestCommonSubsequenceForList.
