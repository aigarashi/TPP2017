(* TPPmark 2017 DP version by Mitsuharu Yamamoto *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DynamicProgramming.

Variables X Y Z : Type.

Variable z00 : Z.
Variable zc0 : X -> seq X -> Z -> Z.
Variable z0c : Y -> seq Y -> Z -> Z.
Variable zcc : X -> seq X -> Y -> seq Y -> Z -> Z -> Z -> Z.

Fixpoint dp0t t :=
  if t is y :: t' then let: (z, zs) := dp0t t' in (z0c y t' z, z :: zs)
  else (z00, [::]).

Fixpoint dpt x s t zs :=
  match t, zs with
  | y :: t', (z, z' :: zs') => let: (zy, zt') := dpt x s t' (z', zs') in
                               (zcc x s y t' z' z zy, zy :: zt')
  | _, (z, _) => (zc0 x s z, [::])
  end.

Fixpoint dps s t := if s is x :: s' then dpt x s' t (dps s' t) else dp0t t.

Definition dp s t := (dps s t).1.

Lemma dp00 : dp [::] [::] = z00.
Proof.  by [].  Qed.

Lemma dp0c y t : dp [::] (y :: t) = z0c y t (dp [::] t).
Proof.  by rewrite /dp /=; case: dp0t.  Qed.

Lemma dpc0 x s : dp (x :: s) [::] = zc0 x s (dp s [::]).
Proof.
  by rewrite /dp; elim: s => [| x' s ->] //= in x *; case: dps => ? [| ? ?].
Qed.

Lemma dpscc x y s t :
  dps (x :: s) (y :: t) = (zcc x s y t (dp s t) (dp s (y :: t)) (dp (x :: s) t),
                           dp (x :: s) t :: (dps (x :: s) t).2).
Proof.
  rewrite /dp; elim: s => /= [| x' s ->] in x *.
  - by case: dp0t => ? [| ? ?]; case: dpt.
  - by rewrite -surjective_pairing; case: dpt.
Qed.

Lemma dpcc x y s t :
  dp (x :: s) (y :: t) = zcc x s y t (dp s t) (dp s (y :: t)) (dp (x :: s) t).
Proof.  by rewrite /dp dpscc.  Qed.

End DynamicProgramming.

Section LongestCommonSubsequence.

Definition argmax (X : Type) f (x y : X) := if f x < f y then y else x.

Lemma argmax_maxn (X : Type) f (x y : X) : f (argmax f x y) = maxn (f x) (f y).
Proof.  by rewrite /argmax fun_if.  Qed.

Variable T : eqType.

Definition LCS : seq T -> seq T -> seq T :=
  dp [::] (fun _ _ _ => [::]) (fun _ _ _ => [::])
     (fun x _ y _ st syt xst =>
        if x == y then x :: st else argmax size syt xst).

Lemma lcs_nil_l s : LCS [::] s = [::].
Proof.  by rewrite /LCS; case: s => [| ? ?]; rewrite ?dp00 ?dp0c.  Qed.

Lemma lcs_nil_r s : LCS s [::] = [::].
Proof.  by rewrite /LCS; case: s => [| ? ?]; rewrite ?dp00 ?dpc0.  Qed.

Lemma lcs_cons x s y t :
  LCS (x :: s) (y :: t) = if x == y then x :: LCS s t
                          else argmax size (LCS s (y :: t)) (LCS (x :: s) t).
Proof.  by rewrite /LCS dpcc.  Qed.

(* Alternatively,
Fixpoint LCS2 x us t : seq (seq T) :=
  if t is y :: t' then let p := LCS2 x (behead us) t' in
                         (if x == y then x :: head [::] (behead us)
                          else argmax size (head [::] us) (head [::] p)) :: p
  else [::].

Fixpoint LCS1 s t : seq (seq T) :=
  if s is x :: s' then LCS2 x (LCS1 s' t) t else [::].

Definition LCS s t := head [::] (LCS1 s t).

Lemma lcs_nil_l s : LCS [::] s = [::].
Proof.  by [].  Qed.

Lemma lcs_nil_r s : LCS s [::] = [::].
Proof.  by rewrite /LCS; case: s => [| x s] //=; case: LCS1.  Qed.

Lemma lcs_cons_aux x s y t :
  LCS1 (x :: s) (y :: t) = (if x == y then x :: (LCS s t)
                            else argmax size (LCS s (y :: t)) (LCS (x :: s) t))
                             :: LCS1 (x :: s) t.
Proof.  by rewrite /LCS; elim: s => [| x' s /= /(_ x') [-> ->]] // in x *.  Qed.

Lemma lcs_cons x s y t :
  LCS (x :: s) (y :: t) = if x == y then x :: LCS s t
                          else argmax size (LCS s (y :: t)) (LCS (x :: s) t).
Proof.  by rewrite /LCS lcs_cons_aux.  Qed.
*)

Lemma lcs_subseq s t : subseq (LCS s t) s /\ subseq (LCS s t) t.
Proof.
  elim: s => [| x s IHs] in t *; first by rewrite lcs_nil_l !sub0seq.
  elim: t => [| y t [IHts IHtt]]; first by rewrite lcs_nil_r sub0seq.
  rewrite lcs_cons; case: ifP => [/eqP -> | Hxy]; first by rewrite /= eqxx.
  case/IHs: (y :: t) => IHss IHst; rewrite /argmax; split; case: ifP => _ //.
  - by rewrite (subseq_trans IHss) // subseq_cons.
  - by rewrite (subseq_trans IHtt) // subseq_cons.
Qed.

Lemma lcs_longest s t u : subseq u s -> subseq u t -> size u <= size (LCS s t).
Proof.
  elim: s => [| x s IHs] in u t *; first by move=> /eqP ->.
  elim: t => [| y t IHt] in u *; first by move=> _ /eqP ->.
  case: u => [| z u] //; rewrite lcs_cons; case: ifP => [/eqP <- {y} | Hxy] /=.
  - by move=> Hs Ht; move: (IHs _ _ Hs Ht); case: ifP => _ // /leqW.
  - rewrite argmax_maxn leq_max; case: ifP => [/eqP -> | _] Hs.
    + by rewrite Hxy => Ht; rewrite (IHt (x :: u)) ?orbT //= eqxx.
    + by move=> Ht; rewrite (IHs (z :: u)).
Qed.

End LongestCommonSubsequence.

Section LongestCommonSubsequenceForList.  (* !!! NOT COMPLETED !!! *)

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

Fixpoint nhead_simpl (X : Type) (d : X) n : iter n seq X -> X :=
  if n is n'.+1 then
    fun s => if s is x :: s' then nhead_simpl d x else d
  else
    id.

Definition nhead := nosimpl nhead_simpl.

Arguments nhead [X] d n s.

Lemma nhead_nil (X : Type) (d : X) n : nhead d n.+1 [::] = d.
Proof.  by [].  Qed.

Lemma nhead_cons (X : Type) (d : X) n x s : nhead d n.+1 (x :: s) = nhead d n x.
Proof.  by [].  Qed.

Definition nheadE := (nhead_nil, nhead_cons).

Fixpoint LCSLs s ys diag neighbors : seq (seq T) :=
  if s is x :: s' then
    let prev := LCSLs s' ys (omap behead diag) (map behead neighbors) in
    (if all (pred1 x) ys then x :: head [::] (oapp behead prev diag)
     else argmaxl size (head [::] prev) (map (head [::]) neighbors)) :: prev
  else [::].

Fixpoint LCSLts_simpl s ts ys :
  option (iter (size ts).+1 seq (seq T)) -> (* diag *)
  seq (iter (size ts).+1 seq (seq T)) -> (* neighbors *)
  iter (size ts).+1 seq (seq T) :=
  if ts is t :: ts' then
    fun diag neighbors =>
      let fix LCSLt t neighbors :=
          if t is y :: t' then
            let prev := LCSLt t' (map behead neighbors) in
            (@LCSLts_simpl s ts' (y :: ys)
                           (Some (head [::] (oapp behead prev diag)))
                           (head [::] prev :: map (head [::]) neighbors))
              :: prev
          else [::]
      in LCSLt t neighbors
  else fun diag neighbors => LCSLs s ys diag neighbors.

Definition LCSLts := nosimpl LCSLts_simpl.

Arguments LCSLts : clear implicits.

Lemma LCSLts_nil s ys diag neighbors:
  LCSLts s [::] ys diag neighbors = LCSLs s ys diag neighbors.
Proof.  by [].  Qed.

Lemma LCSLts_cons_nil s ts ys diag neighbors:
  LCSLts s ([::] :: ts) ys diag neighbors = [::].
Proof.  by [].  Qed.

Lemma LCSLts_cons_cons s y t ts ys diag neighbors:
  LCSLts s ((y :: t) :: ts) ys diag neighbors =
  let prev := LCSLts s (t :: ts) ys diag (map behead neighbors) in
  (LCSLts s ts (y :: ys) (Some (head [::] (oapp behead prev diag)))
          (head [::] prev :: map (head [::]) neighbors)) :: prev.
Proof.  by [].  Qed.

Definition LCSLtsE := (LCSLts_nil, LCSLts_cons_nil, LCSLts_cons_cons).

Definition LCSL s ts := nhead [::] _ (LCSLts s ts [::] None [::]).

Lemma lcsl_nil_l ts : LCSL [::] ts = [::].
Proof.
  rewrite /LCSL; move: {3}[::] (Nil (iter (size ts).+1 seq (seq T))) None.
  by rewrite /nhead /LCSLts; elim: ts => //= t ts IHts; case: t.
Qed.

Lemma lcsl_nil_r s ts : [::] \in ts -> LCSL s ts = [::].
Proof.
  rewrite /LCSL; move: {3}[::] (Nil (iter (size ts).+1 seq (seq T))) None.
  rewrite /nhead; elim: ts => //= t ts IHts ys diag neighbors.
  rewrite inE => /predU1P [<- | Hts] //.
  by case: t => [| y t] // in diag neighbors *; rewrite IHts.
Qed.

Fixpoint nmap (X : Type) n (f : seq X -> seq X) : iter n.+1 seq X -> iter n.+1 seq X :=
  if n is n'.+1 then map (nmap f) else f.

Lemma nmap_behead_nil X n : nmap behead (Nil (iter n seq X)) = [::].
Proof.  by elim: n.  Qed.

Lemma nmap_behead_head X n (s : iter n.+2 seq X) :
  nmap behead (head [::] s) = head [::] (map (nmap behead) s).
Proof.  by case: s => //=; rewrite nmap_behead_nil.  Qed.

Lemma lcsl_cons_behead x s ts ys diag neighbors :
  size ys = size neighbors ->
  nmap behead (LCSLts (x :: s) ts ys diag neighbors) =
  LCSLts s ts ys (omap (nmap behead) diag) (map (nmap behead) neighbors).
Proof.
  elim: ts => [| t ts IHts] in ys diag neighbors *; first by rewrite !LCSLtsE.
  elim: t => [| y t IHt] // in diag neighbors *.
  move=> Hsize; move/(_ diag (map behead neighbors)): IHt.
  rewrite Hsize size_map -map_comp => /(_ erefl) IHt; rewrite /= in IHt.
  rewrite !LCSLtsE /= IHts //; last by rewrite /= size_map Hsize.
  congr cons.
  - congr LCSLts.
    + case: diag => [d |] /= in IHt *; rewrite nmap_behead_head.
      * by congr (Some (head _ _)); case: d {IHt}.
      * congr (Some (head _ _)); rewrite IHt -map_comp.
        by congr (LCSLts _ (_ :: _)); apply: eq_map => -[].
    + rewrite /=; congr cons.
      * rewrite nmap_behead_head IHt -map_comp.
        by congr (head [::] (LCSLts _ (_ :: _) _ _ _)); apply: eq_map => -[].
      * by rewrite -!map_comp; apply: eq_map => ?; rewrite /= nmap_behead_head.
  - by rewrite IHt -map_comp; congr (LCSLts _ (_ :: _)); apply: eq_map => -[].
Qed.

Lemma lcsl_cons x s ts :
  [::] \notin ts ->
  LCSL (x :: s) ts =
  if all (pred1 (Some x)) (map ohead ts) then x :: LCSL s (map behead ts)
  else argmaxl size (LCSL s ts)
               (rev [tuple LCSL (x :: s) (set_nth [::] ts i
                                                  (behead (nth [::] ts i)))
                    | i < size ts]).
Proof.
Admitted.

Definition LCSL_spec s ts (lcsl : seq T) :=
  [/\ subseq lcsl s, all (subseq lcsl) ts &
      forall u, subseq u s -> all (subseq u) ts -> size u <= size lcsl].

Lemma lcsl_correct_nil_l ts : LCSL_spec [::] ts (LCSL [::] ts).
Proof.
  rewrite lcsl_nil_l; split; first by rewrite sub0seq.
  - by apply/allP => ?; rewrite sub0seq.
  - by move=> ?; rewrite subseq0 => /eqP ->.
Qed.

Lemma lcsl_correct_nil_r s ts : [::] \in ts -> LCSL_spec s ts (LCSL s ts).
Proof.
  move=> Hts; rewrite lcsl_nil_r //; split; first by rewrite sub0seq.
  - by apply/allP => ?; rewrite sub0seq.
  - by move=> ? _ /allP /(_ _ Hts); rewrite subseq0 => /eqP ->.
Qed.

Lemma lcsl_correct s ts : LCSL_spec s ts (LCSL s ts).
Proof.
  pose mes (s : seq T) (ts : seq (seq T)) := size s + (\sum_(t <- ts) size t).
  elim: {s ts}(mes s ts) {-2}s {-2}ts (leqnn (mes s ts)) => [| n IHn] s ts.
  - rewrite leqn0 addn_eq0 size_eq0 => /andP [/eqP -> _].
    exact: lcsl_correct_nil_l.
  - case: s => [| x s] Hmes; first by apply: lcsl_correct_nil_l.
    case: (boolP ([::] \in ts)) => [| Hts]; first by apply: lcsl_correct_nil_r.
    rewrite lcsl_cons //. case: ifP => Hx.
    + have /IHn [IH1 IH2 IH3] : mes s [seq behead i | i <- ts] <= n.
      { move: Hmes; rewrite /mes /= addSn ltnS; apply: leq_trans.
        rewrite leq_add2l big_map leq_sum // => t.
        by rewrite size_behead leq_pred. }
      split; first by rewrite /= eqxx.
      * apply/allP => t Ht; move/allP/(_ (ohead t)): Hx.
        rewrite map_f //= => /(_ isT) H; case: t H => // _ t /eqP [] -> in Ht *.
        by rewrite /= eqxx (allP IH2) // (map_f behead Ht).
      * { case=> // z u; rewrite [subseq _ _] /=.
          case: ifP => [/eqP |] Hzx Hus Hzuts.
          - apply: IH3 => //; apply/allP => _ /mapP [t Ht ->].
            move/allP/(_ (ohead t)): Hx.
            rewrite map_f //= => /(_ isT) H; case: t H Ht => // _ t /eqP [] ->.
            by move/(allP Hzuts); rewrite Hzx /= eqxx.
          - apply: leqW; apply: IH3 => //; apply/allP => _ /mapP [t Ht ->].
            move/allP/(_ (ohead t)): Hx.
            rewrite map_f //= => /(_ isT) H; case: t H Ht => // y t /eqP [] ->.
            by move/(allP Hzuts); rewrite /= Hzx.
        }
    + have /IHn [IHs1 IHs2 IHs3] : mes s ts <= n
        by move: Hmes; rewrite /mes /= addSn ltnS.
      have Htsi (i : 'I_(size ts)) :
        mes (x :: s) (set_nth [::] ts i (behead (nth [::] ts i))) <= n.
      {
        move: Hmes; rewrite /mes /= addSn ltnS; apply: leq_trans.
        rewrite addSn -addnS leq_add2l; set ts' := set_nth _ _ _ _.
        have Hsize: size ts' = size ts by rewrite size_set_nth; apply/maxn_idPr.
        have Hts' i0 : i0 != i :> nat -> nth [::] ts' i0 = nth [::] ts i0
          by move=> Hi0; rewrite nth_set_nth /= (negPf Hi0).
        rewrite !(big_nth [::]) (@big_cat_nat _ _ _ i.+1) //= Hsize //.
        rewrite [X in _ < X](@big_cat_nat _ _ _ i.+1) //=.
        rewrite !big_nat_recr //= -addSn -addnS !big_nat !leq_add //.
        - apply: eq_leq; apply: eq_bigr => i0 Hi0; rewrite Hts' //.
          by apply/negP => /eqP Hi0i; rewrite Hi0i ltnn andbF in Hi0.
        - rewrite nth_set_nth /= eqxx size_behead prednK //.
          case E: nth => //; case/negP: Hts; rewrite -E; apply/nthP.
          by exists i.
        - apply: eq_leq; apply: eq_bigr => i0 Hi0; rewrite Hts' //.
          by apply/negP => /eqP Hi0i; rewrite Hi0i ltnn in Hi0.
      }
      set lts' := rev _; split.
      * { move/predU1P: (argmaxl_mem size (LCSL s ts) lts') => [-> |].
          - by rewrite (subseq_trans IHs1) ?subseq_cons.
          - rewrite /lts' [rev _]/= -!map_rev.
            by case/mapP => i Hi ->; case/IHn: (Htsi i).
        }
      * move/predU1P: (argmaxl_mem size (LCSL s ts) lts') => [-> |] //.
        rewrite /lts' [rev _]/= -!map_rev.
        case/mapP => i Hi ->; set ts' := set_nth _ _ _ _; set lt' := LCSL _ _.
        have Hts' : size ts' = size ts
          by rewrite size_set_nth; apply: maxn_idPr.
        apply/allP => _ /(nthP [::]) [j Hj <-].
        case/IHn: (Htsi i) => _ /allP /(_ (nth [::] ts' j)).
        rewrite mem_nth ?Hts' // nth_set_nth => /(_ isT) H _.
        rewrite /= in H; case: ifP H => // /eqP ->; rewrite /lt' /ts'.
        by case: nth => // y t /subseq_trans -> //; rewrite subseq_cons.
      * { case=> // z u Hzuxs Hzuts; apply: argmaxl_sup; rewrite /= in Hzuxs.
          move: Hzuxs; case: ifP => [/eqP {z}-> | Hzx] in Hzuts *.
          - move=> Hus'; case/allPn: Hx => _ /mapP [t Ht ->].
            case: t Ht => [/(negP Hts) | y t Hyt] // => Hyx.
            rewrite /= /eq_op /= in Hyx; case/(nthP [::]): (Hyt) => i Hi Hnthi.
            apply/orP; right; apply/hasP.
            exists (nth [::] lts' (rev_ord (Ordinal Hi))).
            + by rewrite mem_nth // size_rev size_map size_enum_ord.
            + rewrite /lts' (nth_rev [::]) size_tuple.
              rewrite -[size _ - _]/(rev_ord _ : nat) rev_ordK nth_mktuple.
              case/IHn: (Htsi (Ordinal Hi)) => _ _ -> //.
              * by rewrite /= eqxx.
              * { apply/allP => t' /(nthP [::]) [j].
                  rewrite size_set_nth (maxn_idPr Hi) nth_set_nth /= => Hj <-.
                  case: ifP => [_ | Hij].
                  - move/allP/(_ (nth [::] ts i)): Hzuts.
                    by rewrite Hnthi /= eq_sym (negPf Hyx) => ->.
                  - move/allP/(_ (nth [::] ts j)): Hzuts => -> //.
                    by rewrite mem_nth.
                }
              * by rewrite ltn_ord.
          - by move/IHs3 => ->.
        }
Qed.

End LongestCommonSubsequenceForList.

Eval compute in @LCSLts _ [:: 1; 2; 3; 4; 5] [:: [:: 2; 1; 3; 5] ] [::] None [::].
     (* = [:: [:: [:: 2; 3; 5]; [:: 2; 3; 5]; [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*       [:: [:: 1; 3; 5]; [:: 3; 5];    [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*       [:: [:: 3; 5];    [:: 3; 5];    [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*       [:: [:: 5];       [:: 5];       [:: 5];    [:: 5]; [:: 5]]] *)
     (* : iter (size [:: [:: 2; 1; 3; 5]]).+1 seq (seq nat_eqType) *)
Eval compute in @LCSLts _ [:: 1; 3; 4; 5] [:: [:: 2; 1; 3; 5] ] [::] None [::].
     (* = [:: [:: [:: 1; 3; 5]; [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*       [:: [:: 1; 3; 5]; [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*       [:: [:: 3; 5]; [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*       [:: [:: 5]; [:: 5]; [:: 5]; [:: 5]]] *)
     (* : iter (size [:: [:: 2; 1; 3; 5]]).+1 seq (seq nat_eqType) *)
Eval compute in @LCSLts _ [::] [:: [:: 2; 1; 3; 5] ] [::] None [::].
     (* = [:: [::]; [::]; [::]; [::]] *)
     (* : iter (size [:: [:: 2; 1; 3; 5]]).+1 seq (seq nat_eqType) *)
Eval compute in @LCSLts _ [:: 1; 2; 3; 4; 5] [:: [:: 1; 3; 4; 5]; [:: 2; 1; 3; 5] ] [::] None [::].
     (* = [:: [:: [:: [:: 1; 3; 5]; [:: 3; 5]; [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 1; 3; 5]; [:: 3; 5]; [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 3; 5]; [:: 3; 5]; [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 5]; [:: 5]; [:: 5]; [:: 5]; [:: 5]]]; *)
     (*       [:: [:: [:: 3; 5]; [:: 3; 5]; [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 3; 5]; [:: 3; 5]; [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 3; 5]; [:: 3; 5]; [:: 3; 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 5]; [:: 5]; [:: 5]; [:: 5]; [:: 5]]]; *)
     (*       [:: [:: [:: 5]; [:: 5]; [:: 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 5]; [:: 5]; [:: 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 5]; [:: 5]; [:: 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 5]; [:: 5]; [:: 5]; [:: 5]; [:: 5]]]; *)
     (*       [:: [:: [:: 5]; [:: 5]; [:: 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 5]; [:: 5]; [:: 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 5]; [:: 5]; [:: 5]; [:: 5]; [:: 5]]; *)
     (*           [:: [:: 5]; [:: 5]; [:: 5]; [:: 5]; [:: 5]]]] *)
     (* : iter (size [:: [:: 1; 3; 4; 5]; [:: 2; 1; 3; 5]]).+1 seq *)
     (*     (seq nat_eqType) *)
Eval compute in @LCSLts _ [:: 1; 2; 3; 4; 5] [:: [:: 1; 3; 4]; [:: 2; 1; 3; 5] ] [::] None [::].
     (* = [:: [:: [:: [:: 1; 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*           [:: [:: 1; 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*           [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*           [:: [::]; [::]; [::]; [::]; [::]]]; *)
     (*       [:: [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*           [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*           [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*           [:: [::]; [::]; [::]; [::]; [::]]]; *)
     (*       [:: [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*           [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*           [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*           [:: [::]; [::]; [::]; [::]; [::]]]] *)
     (* : iter (size [:: [:: 1; 3; 4]; [:: 2; 1; 3; 5]]).+1 seq (seq nat_eqType) *)
Eval compute in @LCSLts _ [:: 1; 2; 3; 4; 5] [:: [:: 1; 3; 4; 5]; [:: 2; 1; 3; 5]; [:: 2; 1; 3]] [::] None [::].
     (* = [:: [:: [:: [:: [:: 1; 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 1; 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]]; *)
     (*           [:: [:: [:: 1; 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 1; 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]]; *)
     (*           [:: [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]]; *)
     (*           [:: [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]]]; *)
     (*       [:: [:: [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]]; *)
     (*           [:: [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]]; *)
     (*           [:: [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]; *)
     (*               [:: [:: 3]; [:: 3]; [:: 3]; [::]; [::]]]; *)
     (*           [:: [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]]]; *)
     (*       [:: [:: [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]]; *)
     (*           [:: [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]]; *)
     (*           [:: [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]]; *)
     (*           [:: [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]]]; *)
     (*       [:: [:: [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]]; *)
     (*           [:: [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]]; *)
     (*           [:: [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]]; *)
     (*           [:: [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]; *)
     (*               [:: [::]; [::]; [::]; [::]; [::]]]]] *)
     (* : iter (size [:: [:: 1; 3; 4; 5]; [:: 2; 1; 3; 5]; [:: 2; 1; 3]]).+1 seq *)
     (*     (seq nat_eqType) *)
Eval compute in @LCSLts _ [:: 1; 2; 3; 4; 5] [:: [:: 1; 3; 4; 5]; [:: 2; 1; 3; 5]; [::]] [::] None [::].
     (* = [:: [:: [::]; [::]; [::]; [::]]; [:: [::]; [::]; [::]; [::]]; *)
     (*       [:: [::]; [::]; [::]; [::]]; [:: [::]; [::]; [::]; [::]]] *)
     (* : iter (size [:: [:: 1; 3; 4; 5]; [:: 2; 1; 3; 5]; [::]]).+1 seq *)
     (*     (seq nat_eqType) *)
Eval compute in @LCSLts _ [:: 1; 2; 3; 4; 5] [:: [::]; [:: 1; 3; 4; 5]; [:: 2; 1; 3; 5]] [::] None [::].
     (* = [::] *)
     (* : iter (size [:: [::]; [:: 1; 3; 4; 5]; [:: 2; 1; 3; 5]]).+1 seq *)
     (*     (seq nat_eqType) *)
Eval compute in @LCSLts _ [:: 1; 2; 3; 4; 5] [::] [::] None [::].
     (* = [:: [:: 1; 2; 3; 4; 5]; [:: 2; 3; 4; 5]; [:: *)
     (*       3; 4; 5]; [:: 4; 5]; [:: 5]] *)
     (* : iter (size [::]).+1 seq (seq nat_eqType) *)
