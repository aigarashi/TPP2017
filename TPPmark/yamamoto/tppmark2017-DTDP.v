(* TPPmark 2017 dependently-typed DP version by Mitsuharu Yamamoto *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dseq (X : Type) (T : seq X -> Type) : seq X -> Type :=
| DNil : dseq T [::]
| DCons (x : X) (s : seq X) of T s & dseq T s : dseq T (x :: s).

Arguments DNil [X T].
Arguments DCons [X T x s] _ _.

Section DynamicProgramming.

Variables X Y : Type.
Variable Z : seq X -> seq Y -> Type.

Variable z00 : Z [::] [::].
Variable zc0 : forall x s, Z s [::] -> Z (x :: s) [::].
Variable z0c : forall y t, Z [::] t -> Z [::] (y :: t).
Variable zcc : forall x s y t, Z s t -> Z s (y :: t) -> Z (x :: s) t ->
                               Z (x :: s) (y :: t).

Fixpoint dp0t t : Z [::] t * dseq (Z [::]) t :=
  if t is y :: t' then let: (z, zs) := dp0t t' in (z0c y z, DCons z zs)
  else (z00, DNil).

Fixpoint dpt x s t : Z s t * dseq (Z s) t -> (* zs *)
                     Z (x :: s) t * dseq (Z (x :: s)) t :=
  if t is y :: t' then
    fun zs =>
      (if zs.2 is DCons y0 t'0 z' zs' in dseq _ t0 return t0 = y :: t' -> _ then
         fun E => let: Et' := congr1 behead E : t'0 = t' in
                  let: (zy, zt') := dpt x (ecast _ _ Et' (z', zs')) in
                  (zcc (ecast _ _ Et' z') zs.1 zy, DCons zy zt')
       else
         fun E => match List.nil_cons E with end) (erefl (y :: t'))
  else
    fun zs => (zc0 x zs.1, DNil).

(* Alternatively,
Definition dpt x s t (zs : Z s t * dseq (Z s) t)
  : Z (x :: s) t * dseq (Z (x :: s)) t.
  elim: t => [| y t IHt] in zs *; first by apply: (zc0 x zs.1, DNil).
  case: zs => z; case E: _ / => [| y' t' z' zs'] //.
  case: E => <- <- {y' t'} in z' zs' *; case/(_ (z', zs')): IHt => zy zt'.
  exact: (zcc z' z zy, DCons zy zt').
Defined.
*)

Fixpoint dps s t : Z s t * dseq (Z s) t :=
  if s is x :: s' then dpt x (dps s' t) else dp0t t.

Definition dp s t : Z s t := (dps s t).1.

(* unfolding lemmas; only used in the weakly-specified version *)

Lemma dp00 : dp [::] [::] = z00.
Proof.  by [].  Qed.

Lemma dp0c y t : dp [::] (y :: t) = z0c y (dp [::] t).
Proof.  by rewrite /dp /=; case: dp0t.  Qed.

Lemma dpc0 x s : dp (x :: s) [::] = zc0 x (dp s [::]).
Proof.
  by rewrite /dp; elim: s => [| x' s ->] //= in x *; case: dps => ? [| ? ?].
Qed.

Lemma dpscc x y s t :
  dps (x :: s) (y :: t) = (zcc (dp s t) (dp s (y :: t)) (dp (x :: s) t),
                           DCons (dp (x :: s) t) (dps (x :: s) t).2).
Proof.
  rewrite /dp; elim: s => /= [| x' s ->] in x *.
  - by case: dp0t => ? ? /=; case: dpt.
  - by rewrite /= -surjective_pairing; case: dpt.
Qed.

Lemma dpcc x y s t :
  dp (x :: s) (y :: t) = zcc (dp s t) (dp s (y :: t)) (dp (x :: s) t).
Proof.  by rewrite /dp dpscc.  Qed.

End DynamicProgramming.

Section LongestCommonSubsequence.

Definition argmax (X : Type) f (x y : X) := if f x < f y then y else x.

Lemma argmax_maxn (X : Type) f (x y : X) : f (argmax f x y) = maxn (f x) (f y).
Proof.  by rewrite /argmax fun_if.  Qed.

Variable T : eqType.

(* Strongly-specified version *)

Definition LCS_spec (s t lcs : seq T) :=
  [/\ subseq lcs s, subseq lcs t &
      forall u, subseq u s -> subseq u t -> size u <= size lcs].

Definition LCS_strong s t : {lcs | LCS_spec s t lcs}.
  apply: dp (exist _ [::] _)
            (fun _ _ _ => exist _ [::] _) (fun _ _ _ => exist _ [::] _)
            (fun x _ y _ st syt xst =>
               exist _ (if x == y then x :: sval st
                        else argmax size (sval syt) (sval xst)) _)
            s t.
  - by split=> //= ? /eqP ->.
  - by move=> ? ? ?; split=> // ? ? /eqP ->.
  - by move=> ? ? ?; split=> // ? /eqP ->.
  - move=> x s y t [st [Hst1 Hst2 Hst3]].
    move=> [syt [Hsyt1 Hsyt2 Hsyt3]] [xst [Hxst1 Hxst2 Hxst3]].
    rewrite ![sval _]/=; split.
    + case: ifP => [_ | Hxy]; first by rewrite /= eqxx.
      rewrite /argmax; case: ifP => _ //.
      by rewrite (subseq_trans Hsyt1) // subseq_cons.
    + case: ifP => [/eqP -> | Hxy]; first by rewrite /= eqxx.
      rewrite /argmax; case: ifP => _ //.
      by rewrite (subseq_trans Hxst2) // subseq_cons.
    + case=> [| z u] //; case: ifP => [/eqP <- | Hxy] /=.
      * by move=> Hs Ht; move: (Hst3 _ Hs Ht); case: ifP => _ // /leqW.
      * { rewrite argmax_maxn leq_max; case: ifP => [/eqP -> | _] Hs.
          - by rewrite Hxy => Ht; rewrite (Hxst3 (x :: u)) ?orbT //= eqxx.
          - by move=> Ht; rewrite (Hsyt3 (z :: u)).
        }
Defined.

(* Weakly-specified version; identical to the normal DP one *)

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
