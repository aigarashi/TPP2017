(* LCS *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.

Section lcs.
Variable A : eqType.

Fixpoint build_lcss_line prev s1 (b : A) {struct s1} :=
  match s1 with
  | nil => nil
  | a :: s1' =>
    match prev with
    | nil => nil
    | lcs2 :: prev' =>
      let line := build_lcss_line prev' s1' b in
      let lcs1 := head nil line in
      (if a == b then b :: head nil prev' else
       if size lcs1 <= size lcs2 then lcs2 else lcs1) :: line
    end
  end.

Fixpoint build_lcss s1 s2 :=
  match s2 with
  | nil => map (fun _ => nil) s1
  | b :: s2' =>
    let lcss := build_lcss s1 s2' in
    build_lcss_line lcss s1 b
  end.

Definition lcs s1 s2 := head nil (build_lcss s1 s2).

Inductive substring : list A -> list A -> Prop :=
  | ss_nil : forall l, substring nil l
  | ss_cons : forall a s1 s2, substring s1 s2 -> substring (a::s1) (a::s2)
  | ss_drop : forall s1 b s2, substring s1 s2 -> substring s1 (b::s2).

Hint Constructors substring.

Lemma tl_build_lcss a s1 s2 :
  behead (build_lcss (a :: s1) s2) = build_lcss s1 s2.
Proof.
  elim: s2 => //= b s2 IHs2.
  case: (build_lcss (a :: s1) s2) IHs2 => [<- | s ss].
    by case: s1.
  by case: ifP => E <-.
Qed.

Theorem lcs_substring s1 s2 :
  substring (lcs s1 s2) s1 /\ substring (lcs s1 s2) s2.
Proof.
  rewrite /lcs.
  elim: s2 s1 => /= [[] // | b s2 IHs2].
  elim => // a s1 IHs1.
  case H: (build_lcss _ s2).
    by destruct s2.
  move: (f_equal (@behead _) H) IHs1 (IHs2 s1).
  rewrite tl_build_lcss => -> /= [Hs1 Hs2] [Hs1' Hs2'].
  case: ifP => [/eqP <- | N]; first by auto.
  case: ifP => _; last by auto.
  by case: (IHs2 (a :: s1)); rewrite H; auto.
Qed.

Inductive bounded_gap n : list (list A) -> Prop :=
  | bg_nil : bounded_gap n nil
  | bg_sing : forall l, size l <= n -> bounded_gap n (l :: nil)
  | bg_cons : forall l1 l2 r,
      size l2 <= size l1 -> size l1 <= n + size l2 ->
      bounded_gap n (l2 :: r) -> bounded_gap n (l1 :: l2 :: r).

Inductive bounded_diff n : list (list A) -> list (list A) -> Prop :=
  | bd_nil : bounded_diff n nil nil
  | bd_cons : forall a b l1 l2,
      size a <= size b -> size b <= n+size a ->
      bounded_diff n l1 l2 -> bounded_diff n (a::l1) (b::l2).

Hint Constructors bounded_gap bounded_diff.

Lemma build_lcss_line_gap prev s1 a :
  bounded_gap 1 prev -> size prev = size s1 ->
  bounded_gap 1 (build_lcss_line prev s1 a) /\
  bounded_diff 1 prev (build_lcss_line prev s1 a).
Proof.
  move => Hg.
  elim: Hg s1 => //= [|l Hl|l1 l2 ls Hl2 Hl1 Hbg IH] [] // b s1.
    case: s1 => //= _.
    by case: ifP => _; auto.
  move=> [] /(IH _) [] /=.
  case Hbl: (build_lcss_line _ s1) => Hg Hd /=; inversion Hd; subst.
  case: ifP => _ {b}; first by auto.
  case: ifP => Hlen.
    split; auto.
    by inversion Hg; subst; constructor => //; apply (leq_trans Hl1).
  split.
    by inversion Hg; auto.
  constructor => //.
    by rewrite ltnW // ltnNge Hlen.
  by apply: leq_trans; eauto.
Qed.

Lemma length_build_lcss s1 s2 : size (build_lcss s1 s2) = size s1.
Proof.
  elim: s2 => /= [|b s2 IHs2]; first by rewrite size_map.
  elim: s1 (build_lcss s1 s2) IHs2 => //= a s1 IHs1 [// | s prev] IHs2.
  by case: ifP => E /=; rewrite IHs1 //; case: IHs2.
Qed.

Lemma bounded_gap_lcss s1 s2 : bounded_gap 1 (build_lcss s1 s2).
Proof.
  elim: s2 => /= [|a s2 IHs2].
    by elim: s1 => //= b [] /=; auto.
  case: (build_lcss_line_gap _ s1 a IHs2) => //.
  apply length_build_lcss.
Qed.

Theorem lcs_max s1 s2 s :
  substring s s1 -> substring s s2 -> length s <= length (lcs s1 s2).
Proof.
  rewrite /lcs => Hs1 Hs2.
  elim: Hs2 s1 Hs1 => //= {s s2} [b s|s b] s2 Hs2 IHs2.
    elim => [|a s1 IHs1] Hs1.
      by inversion Hs1.
    case H: (build_lcss _ s2).
      move: (f_equal (@size _) H).
      by rewrite length_build_lcss.
    move: {H} (f_equal (@behead _) H) Hs1.
    rewrite tl_build_lcss /= => <-.
    case: ifP => [/eqP -> | N] Hs1.
      inversion Hs1; subst.
        by apply: (IHs2 s1).
      apply: leq_trans; first by apply IHs1.
      case: (build_lcss_line_gap _ s1 b (bounded_gap_lcss s1 s2)) => [|_ Hd].
        apply length_build_lcss.
      by inversion Hd; auto.
    inversion Hs1; subst => //=.
      by rewrite eqxx in N.
    case: ifP => Hlen.
      by apply: leq_trans; first apply IHs1.
    by apply IHs1.
  move=> s1 /(IHs2 _) Hlen.
  apply (leq_trans Hlen).
  case: (build_lcss_line_gap _ s1 b (bounded_gap_lcss s1 s2)) => [|_ Hd].
    apply length_build_lcss.
  by inversion Hd; auto.
Qed.
End lcs.

Eval compute in build_lcss _ (1::2::1::3::nil) (1::3::2::nil).
Eval compute in build_lcss _ (1::3::2::nil) (1::2::1::3::2::nil).
Eval compute in lcs _ (1::2::1::3::nil) (1::2::nil).


