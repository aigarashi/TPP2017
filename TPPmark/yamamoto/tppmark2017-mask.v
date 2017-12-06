(* TPPmark 2017 mask version by Mitsuharu Yamamoto *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LongestCommonSubsequence.

Variable T : eqType.

Definition LCS s t : seq T :=
  mask [arg max_(m > [tuple of nseq (size s) false] | subseq (mask m s) t)
            size (mask m s)] s.

Lemma lcs_subseq s t : subseq (LCS s t) s /\ subseq (LCS s t) t.
Proof.
  rewrite /LCS; split; first by apply: mask_subseq.
  by case: arg_maxP => //; rewrite mask_false sub0seq.
Qed.

Lemma lcs_longest s t u : subseq u s -> subseq u t -> size u <= size (LCS s t).
Proof.
  rewrite /LCS => /subseqP [m [<- Hus]] Hut.
  case: arg_maxP => /=; first by rewrite mask_false sub0seq.
  by move=> ? _ /(_ (in_tuple m)); rewrite -Hus => ->.
Qed.

End LongestCommonSubsequence.

Section LongestCommonSubsequenceForList.

Variable T : eqType.

Definition LCSL s ts : seq T :=
  mask [arg max_(m > [tuple of nseq (size s) false] |
                 all (subseq (mask m s)) ts) size (mask m s)] s.

Lemma lcsl_subseq s ts : subseq (LCSL s ts) s /\ all (subseq (LCSL s ts)) ts.
Proof.
  rewrite /LCSL; split; first by apply: mask_subseq.
  by case: arg_maxP => //; apply/allP => *; rewrite mask_false sub0seq.
Qed.

Lemma lcsl_longest s ts u :
  subseq u s -> all (subseq u) ts -> size u <= size (LCSL s ts).
Proof.
  rewrite /LCSL => /subseqP [m [<- Hus]] Hut.
  case: arg_maxP => /=; first by apply/allP => *; rewrite mask_false sub0seq.
  by move=> ? _ /(_ (in_tuple m)); rewrite -Hus => ->.
Qed.

End LongestCommonSubsequenceForList.
