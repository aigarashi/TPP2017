(* TPPmark 2017 finType version by Mitsuharu Yamamoto *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LongestCommonSubsequence.

Variable T : choiceType.

Definition all_subseqs :=
  foldr (fun (x : T) ss => ss ++ map (cons x) ss) [:: [::]].

Lemma mem_all_subseqs s t : (s \in all_subseqs t) = subseq s t.
Proof.
  elim: t => [| y t IHt] in s *; first by rewrite inE.
  case: s => [| x s] => /=; rewrite mem_cat; first by rewrite IHt sub0seq.
  case: ifPn => [/eqP <- | /eqP Hxy]; rewrite IHt.
  - rewrite mem_map ?IHt ?orb_idl //; last by move=> ? ? [].
    by apply: subseq_trans; rewrite subseq_cons.
  - rewrite orb_idr // => /nthP -/(_ [::]) [n].
    rewrite size_map => Hsize Hnth. case: Hxy. move: Hnth.
    by rewrite (nth_map [::]) // => -[->].
Qed.

(* Alternatively,
Definition all_subseqs (s : seq T) := [seq mask m s | m : (size s).-tuple bool].

Lemma mem_all_subseqs s t : (s \in all_subseqs t) = subseq s t.
Proof.
  apply/imageP/subseqP => /=; last by move=> [m <- ->]; exists (in_tuple m).
  by move=> [m _ ->]; exists m => //; rewrite size_tuple.
Qed.
*)

Lemma nil_in_all_subseqs s : [::] \in all_subseqs s.
Proof.  by rewrite mem_all_subseqs sub0seq.  Qed.

Definition LCS s t : seq T :=
  val [arg max_(r > (Sub [::] (nil_in_all_subseqs s) : seq_sub (all_subseqs s))
               | subseq (val r) t)
           size (val r)].

Lemma lcs_subseq s t : subseq (LCS s t) s /\ subseq (LCS s t) t.
Proof.
  rewrite /LCS; split; first by rewrite -mem_all_subseqs; apply: valP.
  by case: arg_maxP => //=; rewrite sub0seq.
Qed.

Lemma lcs_longest s t u : subseq u s -> subseq u t -> size u <= size (LCS s t).
Proof.
  rewrite /LCS => Hus Hut; case: arg_maxP => /=; first by rewrite sub0seq.
  move=> r Hr; rewrite -mem_all_subseqs in Hus; move/(_ (Sub u Hus)).
  by rewrite SubK => ->.
Qed.

End LongestCommonSubsequence.

Section LongestCommonSubsequenceForList.

Variable T : choiceType.

Definition LCSL s ts : seq T :=
  val [arg max_(r > (Sub [::] (nil_in_all_subseqs s) : seq_sub (all_subseqs s))
               | all (subseq (val r)) ts)
           size (val r)].

Lemma lcsl_subseq s ts : subseq (LCSL s ts) s /\ all (subseq (LCSL s ts)) ts.
Proof.
  rewrite /LCSL; split; first by rewrite -mem_all_subseqs; apply: valP.
  by case: arg_maxP => //=; apply/allP => *; rewrite sub0seq.
Qed.

Lemma lcsl_longest s ts u :
  subseq u s -> all (subseq u) ts -> size u <= size (LCSL s ts).
Proof.
  rewrite /LCSL => Hus Hut; case: arg_maxP => /=.
  - by apply/allP => *; rewrite sub0seq.
  - move=> r /allP Hr; rewrite -mem_all_subseqs in Hus; move/(_ (Sub u Hus)).
    by rewrite SubK => ->.
Qed.

End LongestCommonSubsequenceForList.
