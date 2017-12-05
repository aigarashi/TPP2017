From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ********************* *)
Section LCS.
  Variable (T:eqType).

  Fixpoint behind a (s:seq T) :=
    if s is x :: s' then if a == x then s' else behind a s' else [::].

  Definition argmax I (F:I -> nat) x y := if (F x) > (F y) then x else y.

  Fixpoint LCS (s t:seq T) : seq T :=
    if s is x :: s'
    then if x \in t
         then argmax size (x :: LCS s' (behind x t)) (LCS s' t)
         else LCS s' t
    else [::].

  Lemma LCS_subseql s t : subseq (LCS s t) s.
  Proof.
    elim : s =>[|x s IHs]//= in t *.
    case : ifP =>[|_]; last exact : subseq_trans (subseq_cons _ _).
    rewrite /argmax. case : ifP =>[|_ _]; first by rewrite eq_refl.
    exact : subseq_trans (subseq_cons _ _).
  Qed.

  Lemma LCS_subseqr s t : subseq (LCS s t) t.
  Proof.
    elim : s =>[|x s IHs]/= in t *; first exact : sub0seq.
    case : ifP =>//. rewrite /argmax. case : ifP =>//_.
    elim : t =>[|y t IHt]//=. rewrite in_cons. by case : ifP =>->.
  Qed.

  Lemma LCS_sizesup s t u :
    subseq u s -> subseq u t -> size u <= size (LCS s t).
  Proof.
    elim : s =>[|xs s IHs]/= in u t *=>[/eqP->|]//. case : u =>[|xu u]//.
    case : ifP =>[/eqP-> Hus Hut|_]; last (case : ifP =>_; last exact : IHs).
    - rewrite (mem_subseq Hut (mem_head _ _)) /argmax /= ltnS.
      case : ifP =>[|/negP /negP]/=; first rewrite ltnS.
      + exact : leq_trans (IHs _ _ Hus (subseq_trans (subseq_cons _ _) Hut)).
      + rewrite -ltnNge. apply : leq_ltn_trans (IHs _ _ Hus _).
        elim : t Hut =>[|xt t IHt]//=. by case : ifP.
    - rewrite /argmax => Hus /(IHs _ _ Hus) Hsize. case : ifP =>// /ltnW.
      exact : leq_trans Hsize.
  Qed.
End LCS.