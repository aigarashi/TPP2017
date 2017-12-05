(*
Author: Jasper Hugunin
TPPmark 2017
Longest Common Subsequence
*)

(*
Let's aim for efficiency.
Consider an arbitrary type of elements A, whose elements take space size(A),
and for which we can decide equality in time dec(A).
Assume the given strings have lengths n and m, with n <= m.
Let the length of the longest common subsequence be b, then we have b <= n <= m.
Our input then has size ((n + m) * size(A)),
and our output has size (b * size(A)).

We iteratively generate one row of the grid at a time, storing the best
substring of n along with it's length.
Each cell should take O(log b + dec(A)) time, giving
O(n * m * (log b + dec(A))) time,
and (in a strict evaluation model at least)
we have to store one row at a time, with each cell taking O(n + log b) space
and so taking a total of O(n * (n + log b)) space.

We can then extract a string from the final result,
taking O(n) time and O(b * size(A) + n) space.
*)

From Coq Require Import NArith.
From Coq Require Import List.
From Coq Require Import DecidableClass.
From Coq Require Import SetoidDec.
From Coq Require Import SetoidClass.

Import ListNotations.
Close Scope nat_scope.
Open Scope N_scope.

Set Primitive Projections.

Definition length {A} : list A -> N
  := fold_right (fun _ => N.succ) 0.

(* StrictSubseq l1 l2 expresses that l1 is a subsequence of l2 *)
Inductive StrictSubseq {A} : list A -> list A -> Type :=
  | nil_nil_strict_subseq : StrictSubseq nil nil
  | keep_cons_strict_subseq
    : forall a l1 l2, StrictSubseq l1 l2 -> StrictSubseq l1 (a :: l2)
  | cons_cons_strict_subseq
    : forall a l1 l2, StrictSubseq l1 l2 -> StrictSubseq (a :: l1) (a :: l2)
.
Inductive WeakSubseq {A B} (R : A -> B -> Type) : list A -> list B -> Type :=
  | nil_nil_weak_subseq : WeakSubseq R nil nil
  | keep_cons_weak_subseq
    : forall b l1 l2, WeakSubseq R l1 l2 -> WeakSubseq R l1 (b :: l2)
  | cons_cons_weak_subseq
    : forall a b (aRb : R a b) l1 l2,
      WeakSubseq R l1 l2 -> WeakSubseq R (a :: l1) (b :: l2)
.

Definition LongestCommonSubsequence {A B} (R : A -> B -> Type)
  (seq1 : list A) (seq2 : list B) (ans : list A) : Type
  := StrictSubseq ans seq1 * WeakSubseq R ans seq2 *
     (forall ans', StrictSubseq ans' seq1 -> WeakSubseq R ans' seq2 ->
      length ans' <= length ans).

Module Import subseq.
Definition nil_strict_subseq {A} : forall l : list A, StrictSubseq nil l
  := fix nil_subseq l := match l with
     | nil => nil_nil_strict_subseq
     | cons a l' => keep_cons_strict_subseq a nil l' (nil_subseq l')
     end.
Definition nil_weak_subseq {A B} R
  : forall l : list B, WeakSubseq (A:=A) R nil l
  := fix nil_subseq l := match l with
     | nil => nil_nil_weak_subseq R
     | cons a l' => keep_cons_weak_subseq R a nil l' (nil_subseq l')
     end.

Definition strict_to_weak {A} R (Rrefl : forall a : A, R a a)
  : forall {l1 l2}, StrictSubseq l1 l2 -> WeakSubseq R l1 l2
  := fix strict_to_weak {l1 l2} H :=
     match H in StrictSubseq l1 l2 return WeakSubseq R l1 l2
     with
     | nil_nil_strict_subseq => nil_nil_weak_subseq _
     | keep_cons_strict_subseq a l1 l2 IH =>
       keep_cons_weak_subseq _ a l1 l2 (strict_to_weak IH)
     | cons_cons_strict_subseq a l1 l2 IH =>
       cons_cons_weak_subseq _ a a (Rrefl a) l1 l2 (strict_to_weak IH)
     end.
Definition weak_to_weak {A B} R1 R2
  (Rimpl : forall (a : A) (b : B), R1 a b -> R2 a b)
  : forall {l1 l2}, WeakSubseq R1 l1 l2 -> WeakSubseq R2 l1 l2
  := fix weak_to_weak {l1 l2} H :=
     match H in WeakSubseq _ l1 l2 return WeakSubseq R2 l1 l2
     with
     | nil_nil_weak_subseq _ => nil_nil_weak_subseq R2
     | keep_cons_weak_subseq _ b l1 l2 IH =>
       keep_cons_weak_subseq R2 b l1 l2 (weak_to_weak IH)
     | cons_cons_weak_subseq _ a b aR1b l1 l2 IH =>
       cons_cons_weak_subseq R2 a b (Rimpl a b aR1b) l1 l2 (weak_to_weak IH)
     end.
End subseq.

Module Import inner.
Section inner.
(*
We take as the elements of our sequences arbitrary types with a decidable
relation. We produce a strict substring of the first, and a substring up to
the relation of the second.
*)
Context {A B : Type} (R : A -> B -> bool).
Context (seq1 : list A) (seq2 : list B).

Record cell := { cell_len : N; cell_sel : list bool; }.
Definition row := list cell.
Definition row_hd : row -> cell := hd {| cell_len := 0; cell_sel := [] |}.

Definition cell_max : cell -> cell -> cell
  := fun c1 c2 => match cell_len c1 ?= cell_len c2 with
     | Eq | Lt => c2
     | Gt => c1
     end.
Definition pad_cell : cell -> cell
  := fun c => {| cell_len := cell_len c; cell_sel := false :: cell_sel c |}.
Definition inc_cell : cell -> cell
  := fun c =>
     {| cell_len := N.succ (cell_len c); cell_sel := true :: cell_sel c |}.
Definition cell_update (diag : cell) (left : cell) (up : cell) (a : A) (b : B)
  : cell
  := let standard := cell_max (pad_cell left) up in
     if R a b then cell_max standard (inc_cell diag) else standard.

Definition inner_initial_row : list A -> row * list bool
  := fix init seq := match seq with
     | [] => ([], [])
     | a :: seq' =>
       let IH := init seq' in let tail := fst IH in let head_sel := snd IH in
       ({| cell_len := 0; cell_sel := head_sel |} :: tail, false :: head_sel)
     end.
Definition initial_row : row
  := let inner := inner_initial_row seq1 in
     {| cell_len := 0; cell_sel := snd inner |} :: fst inner.

(*
Takes a char from seq2, all of seq1, the previous row, and returns
the tail of the new row, the head of the previous row,
and the head of the new row.
*)
Definition inner_update (char : B) : list A -> row -> row * cell * cell
  := fix update seq1 := fun cur => match seq1 with
     | nil => ([], row_hd cur, {| cell_len := 0; cell_sel := [] |})
     | cons a seq1' =>
       let step := update seq1' (tl cur) in let new_row_ := fst (fst step) in
       let diagc := snd (fst step) in let leftc := snd step in
       let upc := row_hd cur in
       (leftc :: new_row_, upc, cell_update diagc leftc upc a char)
     end.
Definition update_state (char : B) (cur : row) : row
  := let step := inner_update char seq1 cur in snd step :: fst (fst step).

Definition get_substring : list A -> list bool -> list A
  := fix substr seq {struct seq} := fun sel => match seq, sel with
     | [], _ | _, [] => []
     | a :: seq', true :: sel' => a :: substr seq' sel'
     | a :: seq', false :: sel' => substr seq' sel'
     end.

Definition final_cell : cell
  := let final_state := fold_right update_state initial_row seq2 in
     row_hd final_state.
Definition lcs : list A
  := get_substring seq1 (cell_sel final_cell).

Definition get_substring_StrictSubseq
  : forall seq sel, StrictSubseq (get_substring seq sel) seq
  := fix substr_subseq seq sel := match seq, sel with
     | [], _ | _, [] => nil_strict_subseq _
     | a :: seq', true :: sel' =>
       cons_cons_strict_subseq a _ _ (substr_subseq seq' sel')
     | a :: seq', false :: sel' =>
       keep_cons_strict_subseq a _ _ (substr_subseq seq' sel')
     end.
Definition lcs_StrictSubseq_seq1 : StrictSubseq lcs seq1
  := get_substring_StrictSubseq seq1 _.

(*
Define an the induction for the grid.
*)
Section lcs_rect.
Context
  (P : cell -> list A -> list B -> Type)
  (step_nil1 : forall l, P {| cell_len := 0; cell_sel := [] |} [] l)
  (step_nil2
   : forall sel a l,
     P {| cell_len := 0; cell_sel := sel |} l [] ->
     P {| cell_len := 0; cell_sel := false :: sel |} (a :: l) [])
  (step_cell_update
   : forall diag left up a b seq1 seq2,
     P diag seq1 seq2 -> P left seq1 (b :: seq2) -> P up (a :: seq1) seq2 ->
     P (cell_update diag left up a b) (a :: seq1) (b :: seq2))
.

Definition rowP : row -> list A -> list B -> Type
  := let fix rowP' seq1 := fun cur seq2 =>
       match seq1 return Type with
       | nil => unit
       | cons a seq1' => prod
         (P (row_hd (tl cur)) seq1' seq2)
         (rowP' seq1' (tl cur) seq2)
       end in
     fun cur seq1 seq2 => prod
     (P (row_hd cur) seq1 seq2)
     (rowP' seq1 cur seq2).

Definition initial_row_P : rowP initial_row seq1 []
  := let fix initP seq
      : let inner := inner_initial_row seq in
        let init := {| cell_len := 0; cell_sel := snd inner |} :: fst inner in
        rowP init seq []
      := match seq with
         | [] => (step_nil1 _, tt)
         | a :: seq' => let IH := initP seq' in
           (step_nil2 _ a seq' (fst IH), IH)
         end in
     initP seq1.

Definition update_state_P char cur seq2
  : rowP cur seq1 seq2 ->
    rowP (update_state char cur) seq1 (char :: seq2)
  := fun H =>
     let fix inner seq1
      : forall cur, rowP cur seq1 seq2 ->
        let step := inner_update char seq1 cur in
        P (snd (fst step)) seq1 seq2 *
        rowP (snd step :: fst (fst step)) seq1 (char :: seq2)
      := fun cur => match seq1 with
         | nil => fun H => (fst H, (step_nil1 _, tt))
         | cons a seq1' => fun H =>
           let step := inner_update char seq1' (tl cur) in
           let IH
            : _ *
              rowP (snd step :: fst (fst step)) seq1' (char :: seq2)
            := inner seq1' (tl cur) (snd H) in
           (fst H,
            (step_cell_update _ _ _ a char seq1' seq2
             (fst IH) (fst (snd IH)) (fst H),
             (snd IH)))
         end in
     snd (inner seq1 cur H).

Definition final_cell_P : P final_cell seq1 seq2
  := let fix iter seq2
      : rowP (fold_right update_state initial_row seq2) seq1 seq2
      := match seq2 with
         | nil => initial_row_P
         | cons char seq2' => update_state_P char _ _ (iter seq2')
         end in
     fst (iter seq2).
End lcs_rect.

Definition cell_subseq : cell -> list A -> list B -> Type
  := fun c seq1 seq2 => WeakSubseq (fun x y => R x y = true)
     (get_substring seq1 (cell_sel c)) seq2.

Definition cell_max_subseq {c1 c2 seq1 seq2}
  (H1 : cell_subseq c1 seq1 seq2) (H2 : cell_subseq c2 seq1 seq2)
  : cell_subseq (cell_max c1 c2) seq1 seq2
  := match cell_len c1 ?= cell_len c2 as cond
     return cell_subseq (match cond with Gt => _ | _ => _ end) _ _ with
     | Eq | Lt => H2
     | Gt => H1
     end.
Definition pad_cell_subseq {c a seq1 seq2} (H : cell_subseq c seq1 seq2)
  : cell_subseq (pad_cell c) (a :: seq1) seq2
  := H.
Definition inc_cell_subseq {c a seq1 b seq2}
  (aRb : R a b = true) (H : cell_subseq c seq1 seq2)
  : cell_subseq (inc_cell c) (a :: seq1) (b :: seq2)
  := cons_cons_weak_subseq _ _ _ aRb _ _ H.
Definition lift_cell_subseq {c seq1 b seq2}
  : cell_subseq c seq1 seq2 -> cell_subseq c seq1 (b :: seq2)
  := keep_cons_weak_subseq _ _ _ _.
Definition cell_update_subseq diag left up a b seq1 seq2
  (Hdiag : cell_subseq diag seq1 seq2)
  (Hleft : cell_subseq left seq1 (b :: seq2))
  (Hup : cell_subseq up (a :: seq1) seq2)
  : cell_subseq (cell_update diag left up a b) (a :: seq1) (b :: seq2)
  := let Hsides
      : cell_subseq (cell_max (pad_cell left) up) (a :: seq1) (b :: seq2)
      := cell_max_subseq (pad_cell_subseq Hleft) (lift_cell_subseq Hup) in
     (if R a b as cond
      return R a b = cond -> cell_subseq (if cond then _ else _) _ _
      then fun aRb => cell_max_subseq Hsides (inc_cell_subseq aRb Hdiag)
      else fun _ => Hsides)
     eq_refl.

Definition lcs_WeakSubseq_seq2 : WeakSubseq (fun a b => R a b = true) lcs seq2
  := final_cell_P cell_subseq (nil_weak_subseq _) (fun c a l H => H)
     cell_update_subseq.

Definition len_max n seq1 seq2
  := forall ans,
     StrictSubseq ans seq1 ->
     WeakSubseq (fun x y => R x y = true) ans seq2 ->
     length ans <= n.
Definition cell_len_max c seq1 seq2 := len_max (cell_len c) seq1 seq2.

Definition weak_subseq_nil_len_zero {R : A -> B -> Type} l
  (lsub : WeakSubseq R l nil) : length l <= 0
  := match lsub in WeakSubseq _ l nil return length l <= 0
     with nil_nil_weak_subseq _ => N.le_0_l 0 end.
Definition len_max_zero_l_nil {l} : len_max 0 l nil
  := fun ans _ => weak_subseq_nil_len_zero ans.

Definition len_max_zero_nil_l l : len_max 0 nil l
  := fun ans H _ => match H in StrictSubseq ans nil return length ans <= 0
     with nil_nil_strict_subseq => N.le_0_l 0 end.

Definition cell_max_len1 c1 c2 : cell_len c1 <= cell_len (cell_max c1 c2)
  := match cell_len c1 ?= cell_len c2 as cond
     return
       cell_len c1 ?= cell_len c2 = cond ->
       cell_len c1 <= cell_len (match cond with Gt => _ | _ => _ end)
     with
     | Eq | Lt => fun H1 (H2 : _ ?= cell_len c2 = _) =>
       let H := eq_trans (eq_sym H1) H2 in ltac:(discriminate)
     | Gt => fun _ => N.le_refl _
     end eq_refl.
Definition cell_max_len2 c1 c2 : cell_len c2 <= cell_len (cell_max c1 c2)
  := match cell_len c1 ?= cell_len c2 as cond
     return
       cell_len c1 ?= cell_len c2 = cond ->
       cell_len c2 <= cell_len (match cond with Gt => _ | _ => _ end)
     with
     | Eq | Lt => fun _ => N.le_refl _
     | Gt => fun (H : cell_len c1 > cell_len c2) =>
       N.lt_le_incl _ _ (N.gt_lt _ _ H)
     end eq_refl.
Definition cell_update_len_left {diag left up a b}
  : cell_len left <= cell_len (cell_update diag left up a b)
  := let left_leq_sides
      : cell_len left <= cell_len (cell_max (pad_cell left) up)
      := cell_max_len1 (pad_cell left) up in
     if R a b as cond return _ <= cell_len (if cond then _ else _)
     then N.le_trans _ _ _ left_leq_sides (cell_max_len1 _ _)
     else left_leq_sides.
Definition cell_update_len_up {diag left up a b}
  : cell_len up <= cell_len (cell_update diag left up a b)
  := let up_leq_sides
      : cell_len up <= cell_len (cell_max (pad_cell left) up)
      := cell_max_len2 (pad_cell left) up in
     if R a b as cond return _ <= cell_len (if cond then _ else _)
     then N.le_trans _ _ _ up_leq_sides (cell_max_len1 _ _)
     else up_leq_sides.
Definition cell_update_len_diag {diag left up a b} (aRb : R a b = true)
  : N.succ (cell_len diag) <= cell_len (cell_update diag left up a b)
  := match eq_sym aRb in _ = aRb return _ <= cell_len (if aRb then _ else _)
     with eq_refl => cell_max_len2 _ (inc_cell diag) end.

Definition cell_update_len_max diag left up a b seq1 seq2
  : cell_len_max diag seq1 seq2 ->
    cell_len_max left seq1 (b :: seq2) -> cell_len_max up (a :: seq1) seq2 ->
    cell_len_max (cell_update diag left up a b) (a :: seq1) (b :: seq2)
  := fun Hdiag Hleft Hup ans H1 H2 =>
     match H1 in StrictSubseq ans (a :: seq1)
     return
       WeakSubseq _ ans (b :: seq2) ->
       cell_len_max diag seq1 seq2 ->
       cell_len_max left seq1 (b :: seq2) -> cell_len_max up (a :: seq1) seq2 ->
       length ans <= cell_len (cell_update diag left up a b)
     with
     | keep_cons_strict_subseq a ans seq1 IH1 => fun H2 _ Hleft _ =>
       let less_left : length ans <= cell_len left := Hleft ans IH1 H2 in
       N.le_trans _ _ _ less_left cell_update_len_left
     | cons_cons_strict_subseq a ans' seq1 IH1 => fun H2 =>
       match H2 in WeakSubseq _ (a :: ans') (b :: seq2)
       return
         StrictSubseq ans' seq1 ->
         cell_len_max diag seq1 seq2 ->
         cell_len_max left seq1 (b :: seq2) ->
         cell_len_max up (a :: seq1) seq2 ->
         length (a :: ans') <= cell_len (cell_update diag left up a b)
       with
       | keep_cons_weak_subseq _ b (a :: ans') seq2 IH2 => fun IH1 _ _ Hup =>
         let less_up : length (a :: ans') <= cell_len up
          := Hup _ (cons_cons_strict_subseq a ans' seq1 IH1) IH2 in
         N.le_trans _ _ _ less_up cell_update_len_up
       | cons_cons_weak_subseq _ a b aRb ans' seq2 IH2 => fun IH1 Hdiag _ _ =>
         let less_diag : length (a :: ans') <= N.succ (cell_len diag)
          := proj1 (N.succ_le_mono _ _) (Hdiag _ IH1 IH2) in
         N.le_trans _ _ _ less_diag (cell_update_len_diag aRb)
       end IH1
     end H2 Hdiag Hleft Hup.

Definition lcs_len_max : len_max (cell_len final_cell) seq1 seq2
  := final_cell_P cell_len_max
     len_max_zero_nil_l (fun _ _ _ _ => len_max_zero_l_nil)
     cell_update_len_max.

Definition cell_len_correct c seq1
  := cell_len c = length (get_substring seq1 (cell_sel c)).
Definition cell_max_len_correct {c1 c2 seq1}
  (H1 : cell_len_correct c1 seq1) (H2 : cell_len_correct c2 seq1)
  : cell_len_correct (cell_max c1 c2) seq1
  := match cell_len c1 ?= cell_len c2 as cond
     return cell_len_correct (match cond with Gt => _ | _ => _ end) _ with
     | Eq | Lt => H2
     | Gt => H1
     end.
Definition pad_cell_len_correct {c a seq1} (H : cell_len_correct c seq1)
  : cell_len_correct (pad_cell c) (a :: seq1)
  := H.
Definition inc_cell_len_correct {c a seq1} (H : cell_len_correct c seq1)
  : cell_len_correct (inc_cell c) (a :: seq1)
  := f_equal N.succ H.
Definition cell_update_len_correct diag left up a b seq1
  (Hdiag : cell_len_correct diag seq1)
  (Hleft : cell_len_correct left seq1)
  (Hup : cell_len_correct up (a :: seq1))
  : cell_len_correct (cell_update diag left up a b) (a :: seq1)
  := let Hsides : cell_len_correct (cell_max (pad_cell left) up) (a :: seq1)
      := cell_max_len_correct (pad_cell_len_correct Hleft) Hup in
     if R a b as cond
     return cell_len_correct (if cond then _ else _) _
     then cell_max_len_correct Hsides (inc_cell_len_correct Hdiag)
     else Hsides.
Definition lcs_len_correct : cell_len final_cell = length lcs
  := final_cell_P
     (fun c seq1 _ => cell_len_correct c seq1)
     (fun _ => eq_refl) (fun c a l H => H)
     (fun diag left up a b seq1 seq2 =>
      cell_update_len_correct diag left up a b seq1).

Definition lcs_max : len_max (length lcs) seq1 seq2
  := eq_rect _ (fun n => len_max n seq1 seq2) lcs_len_max _ lcs_len_correct.

Definition inner_lcs_LongestCommonSubsequence
  : LongestCommonSubsequence (fun a b => R a b = true) seq1 seq2 lcs
  := (lcs_StrictSubseq_seq1, lcs_WeakSubseq_seq2, lcs_max).

End inner.
End inner.

Definition lcs_LongestCommonSubsequence {A B} (R : A -> B -> bool) s t
  : LongestCommonSubsequence (fun a b => R a b = true) s t (lcs R s t)
  := inner_lcs_LongestCommonSubsequence R s t.

(*
At this point, we have defined a function that computes the longest subsequence
of s that can be matched with a subsequence of t such that R holds between the
two sequences.

If we take R to be an equivalence relation, we can recover the usual version.
*)

Definition UsualLongestCommonSubsequence {A} (Aeq : A -> A -> Type) s t ans
  : Type
  := WeakSubseq Aeq ans s * WeakSubseq Aeq ans t *
     (forall ans', WeakSubseq Aeq ans' s -> WeakSubseq Aeq ans' t ->
      length ans' <= length ans).

Module Import inner_usual.
Section usual_lcs.
Context
  (A : Type)
  {Asetoid : Setoid A}
  {Adec : EqDec Asetoid}.
Context (seq1 seq2 : list A).

Definition usual_lcs : list A
  := lcs (fun a1 a2 => a1 ==b a2) seq1 seq2.
Definition usual_lcs_subseq1
  : WeakSubseq equiv usual_lcs seq1
  := strict_to_weak _ reflexivity (lcs_StrictSubseq_seq1 _ seq1 seq2).
Definition usual_lcs_subseq2
  : WeakSubseq equiv usual_lcs seq2
  := weak_to_weak _ _
     (fun a b => match a == b as cond
      return (if cond then true else false) = true -> a == b
      with left H => fun _ => H | right _ => fun XX => ltac:(discriminate) end)
     (lcs_WeakSubseq_seq2 _ seq1 seq2).

Definition ans'
  : forall ans'_ seq1 : list A, WeakSubseq equiv ans'_ seq1 -> list A
  := fix ans' ans'_ seq1 ans'_sub1 : list A :=
     match ans'_sub1 with
     | nil_nil_weak_subseq _ => nil
     | keep_cons_weak_subseq _ _ _ _ IH => ans' _ _ IH
     | cons_cons_weak_subseq _ _ b _ _ _ IH => b :: ans' _ _ IH
     end.
Definition ans'_length_eq
  : forall ans'_ seq1 ans'_sub1,
    length (ans' ans'_ seq1 ans'_sub1) = length ans'_
  := fix ans'_len ans'_ seq1 ans'_sub1 :=
     match ans'_sub1 with
     | nil_nil_weak_subseq _ => eq_refl
     | keep_cons_weak_subseq _ _ _ _ IH => ans'_len _ _ IH
     | cons_cons_weak_subseq _ _ _ _ _ _ IH => f_equal N.succ (ans'_len _ _ IH)
     end.
Definition equiv_to_eqtrue a1 a2 : a1 == a2 -> a1 ==b a2 = true
  := match a1 == a2 as cond
     return a1 == a2 -> (if cond then true else false) = true
     with
     | left H => fun _ => eq_refl
     | right nH => fun H => False_rect _ (nH H)
     end.
Definition ans'sub1
  : forall ans'_ seq1 ans'_sub1,
    StrictSubseq (ans' ans'_ seq1 ans'_sub1) seq1
  := fix ans'sub1 ans'_ seq1 ans'_sub1 := match ans'_sub1 with
     | nil_nil_weak_subseq _ => nil_nil_strict_subseq
     | keep_cons_weak_subseq _ _ _ _ IH =>
       keep_cons_strict_subseq _ _ _ (ans'sub1 _ _ IH)
     | cons_cons_weak_subseq _ _ _ _ _ _ IH =>
       cons_cons_strict_subseq _ _ _ (ans'sub1 _ _ IH)
     end.
Definition ans'sub2
  : forall ans'_ seq1 ans'_sub1 seq2 (ans'_sub2 : WeakSubseq equiv ans'_ seq2),
    WeakSubseq (fun a1 a2 => a1 ==b a2 = true) (ans' ans'_ seq1 ans'_sub1) seq2
  := fix ans'sub2 ans'_ seq1 ans'_sub1 :=
     match ans'_sub1 in WeakSubseq _ ans'_ seq1
     return
       forall seq2, WeakSubseq equiv ans'_ seq2 ->
       WeakSubseq _ (ans' ans'_ seq1 ans'_sub1) seq2
     with
     | nil_nil_weak_subseq _ => fun seq2 ans'_seq2 => nil_weak_subseq _ _
     | keep_cons_weak_subseq _ _ _ _ IH => ans'sub2 _ _ IH
     | cons_cons_weak_subseq _ a b a_equiv_b l1 l2 IH => fun seq2 ans'_sub2 =>
       let IH' := ans'sub2 _ _ IH in
       (fix inner a l1 seq2 (ans'_sub2 : WeakSubseq _ (a :: l1) seq2)
        : forall l2 IH, a == b ->
          (forall seq, WeakSubseq equiv l1 seq ->
           WeakSubseq _ (ans' l1 l2 IH) seq) ->
          WeakSubseq _ (b :: ans' l1 l2 IH) seq2
        := match ans'_sub2 in WeakSubseq _ (a :: l1) seq2
           return
             forall l2 IH, a == b ->
             (forall seq, WeakSubseq equiv l1 seq ->
              WeakSubseq _ (ans' l1 l2 IH) seq) ->
             WeakSubseq _ (b :: ans' l1 l2 IH) seq2
           with
           | cons_cons_weak_subseq _ _ _ bR _ _ IH => fun l2 IH1 a_equiv_b IH' =>
             cons_cons_weak_subseq _ _ _
             (equiv_to_eqtrue _ _ (transitivity (symmetry a_equiv_b) bR))
             _ _ (IH' _ IH)
           | keep_cons_weak_subseq _ w (a :: l1) seq2' IH =>
             fun l2 IH1 a_equiv_b IH' =>
             keep_cons_weak_subseq _ w (b :: ans' _ _ IH1) seq2'
             (inner _ _ _ IH _ _ a_equiv_b IH')
           end) a l1 seq2 ans'_sub2 l2 IH a_equiv_b IH'
       : WeakSubseq (fun a1 a2 => a1 ==b a2 = true) (b :: ans' l1 l2 IH) seq2
     end.

Definition usual_lcs_max ans'_
  (ans'_sub1 : WeakSubseq equiv ans'_ seq1)
  (ans'_sub2 : WeakSubseq equiv ans'_ seq2)
  : length ans'_ <= length usual_lcs
  := eq_rect _ (fun n => n <= length usual_lcs)
     (lcs_max _ _ _ _ (ans'sub1 _ _ _) (ans'sub2 _ _ _ _ ans'_sub2))
     _ (ans'_length_eq ans'_ seq1 ans'_sub1).

Definition inner_usual_lcs_UsualLongestCommonSubsequence
  : UsualLongestCommonSubsequence (A:=A) equiv seq1 seq2 usual_lcs
  := (usual_lcs_subseq1, usual_lcs_subseq2, usual_lcs_max).

End usual_lcs.
End inner_usual.

Definition usual_lcs_UsualLongestCommonSubsequence
  : forall (A : Type) {Asetoid : Setoid A} {Adec : EqDec Asetoid},
    forall (s t : list A),
    UsualLongestCommonSubsequence (A:=A) equiv s t (usual_lcs A s t)
  := inner_usual_lcs_UsualLongestCommonSubsequence.
