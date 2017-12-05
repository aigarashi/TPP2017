prelude
import init.data.list.lemmas
import init.data.nat.lemmas

variables {α : Type} {β : Type}
open list nat prod well_founded
namespace list

lemma strong_ind_help {A : Type} (f : A → ℕ) {P : A → Prop}
(H : ∀ n : ℕ, ∀ a : A, f a ≤ n → P a) :
∀ a : A,  P a :=
begin
intro a, apply (H (f a)), reflexivity
end

lemma funcToNat_strong_ind {A : Type} {f : A → ℕ} {P : A → Prop}
(H0 : ∀ a : A, f a = 0 → P a)
(Hn : ∀ n : ℕ, (∀ b : A, f b ≤ n → P b) → ∀ c : A, f c = n+1 → P c) :
∀ a : A, P a :=
begin
intro a,
apply (strong_ind_help f),
intro n,
induction n with n H',
    {intros a0 Ha0, apply H0,
    assert Temp : forall x: nat,  x ≤ 0 → x = 0,
        {intros x H, cases H, {trivial}},
    apply Temp, assumption},
    {intros b h,
    assert hm : f b = succ n ∨ f b < succ n, apply nat.eq_or_lt_of_le h,
    apply or.elim hm,
        apply Hn, apply H',
        intro h, assert hk : f b ≤ n, apply le_of_lt_succ, apply h,
        apply H', apply hk},
end

definition subseq   : list α → list α → Prop
| []        _       := true
| (a::A')   []      := false
| (a::A')   (b::B') := ((a=b) ∧ (subseq A' B')) ∨ (subseq (a::A') B')

lemma nil_subseq (A : list α) : subseq [] A :=
begin
cases A with a A',
trivial, unfold subseq, trivial
end

lemma subseq_nil (A : list α) : subseq A [] ↔ A = [] :=
begin
apply iff.intro,
    {cases A with a A',
        {intro h, apply eq.refl},
        {unfold subseq, apply false.elim}},
    {intro h, rw h, apply nil_subseq}
end

lemma subseq_self (A : list α) : subseq A A :=
begin
induction A with a A',
    {apply nil_subseq},
    {unfold subseq, apply or.intro_left, apply and.intro, apply rfl, apply ih_1}
end

lemma tail_subseq (a : α) (A' : list α): subseq A' (a::A') :=
begin
induction A' with a' A'',
    {apply nil_subseq},
    {unfold subseq, apply or.intro_right, apply subseq_self (a'::A'')}
end

lemma subseq_implies_leq (A B : list α) : (subseq A B) → length (A) ≤ length (B) :=
begin
revert A,
induction B with b B',
    {intros A h,
    assert h1 : A = [], revert h, apply iff.elim_left (subseq_nil A),
    rw h1},
    {intro A,
    cases A with a A',
        {intro h, unfold length, apply zero_le},
        {unfold subseq, intro h, apply or.elim h,
            {intro h, unfold length, apply succ_le_succ,
            apply ih_1 A', apply and.right h},
            {intro h, apply le_succ_of_le,
            apply ih_1 (a::A'), apply h}}}
end

lemma subseq_trans (X Y Z : list α) : (subseq X Y) → (subseq Y Z) → (subseq X Z) :=
begin
revert X Y,
induction Z with z Z',
    {intros X Y hXY hY,
    unfold subseq,
    assert h1 : Y = [], revert hY, apply iff.elim_left (subseq_nil Y),
    assert h2 : X = [], revert hXY, rw h1, apply iff.elim_left (subseq_nil X),
    rw h2, unfold subseq, trivial},
    {intros X Y, cases Y with y Y',
        {intros h1 h2,
        assert h3 : X = [], revert h1, apply iff.elim_left (subseq_nil X),
        rw h3, apply nil_subseq},
    {cases X with x X',
        {intros, apply nil_subseq},
        {unfold subseq, intros h1 h2, apply or.elim h1,
            {intro hXY, apply or.elim h2,
                {intro hYZ, apply or.intro_left, apply and.intro,
                    apply eq.trans, apply and.left hXY, apply and.left hYZ,
                    apply ih_1 X' Y' (and.right hXY) (and.right hYZ)},
                {intro hYZ', apply or.intro_right,
                apply ih_1 (x::X') (y::Y'), apply or.intro_left, apply hXY, apply hYZ'}},
            {intro hXY', apply or.elim h2,
                {intro h5, apply or.intro_right,
                apply ih_1 (x::X') Y' (hXY') (and.right h5)},
                {intro hYZ', apply or.intro_right,
                apply ih_1 (x::X') Y',
                apply hXY', apply ih_1 Y' (y::Y'), apply tail_subseq, apply hYZ'}}}}}
end

lemma subseq_iff_tail_subseq (x : α) (X Y : list α) : subseq (x::X) (x::Y) ↔ subseq X Y :=
begin
apply iff.intro,
    {unfold subseq, intro h, apply or.elim h,
        {intro h2, apply and.right h2},
        {intro h2, apply subseq_trans, apply tail_subseq x, apply h2},},
    {intro h, unfold subseq, apply or.intro_left, apply and.intro, apply rfl, apply h}
end

definition com_subseq (V X Y: list α) := (subseq V X) ∧ (subseq V Y)

lemma nil_com_subseq (X Y : list α) : com_subseq [] X Y :=
begin
unfold com_subseq, apply and.intro, apply nil_subseq, apply nil_subseq
end

lemma com_subseq_nil_left (V X: list α) : com_subseq V [] X ↔ V = [] :=
begin
apply iff.intro,
{intro h, apply iff.elim_left (subseq_nil V), apply and.left h},
{intro h, rw h, apply nil_com_subseq}
end

lemma com_subseq_nil_right (V X : list α) : com_subseq V X [] ↔ V = [] :=
begin
apply iff.intro,
{intro h, apply iff.elim_left (subseq_nil V), apply and.right h},
{intro h, rw h, apply nil_com_subseq}
end

lemma com_subseq_tail_tail (x: α) (V X Y : list α) : com_subseq (x::V) (x::X) (x::Y) ↔ com_subseq V X Y :=
begin
apply iff.intro,
    {intro h,
    unfold com_subseq, apply and.intro,
        {apply iff.elim_left (subseq_iff_tail_subseq x V X), apply and.left h},
        {apply iff.elim_left (subseq_iff_tail_subseq x V Y), apply and.right h}},
    {intro h,
    unfold com_subseq, apply and.intro,
        {unfold subseq, apply or.intro_left, apply and.intro, refl, apply and.left h},
        {unfold subseq, apply or.intro_left, apply and.intro, refl, apply and.right h},}
end

definition longest_com (V X Y : list α) := (com_subseq V X Y) ∧ (∀ ⦃W : list α⦄, (com_subseq W X Y) → (length W ≤ length V))

lemma nil_longest_com_left (X : list α) : longest_com [] [] X :=
begin
apply and.intro,
    {apply nil_com_subseq},
    {intros W hW,
    assert hW1 : W = [], revert hW, apply iff.elim_left (com_subseq_nil_left W X),
    rw hW1},
end

lemma nil_longest_com_right (X : list α) : longest_com [] X [] :=
begin
apply and.intro,
    {apply nil_com_subseq},
    {intros W hW,
    assert hW1 : W = [], revert hW, apply iff.elim_left (com_subseq_nil_right W X),
    rw hW1}
end

lemma longest_com_tail (x : nat) (V X' Y' : list nat) : longest_com (x::V) (x::X') (x::Y') ↔ longest_com V X' Y' :=
begin
    apply iff.intro,
        {intro h, unfold longest_com, apply and.intro,
            {apply iff.elim_left (com_subseq_tail_tail x V X' Y'), apply and.left h},
            {intros W h1,
            apply nat.le_of_add_le_add_left, rw -add_comm, rw add_comm 1 (length V),
            change length (x::W) ≤ length (x::V),
            apply and.right h, apply iff.elim_right (com_subseq_tail_tail x W X' Y'), apply h1},},
        {intro h, unfold longest_com, apply and.intro,
            {apply iff.elim_right (com_subseq_tail_tail x V X' Y'), apply and.left h},
            {intros W h1,
            cases W with w W',
            begin -- W = []
                unfold length, apply zero_le,
                end,
            begin -- W = (w::W')
                cases decidable.em (w=x),
                begin -- w=x,
                    revert h1, rw -a, intro h1,
                    unfold length, apply succ_le_succ, apply and.right h, apply iff.elim_left (com_subseq_tail_tail w W' X' Y'), apply h1,
                    end,
                begin -- w≠x
                    note hWX := and.left h1,
                    note hWY := and.right h1,
                    unfold length, apply succ_le_succ, apply and.right h, apply and.intro,
                        {apply subseq_trans, apply (tail_subseq w W'),
                        revert hWX, unfold subseq, intro hWX, apply or.elim hWX,
                            {intro h2, apply false.elim, apply iff.elim_left (not_and_self (w=x)), apply and.intro, apply a, apply and.left h2},
                            {intro h2, apply h2}},
                        {apply subseq_trans, apply (tail_subseq w W'),
                        revert hWY, unfold subseq, intro hWY, apply or.elim hWY,
                            {intro h2, apply false.elim, apply iff.elim_left (not_and_self (w=x)), apply and.intro, apply a, apply and.left h2},
                            {intro h2, apply h2},}
                    end,
            end,},},
end

definition longer : list α → list α → list α
| X Y := if length X ≤ length Y then Y else X

-- If well-founded recursion is enabled, use this defintion for com' instead :

-- definition com : list nat → list nat → list nat
-- | []      _       := []
-- | _       []      := []
-- | (x::X') (y::Y') := if x = y then (x :: (com X' Y')) else longer (com (x::X') Y') (com X' (y:: Y'))

definition com (comX : list nat → list nat) (x : nat) (X : list nat) : list nat → list nat
| []     := []
| (y::Y) := if x = y then x :: comX Y else longer (com Y) (comX (y :: Y))

definition com' : list nat → list nat → list nat
| []    _   := []
| (x::X) Y  := com (com' X) x X Y

lemma com'_nil_left (X : list nat) : com' [] X = [] :=
begin
unfold com', trivial
end

lemma com'_nil_right (X : list nat) : com' X [] = [] :=
begin
cases X with x X',
    {unfold com, trivial},
    {unfold com, unfold com', trivial}
end

definition pair_length (Z : list α × list β) := length (fst Z) + length (snd Z)

lemma com'_implies_subseq_left_prod (Z : list nat × list nat) : subseq (com' (fst Z) (snd Z)) (fst Z) :=
begin
assert H0 : ∀ Z : list ℕ × list ℕ, pair_length Z = 0 → subseq (com' (fst Z) (snd Z)) (fst Z),
    intros Z1 hlZ,
    cases Z1 with X Y,
    assert h: X = [], apply eq_nil_of_length_eq_zero, apply eq_zero_of_add_eq_zero_right hlZ,
    rw h, rw com'_nil_left, apply nil_subseq,
assert Hn : ∀ n : ℕ, (∀ Z : list ℕ × list ℕ, pair_length Z ≤ n → subseq (com' (fst Z) (snd Z)) (fst Z))
                        → (∀ Z : list ℕ × list ℕ, pair_length Z = n+1 → subseq (com' (fst Z) (snd Z)) (fst Z)),
{intros n hind Z hlZ,
cases Z with X Y, cases X with x X',
    {rw com'_nil_left, apply nil_subseq},
    {cases Y with y Y',
        {rw com'_nil_right, apply nil_subseq},
        {change subseq (com' (x::X') (y::Y')) (x::X'),
        unfold com', unfold com,
        cases decidable.em (x=y) with hxy hnxy,
            {rw if_pos hxy, unfold subseq, apply or.intro_left, apply and.intro, refl,
            apply hind (X', Y'),
                assert hlXY'' : pair_length (X', Y') = n - 1,
                    revert hlZ, unfold pair_length, change length (x::X') + length (y::Y') = n + 1 → length X' + length Y' = n - 1, unfold length, intro h1,
                    assert h2 : length X' + 1 + length Y' = n, revert h1, rw -add_assoc, apply nat.add_right_cancel,
                    rw -h2, rw add_assoc, rw (add_comm 1 (length Y')), rw -add_assoc, trivial,
                rw hlXY'', rw sub_one, rw pred_le_iff_true, trivial},
            {rw if_neg hnxy, change subseq (longer (com' (x::X') Y') (com' X' (y::Y'))) (x::X'),
            unfold longer, cases decidable.em (length (com' (x::X') Y') ≤ length (com' X' (y::Y'))),
                {rw if_pos a, apply subseq_trans,
                    apply hind (X', (y::Y')), apply le_of_eq, revert hlZ, unfold pair_length, unfold length, simp, rw add_comm, apply nat.add_right_cancel,
                    apply tail_subseq},
                {rw if_neg a, apply hind ((x::X'), Y'), apply le_of_eq, revert hlZ, unfold pair_length, unfold length, rw -add_assoc, apply add_right_cancel},
                },
            },
        },
    },
apply funcToNat_strong_ind H0 Hn
end

lemma com'_implies_subseq_right_prod (Z : list nat × list nat) : subseq (com' (fst Z) (snd Z)) (snd Z) :=
begin
assert H0 : ∀ Z : list ℕ × list ℕ, pair_length Z = 0 → subseq (com' (fst Z) (snd Z)) (snd Z),
    intros Z1 hlZ,
    cases Z1 with X Y,
    assert h: X = [], apply eq_nil_of_length_eq_zero, apply eq_zero_of_add_eq_zero_right hlZ,
    rw h, rw com'_nil_left, apply nil_subseq,
assert Hn : ∀ n : ℕ, (∀ Z : list ℕ × list ℕ, pair_length Z ≤ n → subseq (com' (fst Z) (snd Z)) (snd Z))
                        → (∀ Z : list ℕ × list ℕ, pair_length Z = n+1 → subseq (com' (fst Z) (snd Z)) (snd Z)),
{intros n hind Z hlZ,
cases Z with X Y, cases X with x X',
    {rw com'_nil_left, apply nil_subseq},
    {cases Y with y Y',
        {rw com'_nil_right, apply nil_subseq},
        {change subseq (com' (x::X') (y::Y')) (y::Y'),
        unfold com', unfold com,
        cases decidable.em (x=y) with hxy hnxy,
            {rw if_pos hxy, unfold subseq, apply or.intro_left, apply and.intro, apply hxy,
            apply hind (X', Y'),
                assert hlXY'' : pair_length (X', Y') = n - 1,
                    revert hlZ, unfold pair_length, change length (x::X') + length (y::Y') = n + 1 → length X' + length Y' = n - 1, unfold length, intro h1,
                    assert h2 : length X' + 1 + length Y' = n, revert h1, rw -add_assoc, apply nat.add_right_cancel,
                    rw -h2, rw add_assoc, rw (add_comm 1 (length Y')), rw -add_assoc, trivial,
                rw hlXY'', rw sub_one, rw pred_le_iff_true, trivial},
            {rw if_neg hnxy, change subseq (longer (com' (x::X') Y') (com' X' (y::Y'))) (y::Y'),
            unfold longer, cases decidable.em (length (com' (x::X') Y') ≤ length (com' X' (y::Y'))),
                {rw if_pos a, apply hind (X', (y::Y')), apply le_of_eq, revert hlZ, unfold pair_length, unfold length, simp, rw add_comm, apply nat.add_right_cancel},                
                {rw if_neg a, apply subseq_trans, apply hind ((x::X'), Y'), apply le_of_eq, revert hlZ, unfold pair_length, unfold length, rw -add_assoc, apply add_right_cancel,
                apply tail_subseq},
                },
            },
        },
    },
apply funcToNat_strong_ind H0 Hn
end

lemma com'_implies_subseq_left (X Y : list nat) : subseq (com' X Y) X :=
begin
apply com'_implies_subseq_left_prod (X, Y)
end

lemma com'_implies_subseq_right (X Y : list nat) : subseq (com' X Y) Y :=
begin
apply com'_implies_subseq_right_prod (X, Y)
end

lemma com'_implies_com_subseq (X Y : list nat) : com_subseq (com' X Y) X Y :=
begin
apply and.intro, apply com'_implies_subseq_left, apply com'_implies_subseq_right
end

end list