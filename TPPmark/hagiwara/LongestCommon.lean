prelude
import init.data.list.lemmas
import init.data.nat.lemmas
import .Subsequences

variables {α : Type} {β : Type}
open list nat prod
namespace list

definition longest_com' (X Y : list ℕ) := length (com' X Y)

theorem com'_is_longest_com (Z : list ℕ × list ℕ) : longest_com (com' (fst Z) (snd Z)) (fst Z) (snd Z) :=
begin
assert H0 : ∀ Z : list ℕ × list ℕ, pair_length Z = 0 → longest_com (com' (fst Z) (snd Z)) (fst Z) (snd Z),
    {intro Z1, cases Z1 with X Y,
    unfold pair_length, intro h,
    assert h1 : X = [], apply eq_nil_of_length_eq_zero, apply eq_zero_of_add_eq_zero_right h,
    rw h1, rw com'_nil_left, apply nil_longest_com_left},
assert Hn : ∀ n : ℕ, (∀ Z : list ℕ × list ℕ, pair_length Z ≤ n → longest_com (com' (fst Z) (snd Z)) (fst Z) (snd Z))
                     → ∀ Z : list ℕ × list ℕ, pair_length Z = n+1 → longest_com (com' (fst Z) (snd Z)) (fst Z) (snd Z),
{intros n hind Z hlZ,
    cases Z with X Y,
        change longest_com (com' X Y) X Y,
        cases X with x X',
            {rw com'_nil_left, apply nil_longest_com_left},
            {cases Y with y Y',
                {rw com'_nil_right, apply nil_longest_com_right},
                {cases decidable.em (x=y) with hxy hnxy,
                    {rw -hxy,
                    assert hlXY'' : pair_length (X', Y') ≤ n,
                        {revert hlZ, unfold pair_length, unfold length, intro h1,
                        assert h2 : length X' + 1 + length Y' = n, revert h1, rw -add_assoc, apply nat.add_right_cancel,
                        rw -h2, rw add_assoc, rw (add_comm 1 (length Y')), rw -add_assoc,
                        change length X' + length Y' ≤ length X' + length Y' + 1, apply le_succ},
                    assert hcom' : com' (x::X') (x::Y') = x::(com' X' Y'), unfold com', unfold com, rw if_pos (eq.refl x),
                    rw hcom', apply iff.elim_right (longest_com_tail x (com' X' Y') X' Y'),
                    apply hind (X', Y'), apply hlXY''},
                    {unfold longest_com, apply and.intro,
                        {apply com'_implies_com_subseq},
                        {intros W h, 
                        cases W with w W',
                            {unfold length, apply zero_le},
                            {unfold com', unfold com, rw if_neg hnxy,
                            change length (w::W') ≤ length (longer (com' (x::X') Y') (com' X' (y::Y'))), unfold longer,
                            cases decidable.em (length (com' (x::X') Y') ≤ length (com' X' (y::Y'))) with hle hg,
                            {rw if_pos hle,
                            cases decidable.em (x=w) with hxw hnxw,
                                {assert hlongX'Y : longest_com (com' (x::X') Y') (x::X') Y',
                                    apply hind ((x::X'), Y'), apply le_of_eq, revert hlZ, unfold pair_length, unfold length, rw -add_assoc, apply add_right_cancel,
                                assert hW : com_subseq (w::W') (x::X') Y', apply and.intro, apply and.left h, apply or.elim (and.right h),
                                    intro h2, apply absurd, apply (eq.trans hxw (and.left h2)), apply hnxy,
                                    intro h2, apply h2,
                                assert hWle : length (w::W') ≤ length (com' (x::X') Y'), note h2 := and.right hlongX'Y, apply h2, apply hW,
                                apply le_trans, apply hWle, apply hle},
                                {assert hlongXY' : longest_com (com' X' (y::Y')) X' (y::Y'),
                                    apply hind (X', (y::Y')), apply le_of_eq, revert hlZ, unfold pair_length, unfold length, simp, rw add_comm, intro hlZ, apply add_right_cancel, apply hlZ,
                                assert hW : com_subseq (w::W') X' (y::Y'), apply and.intro,
                                    note h1 := and.left h, revert h1, unfold subseq, intro h1, apply or.elim h1,
                                        intro h2, apply absurd, apply (eq.symm (and.left h2)), apply hnxw,
                                        intro h2, apply h2,
                                    apply and.right h,
                                note h2 := and.right hlongXY', apply h2, apply hW},},
                            {rw if_neg hg,
                            cases decidable.em (x=w) with hxw hnxw,
                                {assert hlongX'Y : longest_com (com' (x::X') Y') (x::X') Y',
                                    apply hind ((x::X'), Y'), apply le_of_eq, revert hlZ, unfold pair_length, unfold length, rw -add_assoc, apply add_right_cancel,
                                assert hW : com_subseq (w::W') (x::X') Y', apply and.intro, apply and.left h, apply or.elim (and.right h),
                                    intro h2, apply absurd, apply (eq.trans hxw (and.left h2)), apply hnxy,
                                    intro h2, apply h2,
                                assert hWle : length (w::W') ≤ length (com' (x::X') Y'), note h2 := and.right hlongX'Y, apply h2, apply hW,
                                apply hWle},
                                {assert hlongXY' : longest_com (com' X' (y::Y')) X' (y::Y'),
                                    apply hind (X', (y::Y')), apply le_of_eq, revert hlZ, unfold pair_length, unfold length, simp, rw add_comm, intro hlZ, apply add_right_cancel, apply hlZ,
                                assert hW : com_subseq (w::W') X' (y::Y'), apply and.intro,
                                    note h1 := and.left h, revert h1, unfold subseq, intro h1, apply or.elim h1,
                                        intro h2, apply absurd, apply (eq.symm (and.left h2)), apply hnxw,
                                        intro h2, apply h2,
                                    apply and.right h,
                                assert hl : length (com' X' (y::Y')) ≤ length (com' (x::X') Y'), apply le_of_not_le, apply hg, 
                                note h2 := and.right hlongXY',
                                apply le_trans, apply h2, apply hW, apply hl
                                }}}}}}}},
apply funcToNat_strong_ind H0 Hn
end

end list