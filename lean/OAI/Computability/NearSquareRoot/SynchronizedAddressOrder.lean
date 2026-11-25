import OAI.Computability.NearSquareRoot.SynchronizedAddress
import Mathlib.Data.List.Sort

/-! # Occupied tape addresses are traversed in mixed-radix order

Widen each axis digit from its actual cyclic range to its padded dyadic range.
This preserves the ordering of the mixed-radix rank. Thus a streaming filter
testing axis validity visits the digits in their original order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

/-- Extend each mixed-radix digit to the larger radix with the same value;
the higher digits are decoded by successive quotient operations. -/
def widenRank : (d : ℕ) → (Fin d → ℕ) → (Fin d → ℕ) → ℕ → ℕ
  | 0, _, _, x => x
  | d+1, a, b, x => x % a 0 + b 0 * widenRank d (fun i => a i.succ) (fun i => b i.succ) (x / a 0)

theorem widenRank_strictMono {d : ℕ} (a b : Fin d → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, a i ≤ b i) : StrictMono (widenRank d a b) := by
  induction d with
  | zero => exact fun _ _ h => h
  | succ d ih =>
    intro x y hxy
    have ih' := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => ha i.succ) (fun i => hb i.succ)
    simp only [widenRank]
    have hdiv := Nat.div_le_div_right (c := a 0) hxy.le
    rcases hdiv.eq_or_lt with he | he
    · rw [he]
      exact Nat.add_lt_add_right (by
        have hx := Nat.mod_add_div x (a 0)
        have hy := Nat.mod_add_div y (a 0)
        rw [he] at hx; omega) _
    · have hm := Nat.mod_lt x (ha 0)
      have ht := Nat.mul_le_mul_left (b 0) (ih' he : _ + 1 ≤ _)
      rw [Nat.mul_succ] at ht
      have h₀ := hb 0
      omega

private theorem rank_head {d : ℕ} {a : Fin (d+1) → ℕ} (x : (i : Fin (d+1)) → Fin (a i)) :
    (finPiFinEquiv x).val = (x 0).val + a 0 * (finPiFinEquiv (fun i => x i.succ)).val := by
  simp only [finPiFinEquiv_apply]
  rw [Fin.sum_univ_succ]
  apply congrArg₂ Nat.add
  · change (x 0).val * (∏ j : Fin 0, a (Fin.castLE (by omega) j)) = _
    simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (x i.succ).val * (∏ j : Fin (i.val+1), a (Fin.castLE i.succ.isLt.le j)) = _
  rw [Fin.prod_univ_succ]
  change (x i.succ).val * (a 0 * _) = a 0 * ((x i.succ).val * _)
  rw [Nat.mul_left_comm]
  congr 1

theorem widenRank_val {d : ℕ} (a b : Fin d → ℕ) (hb : ∀ i, a i ≤ b i)
    (x : (i : Fin d) → Fin (a i)) :
    widenRank d a b (finPiFinEquiv x).val =
      (finPiFinEquiv (fun i => Fin.castLE (hb i) (x i))).val := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [widenRank, rank_head]
    have h₀ := (x 0).isLt
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h₀,
      Nat.add_mul_div_left _ _ (by omega : 0 < a 0), Nat.div_eq_of_lt h₀, Nat.zero_add]
    rw [ih (fun i => a i.succ) (fun i => b i.succ) (fun i => hb i.succ) (fun i => x i.succ)]
    rfl


variable {box : List (ℕ × ℕ)} {k l : ℕ} (hb : BoxShape.Valid k l box)
    [∀ i, NeZero (modulus box i)]

/-- Tape slot occupied by the digit of unpadded mixed-radix rank `t`. -/
def digitSlot (t : Fin (∏ i, modulus box i)) : Fin (2^k) :=
  recordIndex hb (SynchronizedPadding.occupied (fun i => Fin (padding box i))
    (fun i => ZMod.finEquiv _ (finPiFinEquiv.symm t i)))

theorem digitSlot_val (t : Fin (∏ i, modulus box i)) : (digitSlot hb t).val =
    widenRank box.length (modulus box) (fun i => 2^(box.get i).1) t.val := by
  let u := finPiFinEquiv.symm t
  have H (i : Fin box.length) : modulus box i ≤ 2^(box.get i).1 :=
    (hb.axisBounds _ (List.get_mem _ i)).2.2.2
  have he (i : Fin box.length) :
      field hb i (Sum.inl (ZMod.finEquiv _ (u i))) = Fin.castLE (H i) (u i) := by
    apply Fin.ext
    rw [field_inl hb i, RingEquiv.symm_apply_apply]; rfl
  have valEq := widenRank_val (modulus box) _ H u
  change (finPiFinEquiv (fun i => field hb i (Sum.inl (ZMod.finEquiv _ (u i))))).val = _
  simp_rw [he]
  simpa only [u, Equiv.apply_symm_apply] using valEq.symm

theorem digitSlot_strictMono : StrictMono (digitSlot hb) := by
  intro i j hij
  rw [Fin.lt_def, digitSlot_val, digitSlot_val]
  exact widenRank_strictMono _ _ (fun t => NeZero.pos (modulus box t))
    (fun t => (hb.axisBounds _ (List.get_mem _ t)).2.2.2) hij

/-- A left-to-right scan that emits precisely the valid slots encounters them in
mixed-radix rank order. The test is the comparison of each binary field to its modulus. -/
theorem filter_valid_slots :
    (List.finRange (2^k)).filter (fun t => decide (∀ i : Fin box.length,
      (t.val / 2^(offset i)) % 2^(box.get i).1 < modulus box i)) = List.ofFn (digitSlot hb) := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact ((List.sortedLT_finRange _).pairwise).filter _
  · exact List.pairwise_ofFn.mpr (digitSlot_strictMono hb)
  intro t
  simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, List.mem_ofFn]
  rw [← occupied_iff hb t]
  constructor
  · rintro ⟨x, hx⟩
    let u (i : Fin box.length) := (ZMod.finEquiv _).symm (x i)
    use finPiFinEquiv u
    apply (recordIndex hb).symm.injective
    simpa [digitSlot, u] using hx
  · rintro ⟨p, rfl⟩
    exact ⟨_, ((recordIndex hb).symm_apply_apply _).symm⟩

end BoxFin

end NearSquareRoot
end Computability
end OAI
