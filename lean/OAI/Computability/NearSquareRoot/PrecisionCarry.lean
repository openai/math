import OAI.Computability.IntegerMultiplication.Lea.Wintry
import OAI.Computability.NearSquareRoot.PrecisionCarryConvolution
import OAI.Computability.NearSquareRoot.PrecisionCarrySetup
import OAI.Computability.NearSquareRoot.PrecisionCarryMachine

/-! # From recovered coefficients to the fixed-width binary product

In radix `2^b`, the carry pass needs just three layers of the P192
`harvest` algorithm when each recovered coefficient fits into `3*b`
bits. The same three-layer program handles every operand and radix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication Code Bits Finset

/-- The digits obtained by chopping a most-significant-first operand after reversal and padding. -/
noncomputable def unpackDigits (b m : ℕ) (x : Word) : Fin m → ℕ :=
  value ∘ Lea.crop b m x.reverse

theorem unpackDigits_lt (b m : ℕ) (x : Word) (i : Fin m) :
    unpackDigits b m x i < 2^b := by
  simpa [unpackDigits, (Lea.crop_ b m x.reverse).1 i] using value_lt (Lea.crop b m x.reverse i)

theorem unpackDigits_eq_zero {b m h : ℕ} (x : Word) (hx : x.length ≤ b*h) (hm : h ≤ m)
    (i : Fin m) (hi : h ≤ i.val) : unpackDigits b m x i = 0 := by
  apply Lea.emptyCrop b m x.reverse h _ _ i hi
  · simpa using hx
  · simpa [Nat.mul_comm m b] using hx.trans (Nat.mul_le_mul_left b hm)

theorem score_unpackDigits {b m : ℕ} (x : Word) (hx : x.length ≤ m*b) :
    Cap.score (2^b) (unpackDigits b m x) = bitValue x := by
  rw [endianness]
  exact Lea.scoreV b m _ (by simpa using hx)

private theorem score_succ (R : ℕ) {m : ℕ} (a : Fin (m+1) → ℕ) :
    Cap.score R a = a 0 + R * Cap.score R (fun i => a i.succ) := by
  unfold Cap.score
  rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [Fin.val_succ, pow_succ']
  ring

private theorem score_extract {m R : ℕ} (hR : 0 < R) (a : Fin m → ℕ) (ha : ∀ i, a i < R)
    (i : Fin m) : (Cap.score R a / R^i.val) % R = a i := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [score_succ, Nat.mod_eq_of_lt (ha 0)]
    · rw [score_succ, Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt (ha 0), zero_add]
      exact ih (fun i => a i.succ) (fun i => ha i.succ) j

/-- Every extracted digit is the corresponding radix residue of the input value. -/
theorem unpackDigits_extract {b m : ℕ} (x : Word) (hx : x.length ≤ m*b) (i : Fin m) :
    unpackDigits b m x i = bitValue x / (2^b)^i.val % (2^b) := by
  rw [← score_unpackDigits x hx]
  exact (score_extract (by positivity) _ (unpackDigits_lt b m x) i).symm

/-- After increasing the slot count, the old digits are preserved in order
and all successive entries are zero. -/
theorem unpackDigits_widen {b h m : ℕ} (x : Word) (hx : x.length ≤ h*b) (hm : h ≤ m)
    (i : Fin m) :
    unpackDigits b m x i = if hi : i.val < h then
      value (Lea.crop b h x.reverse ⟨i.val, hi⟩) else 0 := by
  split_ifs with hi
  · change unpackDigits b m x i = unpackDigits b h x ⟨i.val, hi⟩
    rw [unpackDigits_extract x (hx.trans (Nat.mul_le_mul_right b hm)), unpackDigits_extract x hx]
  · exact unpackDigits_eq_zero x (Nat.mul_comm h b ▸ hx) hm i (by omega)

/-- P192's radix evaluation theorem specialized to a plain coefficient array of any length. -/
theorem ordinaryCoefficient_score {m : ℕ} (R : ℕ) (x y : Fin m → ℕ) (h : ℕ)
    (hx : ∀ i, h ≤ i.val → x i = 0) (hy : ∀ i, h ≤ i.val → y i = 0) (hm : 2*h ≤ m) :
    Cap.score R (ordinaryCoefficient x y) = Cap.score R x * Cap.score R y := by
  let s : Cap.Bounds 1 := fun _ => m
  have aux : ∀ (x y : Fin (Cap.space s) → ℕ), (∀ i, h ≤ i.val → x i = 0) →
      (∀ i, h ≤ i.val → y i = 0) → 2*h ≤ Cap.space s →
      Cap.score R (ordinaryCoefficient x y) = Cap.score R x * Cap.score R y :=
    fun x y => Cap.scoreboard (s := s) R x y h
  rw [show Cap.space s = m by simp [Cap.space, s]] at aux
  exact aux x y hx hy hm

/-- Encode the recovered words, the radix widths and the required output width. -/
def carryPacket {m : ℕ} (n b : ℕ) (words : Fin m → Word) : Tally × Lea.Trigger :=
  (Code.tally (2*n), List.ofFn words, Lea.scale0 m b)

/-- Three P192 `harvest` passes accumulate the coefficient words. Width reduction
and reversal write the answer in the input convention, including leading zeros. -/
def finishCarry (p : Tally × Lea.Trigger) : Word :=
  (resize (p.1, Lea.harvest 3 p.2)).reverse

theorem finishCarry_easy : Easy finishCarry :=
  (easy_resize (Easy.fst.pair (Easy.snd.compose (Lea.harvestE 3)))).compose Easy.reverse

/-- Exact MSF output for the natural-order coefficient stream returned from inverse CRT. -/
theorem finishCarry_product {n b h m : ℕ} (x y : Word) (hx : x.length = n) (hy : y.length = n)
    (hn : n ≤ b*h) (hm : 2*h ≤ m) (words : Fin m → Word)
    (width : ∀ i, (words i).length ≤ 3*b)
    (coeff : ∀ i, value (words i) = ordinaryCoefficient (unpackDigits b m x) (unpackDigits b m y) i) :
    let z := finishCarry (carryPacket n b words)
    z.length = 2*n ∧ bitValue z = bitValue x * bitValue y := by
  have hhm : h ≤ m := by omega
  have cover : n ≤ m*b := by rw [mul_comm m]; exact hn.trans (Nat.mul_le_mul_left _ hhm)
  have low (t : Word) (ht : t.length = n) : bitValue t < 2^n := by
    simpa [endianness, ht] using value_lt t.reverse
  have fits : bitValue x * bitValue y < 2^(2*n) := by
    rw [two_mul, pow_add]
    exact (Nat.mul_le_mul_right _ (low x hx).le).trans_lt
      (Nat.mul_lt_mul_of_pos_left (low y hy) (Nat.pow_pos (by decide)))
  change (sized (2*n) _).reverse.length = _ ∧ bitValue (sized (2*n) _).reverse = _
  constructor
  · simp
  · rw [endianness, List.reverse_reverse, sized_low]
    change value (Lea.harvest 3 (List.ofFn words, Lea.scale0 m b)) % 2^(2*n) = _
    rw [Lea.savored b 3 words width]
    rw [show value ∘ words = ordinaryCoefficient (unpackDigits b m x) (unpackDigits b m y) by
      funext i; exact coeff i]
    rw [ordinaryCoefficient_score _ _ _ h
      (unpackDigits_eq_zero _ (hx ▸ hn) hhm) (unpackDigits_eq_zero _ (hy ▸ hn) hhm) hm,
      show Lea.radix b = 2^b from rfl,
      score_unpackDigits x (hx ▸ cover), score_unpackDigits y (hy ▸ cover), Nat.mod_eq_of_lt fits]

/-- Three radix blocks suffice for the recovered integer coefficient. -/
theorem unpackedCoefficient_lt {n b h m : ℕ} (x y : Word) (hx : x.length = n) (hy : y.length = n)
    (hn : n ≤ b*h) (hm : 2*h ≤ m) (hh : 0 < h) (hbits : h ≤ 2^b) (i : Fin m) :
    ordinaryCoefficient (unpackDigits b m x) (unpackDigits b m y) i < 2^(3*b) := by
  let : NeZero m := ⟨by omega⟩
  have hhm : h ≤ m := by omega
  apply (ordinaryCoefficient_lt hh _ _
    (unpackDigits_eq_zero x (hx ▸ hn) hhm) (unpackDigits_eq_zero y (hy ▸ hn) hhm)
    hm (unpackDigits_lt b m x) (unpackDigits_lt b m y) i).trans_le
  rw [show 3*b = b + 2*b by omega, pow_add]
  exact Nat.mul_le_mul_right _ hbits

/-- A single P192 command carries and resizes all packets within a linear-step
bound, for every size, with any stack suffix and any external control scope. -/
theorem finishCarry_runs :
    ∃ (c : Cmd) (C : ℕ), ∀ {n b m N k : ℕ} (words : Fin m → Word),
      (∀ i, (words i).length ≤ 3*b) → m ≤ N → b ≤ 2*k → n ≤ N*k → 1 ≤ N → 1 ≤ k →
      ∀ env, Fits.value env c 0 (send (carryPacket n b words))
        (send (finishCarry (carryPacket n b words))) (C*(N*k)) := by
  obtain ⟨c, A, run⟩ := finishCarry_easy
  refine ⟨c, A * 36, ?_⟩
  intro n b m N k words hw hm hb hn hN hk env r
  apply (run (carryPacket n b words) env r).mono
  have bound : size (carryPacket n b words) ≤ 35*(N*k) :=
    carryInputSize_le_volume words hw hm hb hn hN hk
  rw [mul_assoc]
  exact Nat.mul_le_mul_left _ (by have hpos := Nat.mul_pos hN hk; omega)

/-- One fixed machine on serialized carry packets, with plain MSF bits on a separate
output tape. The bound charges movement, the carry program, and plain output conversion. -/
theorem finishCarry_machine :
    TreeToPlainBits send finishCarry (fun p => size p + (finishCarry p).length) :=
  treeToPlainBits_of_task finishCarry_easy

/-- Both the halting time and the union of visited cells in `finishCarry_machine`
are linear in the padded stream volume on the multiplication packets. -/
theorem finishCarry_physicalBudget {n b m N k : ℕ} (words : Fin m → Word)
    (hw : ∀ i, (words i).length ≤ 3*b) (hm : m ≤ N) (hb : b ≤ 2*k) (hn : n ≤ N*k)
    (hN : 1 ≤ N) (hk : 1 ≤ k) :
    size (carryPacket n b words) + (finishCarry (carryPacket n b words)).length + 1 ≤
      38*(N*k) := by
  have bound : size (carryPacket n b words) ≤ 35*(N*k) :=
    carryInputSize_le_volume words hw hm hb hn hN hk
  have len : (finishCarry (carryPacket n b words)).length = 2*n := by
    change (sized (2*n) _).reverse.length = _
    simp
  rw [len]
  have hpos := Nat.mul_pos hN hk
  omega

/-- The compact-packet subroutine charges generation of the coefficient-specific
radix rulers, carry propagation, resizing, and reversal. -/
theorem finishCarry_compact {I : Type*} (n b m N k : I → ℕ) (words : (i : I) → Fin (m i) → Word)
    (hw : ∀ i j, (words i j).length ≤ 3*b i) (hm : ∀ i, m i ≤ N i)
    (hb : ∀ i, b i ≤ 2*k i) (hn : ∀ i, n i ≤ N i*k i)
    (hN : ∀ i, 1 ≤ N i) (hk : ∀ i, 1 ≤ k i) :
    Task (fun i => N i*k i)
      (fun i => send (tally (n i), tally (b i), List.ofFn (words i)))
      (fun i => send (finishCarry (carryPacket (n i) (b i) (words i)))) := by
  have build := prepareCarry n b m N k words hw hm hb hn hN hk
  have run := finishCarry_easy.on (fun i => carryPacket (n i) (b i) (words i))
  apply (build.compose run).bound 36
  intro i
  have bound : size (carryPacket (n i) (b i) (words i)) ≤ 35*(N i*k i) :=
    carryInputSize_le_volume _ (hw i) (hm i) (hb i) (hn i) (hN i) (hk i)
  omega

end NearSquareRoot
end Computability
end OAI
