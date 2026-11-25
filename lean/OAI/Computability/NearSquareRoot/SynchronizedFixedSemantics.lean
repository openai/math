import OAI.Computability.NearSquareRoot.SynchronizedFixedFields
import OAI.Computability.NearSquareRoot.SynchronizedSlotTable
import OAI.Computability.NearSquareRoot.SynchronizedInternalRouting
import OAI.Computability.NearSquareRoot.SynchronizedBlockSlots

/-! # Execution of routed opcodes on the physical half selector -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord

open Matrix SynchronizedLayers SynchronizedPair IntegerMultiplication.Code
open scoped Matrix
noncomputable section

variable {k a : ℕ} [NeZero a]

/-- Bit reversal in the primary half; the other half keeps its address. -/
def reverseLeft (k : ℕ) : Equiv.Perm (Ambient k) :=
  (reversalPerm k).sumCongr (Equiv.refl _)

private theorem reverseLeft_matrix (k : ℕ) :
    ((reverseLeft k).toPEquiv.toMatrix : Matrix (Ambient k) (Ambient k) ℂ) =
        firstHalf (radixReverseMatrix k) := by
  ext i j
  cases i <;> cases j <;>
    simp [reverseLeft, firstHalf, radixReverseMatrix, PEquiv.toMatrix_apply, one_apply]

/-- Malformed radix-bit addresses leave the routes unchanged. -/
def routeAt (k arg : ℕ) : Equiv.Perm (Ambient k) :=
  if h : arg < k then internalRoute ⟨arg,h⟩ else Equiv.refl _

def fixedBase (a k : ℕ) [NeZero a] (tag arg : ℕ) : Slot (Ambient k) :=
  if tag = 0 then .permutation (reverseLeft k) else
  if tag = 10 then .walsh else
  if tag = 18 then .permutation (routeAt k arg) else
    .phase (slotPhase a k tag arg) (slotPhase_norm _ _ _ _)

private def orient {A : Type} (s : Slot A) (b : Bool) : Slot A :=
  if b then
    match s with
    | .permutation p => .permutation p.symm
    | .walsh => .walsh
    | .phase d h => .phase (fun i => star (d i)) (fun i => by simpa using h i)
  else s

/-- Read an instruction directly as a permutation, a unit phase table, or
the Walsh butterfly on the designated selector. -/
def fixedSlot (a k : ℕ) [NeZero a] (x : Inst) : Slot (Ambient k) :=
  orient (fixedBase a k x.1.length x.2.1.length) x.2.2

private theorem orient_matrix {A S : Type} [Fintype A] [DecidableEq A]
    [Fintype S] [DecidableEq S] (e : A ≃ Fin 2 × S) (s : Slot A) (b : Bool) :
    (orient s b).matrix e = if b then (s.matrix e)ᴴ else s.matrix e := by
  cases b
  · rfl
  · simp only [orient, ite_true]
    cases s with
    | phase d h => exact (diagonal_conjTranspose d).symm
    | permutation p =>
      ext i j
      simp only [Slot.matrix, conjTranspose_apply, PEquiv.toMatrix_apply,
        Equiv.toPEquiv_apply, Option.mem_some_iff, Equiv.symm_apply_eq]
      split_ifs <;> simp_all [eq_comm]
    | walsh =>
      have hw : walshᴴ = walsh := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [walsh, conjTranspose_apply]
      simp [Slot.matrix, conjTranspose_submatrix, blockDiagonal_conjTranspose, hw]

theorem fixedSlot_kind (a k : ℕ) [NeZero a] (x : Inst) :
    (fixedSlot a k x).kind =
      if x.1.length = 0 then .permutation else
      if x.1.length = 10 then .walsh else
      if x.1.length = 18 then .permutation else .diagonal := by
  have orient_kind {A : Type} (s : Slot A) (b : Bool) : (orient s b).kind = s.kind := by
    cases b <;> cases s <;> rfl
  simp only [fixedSlot, orient_kind, fixedBase]
  split_ifs <;> rfl

private theorem base_sound (har : a ≤ 2^k) (t arg : ℕ)
    (ht : t ∈ phaseTags ∨ t = 0 ∨ t = 10) :
    (fixedBase a k t arg).matrix dilationAddress = lowerDecode har t arg := by
  rcases ht with h | rfl | rfl
  · have ne (n : ℕ) (hn : n ∉ phaseTags) : t ≠ n := fun he => hn (he ▸ h)
    simp [fixedBase, ne 0 (by decide), ne 10 (by decide), ne 18 (by decide),
      Slot.matrix, slotPhase_matrix har h]
  · exact reverseLeft_matrix k
  · rfl

/-- Every emitted phase instruction is the oriented entrywise phase table. -/
theorem fixedSlot_phase (har : a ≤ 2^k) (x : Inst) (h : x.1.length ∈ phaseTags) :
    (fixedSlot a k x).matrix dilationAddress = diagonal (fun y =>
      if x.2.2 then star (slotPhase a k x.1.length x.2.1.length y)
      else slotPhase a k x.1.length x.2.1.length y) := by
  rw [← slotPhase_matrix_oriented har x h, fixedSlot, orient_matrix, base_sound har _ _ (.inl h)]
  rfl

private def fixedProd (a k : ℕ) [NeZero a] (w : List Inst) :=
  (w.map (fun x => (fixedSlot a k x).matrix dilationAddress)).prod

private theorem fixedProd_flip (a k : ℕ) [NeZero a] (x : Inst) :
    (fixedSlot a k (flip x)).matrix dilationAddress = ((fixedSlot a k x).matrix dilationAddress)ᴴ := by
  rcases x with ⟨t,i,b⟩
  cases b <;> simp [flip, fixedSlot, orient_matrix]

private theorem fixedProd_adj (a k : ℕ) [NeZero a] (w : List Inst) :
    fixedProd a k (adj w) = (fixedProd a k w)ᴴ := by
  induction w with
  | nil => simp [fixedProd, adj]
  | cons x w ih =>
    rw [show adj (x::w) = adj w ++ [flip x] by simp [adj]]
    simpa [fixedProd, fixedProd_flip] using congrArg
      (fun m : Matrix (Ambient k) (Ambient k) ℂ => m * ((fixedSlot a k x).matrix dilationAddress)ᴴ) ih

private theorem fixedProd_route (i : Fin k) (arg : Tally) (hi : arg.length = i.val) :
    fixedProd a k [inst 18 arg, inst 10, inst 18 arg] = bothHalvesWalsh i := by
  rw [bothHalvesWalsh_route, internalRoute_symm]
  simp [fixedProd, fixedSlot, orient, fixedBase, inst, Slot.matrix, routeAt, hi,
    i.isLt, physicalHalfWalsh, halfWalsh, mul_assoc]

private theorem fixedInst_sound (har : a ≤ 2^k) (x : Inst)
    (hx : x.1.length ∈ phaseTags ∨ x.1.length = 0 ∨ x.1.length = 10 ∨ x.1.length = 14) :
    fixedProd a k (fixedInst (tally k) x) = evalSlot har x := by
  by_cases h : x.1.length = 14
  · have hbase : lowerDecode har 14 x.2.1.length = bitLookup x.2.1.length bothHalvesWalsh := rfl
    simp only [fixedInst, h, ite_true, tally_length, evalSlot, hbase, bitLookup]
    by_cases hi : x.2.1.length < k
    · simp only [hi, dite_true, ite_true]
      have hr := fixedProd_route (a := a) (⟨x.2.1.length, hi⟩ : Fin k) x.2.1 rfl
      cases x.2.2 <;> simp [fixedProd_adj, hr]
    · simp [hi, fixedProd]
  · have ht : x.1.length ∈ phaseTags ∨ x.1.length = 0 ∨ x.1.length = 10 := by tauto
    simp [fixedInst, h, fixedProd, fixedSlot, orient_matrix, base_sound har _ _ ht, evalSlot]

/-- The physical fixed-bit program generated from unary k restores this
fiber's normalized Fourier transform and returns every borrowed coordinate. -/
theorem fixedWord_correct (hr : 2*a-1 ≤ 2^k) (har : a ≤ 2^k) :
    ((fixedWord (tally k)).map (fun x => (fixedSlot a k x).matrix dilationAddress)).prod =
      extend (activeFiber har) (normalizedFourier a) := by
  rw [← loweredRestored_correct hr har]
  let w := loweredRestored (tally k)
  change fixedProd a k (w.flatMap (fixedInst (tally k))) = slotProd har w
  have aux (u : List Inst) (hu : ∀ x ∈ u, LoweredTag x.1.length) :
      fixedProd a k (u.flatMap (fixedInst (tally k))) = slotProd har u := by
    induction u with
    | nil => simp [fixedProd, slotProd]
    | cons x u ih =>
      have head := fixedInst_sound har x (hu x List.mem_cons_self)
      have tail := ih (fun y hy => hu y (List.mem_cons_of_mem _ hy))
      simpa [fixedProd, slotProd] using congrArg₂ (· * ·) head tail
  exact aux w (fun _ h => loweredRestored_tag _ h)

end
end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
