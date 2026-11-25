import OAI.Computability.NearSquareRoot.PrecisionPlacedSlot
import OAI.Computability.NearSquareRoot.SynchronizedPlacedTables
import OAI.Computability.NearSquareRoot.SynchronizedBatchWordSemantics

/-! # Computed phase entries are the entries of the exact block instruction -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open Matrix ShortFourier AxisWord SynchronizedBorrowing
noncomputable section

theorem SlotQuery.atFlat_address (q : SlotQuery) (x : Ambient q.width) :
    (q.atFlat (finSumFinEquiv x).val).address = x := by
  cases x with
  | inl i =>
    have h : ¬ 2^q.width < i.val+1 := by have := i.isLt; omega
    simp [SlotQuery.atFlat, SlotQuery.address, h, Nat.mod_eq_of_lt i.isLt]
  | inr i =>
    simp [SlotQuery.atFlat, SlotQuery.address, Nat.mod_eq_of_lt i.isLt]

private theorem placedCoefficient_eq (q : SlotQuery) {b c : ℕ} (j : Fin 15)
    (p : Fin b × (Fin q.axis ⊕ Fin c)) :
    placedPhase (2^q.width) j (fun flat => (q.atFlat flat).coefficient) p =
      placedCoefficient q (first b j) (size b j) p.1.val (finSumFinEquiv p.2).val := by
  by_cases h : (finSumFinEquiv p.2).val < q.axis
  · simp only [placedPhase, cellLookup, placedCoefficient, h, ite_true]
    cases lookupRank _ _ _ _ _ <;> rfl
  · simp [placedPhase, cellLookup, placedCoefficient, h]

theorem placed_fixed_phase {a k b c : ℕ} [NeZero a] (har : a ≤ 2^k)
    (hr : 2*2^k ≤ 8*a) (j : Fin 15) (op : Inst) (ht : op.1.length ∈ phaseTags) (bits : ℕ) :
    let q := SlotQuery.fromInst a k bits op
    let u := auxiliaryLayout har
    batchMatrix (c := c) (b := b) hr j
        (((fixedSlot a k op).matrix dilationAddress).submatrix u.symm u.symm) =
      diagonal (fun p => placedCoefficient q (first b j) (size b j) p.1.val (finSumFinEquiv p.2).val) := by
  let q := SlotQuery.fromInst a k bits op
  let u := auxiliaryLayout har
  let f (x : Ambient k) :=
    if op.2.2 then star (slotPhase a k op.1.length op.2.1.length x) else slotPhase a k op.1.length op.2.1.length x
  have hflat (t : Fin a ⊕ Fin (2*2^k-a)) :
      (finSumFinEquiv (u.symm t)).val = (finSumFinEquiv t).val := by simp [u, auxiliaryLayout]
  have hlookup (t : Fin a ⊕ Fin (2*2^k-a)) :
      f (u.symm t) = (q.atFlat (finSumFinEquiv t).val).coefficient := by
    rw [← hflat t]
    have he := SlotQuery.atFlat_address q (u.symm t)
    let g (y : Ambient k) := adjointValue op.2.2 (slotPhase a k op.1.length op.2.1.length y)
    have hh : f (u.symm t) = g (u.symm t) := by
      cases ho : op.2.2 <;> simp [f, g, adjointValue, ho]
    exact hh.trans (congrArg g he.symm)
  change batchMatrix hr j _ = diagonal _
  rw [fixedSlot_phase har op ht]
  change batchMatrix hr j ((diagonal f).submatrix u.symm u.symm) = _
  rw [submatrix_diagonal_equiv]
  change batchMatrix hr j (diagonal (fun t => f (u.symm t))) = _
  simp_rw [hlookup]
  exact (placedPhase_diagonal (b := b) (c := c) (NeZero.pos a) har hr j
    (fun flat => (q.atFlat flat).coefficient)).trans (congrArg diagonal (funext (placedCoefficient_eq q j)))

/-- The physical computation of a directly placed phase agrees with the
phase instruction of the axis- and batch-tagged block program. -/
theorem gateMatrix_phase {m : ℕ} (a c k : Fin m → ℕ) [∀ i, NeZero (a i)]
    (spectator : ∀ i, Spectators a c i ≃ Fin (Fintype.card (Spectators a c i)))
    (har : ∀ i, a i ≤ 2 ^ k i) (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * a i)
    (i : Fin m) (j : Fin 15) (op : Inst) (ht : op.1.length ∈ phaseTags) (bits : ℕ) :
    let b := Fintype.card (Spectators a c i)
    let q := SlotQuery.fromInst (a i) (k i) bits op
    let addr := BatchWord.axisLayout a c spectator i
    BatchWord.gateMatrix a c k spectator har hborrow (i,j,op) =
      diagonal (fun p => placedCoefficient q (first b j) (size b j)
        (addr p).1.val (finSumFinEquiv (addr p).2).val) := by
  dsimp only
  rw [BatchWord.gateMatrix, placed_fixed_phase (har i) (hborrow i) j op ht bits, submatrix_diagonal_equiv]
  rfl

end
end PhaseTable

end NearSquareRoot
end Computability
end OAI
