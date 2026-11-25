import OAI.Computability.BorderVNP.DiagonalSewnTape
import OAI.Computability.BorderVNP.DiagonalAssignedRows

/-! # Complete numbered parse-row expansion on the actual physical tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.SewnTape


open Crossing Shortening Adaptive Packing Packing.DeckGrid Packing.PhysicalEpochs Cover TeamContraction
open ExternalSew ExternalSew.GridHosts VPVNP BorderVNP.Cube MvPolynomial
open scoped BigOperators Classical

set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : PackedHistoryCircuit.Normalized.SiteSchedule e} (U : Factory.Dense.Programs S)
    {R r pins link k axes gridDepth a regs w ec width s copies T start : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs w ec width ≤ k+1)
    {order : Fin (tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D axes gridDepth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (free : Fin (R+1) → Fin r → Fin a → Bool)

/-- Row-major enumeration of the original batches after these packing stages. -/
noncomputable local instance numberedBatchFinite {j : ℕ} :
    Fintype (Port (Factory.ofDenseSchedule U).fan (Fin copies × Unit) j) :=
  Replay.batchFinite (Factory.ofDenseSchedule U).fan (Fin copies × Unit) j

variable (deep : (Factory.ofDenseSchedule U).floor+1+(Factory.ofDenseSchedule U).drop*T ≤ start) (count : (Factory.ofDenseSchedule U).fan^T*copies = R+1)
    (bottom : (Factory.ofDenseSchedule U).State (fun _ : Fin (tileCount axes gridDepth) => copies*(inputBlockWidth r (k+1) axes gridDepth)) start 0)
    (installed : bottom.pack.layout = (wiredGrid (tapeTemplate p fit pins) axes gridDepth order position).groupedRepeat
      (fun _ : Fin (tileCount axes gridDepth) => (inputBlockWidth r (k+1) axes gridDepth)) order copies)
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (hg : 0 < (inputBlockWidth r (k+1) axes gridDepth))


/-- Original exponent-word teams in the row-major order of the physical machine. -/
def teamNumber (fan T copies R : ℕ) (count : fan^T*copies = R+1) :
    Port fan (Fin copies × Unit) T ≃ Fin (R+1) :=
  (portEquiv fan (Fin copies × Unit) T).trans
    (((Equiv.refl (Fin (fan^T))).prodCongr (Equiv.prodUnique (Fin copies) Unit)).trans
      (teamBlocks (fan^T) copies count).symm)

variable {cn cd cb ch cK cs : ℕ} {Pin : Type} [Fintype Gadget]
    (packet : ∀ q, PacketPlacement (Port (Factory.ofDenseSchedule U).fan (Fin copies × Unit) T)
      cn cd cb ch cK (network U p fit position free deep count bottom installed q))
    (cubePos : TableEntry cn cb ch cK cs → Gadget)
    (encode : Pin → Fin pins → Bool)
    (bank : Pin → Ports (fun _ : FreeBlock R (tileCount axes gridDepth) =>
      inputBlockWidth r (k+1) axes gridDepth))

/-- Each physical path has one public geometry history, one original private
route assignment per batch copy, then one passing packed cube assignment.
The scalar and length declaration choices are attached to that same path. -/
noncomputable abbrev assignedPath (i : Pin) :=
  Assigned.Path (network U p fit position free deep count bottom installed) packet
    (tags U p fit W position free deep count bottom installed y hy pos hg)
    (fun i _ => bank i) cubePos i

/-- All scalar positions, including selected zero positions, and all real
parameter occurrences on this assignment, in the reader's native order. -/
noncomputable def assigned (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (i : Pin) (v : assignedPath U p fit W position free deep count bottom installed y hy pos hg packet cubePos bank i) :=
  Assigned.numbered (network U p fit position free deep count bottom installed) packet
    (tags U p fit W position free deep count bottom installed y hy pos hg)
    (fun i _ => bank i) cubePos ord (teamNumber _ T copies R count) i v

/-- Equation (11.2) on the original wired parse table. The same named
fine verifier is used on every substituted pin, on all subsequent choices
of literal tails and at every finite scalar specialization. -/
theorem numbered_expansion (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (cube : ValidTables (values ∘ cubePos)) (i : Pin)
    (delivered : ∀ z, let a := freeLane hg (gridRoom (wiring p fit free pins) Fintype.card_pos) z
      bank i a.1 a.2 = freeBits (wiring p fit free pins) (encode i) z) :
    numberedSubstituted E k s ord (wiring p fit free pins).slot (encode i) =
      ∑ v : assignedPath U p fit W position free deep count bottom installed y hy pos hg packet cubePos bank i,
        monomial (assigned U p fit W position free deep count bottom installed y hy pos hg packet cubePos bank ord i v).exponents
          ((assigned U p fit W position free deep count bottom installed y hy pos hg packet cubePos bank ord i v).coefficient values) :=
by
  have row := Assigned.numbered_row (network U p fit position free deep count bottom installed) packet
    (tags U p fit W position free deep count bottom installed y hy pos hg) (fun i _ => bank i) cubePos
    ord (teamNumber _ T copies R count) (wiring p fit free pins).slot encode values cube i
  have sewn := substituted_eq U p fit W position free deep count bottom installed y hy pos hg
    values lookup (encode i) (bank i) delivered
  refine Eq.trans ?_ (Eq.trans (row (sewn.trans ?_)) ?_)
  · unfold numberedSubstituted
    exact Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _)) fun _ _ => rfl
  · apply Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _))
    intro q _
    exact Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _)) fun _ _ => rfl
  · exact Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _)) fun _ _ => rfl

end Diagonal.CellEntries.SewnTape

end BorderVNP
end Computability
end OAI
