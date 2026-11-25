import OAI.Computability.BorderVNP.DiagonalEnrichedTape

/-! # Numbered formal row on the actual public bit-frame execution -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedTape

open Crossing Shortening Adaptive Packing Packing.DeckGrid Cover TeamContraction ExternalSew GridHosts
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PublicCapacity VPVNP BorderVNP.Cube MvPolynomial
open scoped BigOperators Classical BorderVNP.Epoch.Cube

universe u

variable {D m start T : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {Word : ℕ → Type} [∀ t, Fintype (Word t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r pins link k axes gridDepth a regs rw ec width s copies : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
    {order : Fin (tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D axes gridDepth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (free : Fin (R+1) → Fin r → Fin a → Bool)
    {deep : S.floor+1+S.drop*T ≤ start} (count : (EnrichedOuter.fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (tileCount axes gridDepth))
      (fun _ => copies*inputBlockWidth r (k+1) axes gridDepth) shape Word j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : EnrichedOuter.Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid (tapeTemplate p fit pins) axes gridDepth order position).groupedRepeat
      (fun _ : Fin (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth) order copies)
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (hg : 0 < inputBlockWidth r (k+1) axes gridDepth)

set_option synthInstance.maxSize 4000

/-- Enumerate the true original batch numbers in the nested public history. -/
noncomputable local instance numberedBatchFinite {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j

variable {cn cd cb ch cK cs : ℕ} {Pin : Type} [Fintype Gadget]
    (packet : ∀ q, PacketPlacement (Port (EnrichedOuter.fan S) (Fin copies × Unit) T)
      cn cd cb ch cK (network p fit position free count M bottom installed q))
    (cubePos : TableEntry cn cb ch cK cs → Gadget)
    (encode : Pin → Fin pins → Bool)
    (bank : Pin → Ports (fun _ : FreeBlock R (tileCount axes gridDepth) =>
      inputBlockWidth r (k+1) axes gridDepth))

/-- Each physical path has one public geometry history, one original private
route assignment per batch copy, then one passing packed cube assignment.
The public rows retain their actual per-branch sparse names and saved bits. -/
noncomputable abbrev assignedPath (i : Pin) :=
  Assigned.Path (network p fit position free count M bottom installed) packet
    (tags p fit W position free count M bottom installed y hy pos hg)
    (fun i _ => bank i) cubePos i

/-- All scalar positions, including selected zero positions, and all real
parameter occurrences on this assignment, in the reader's native order. -/
noncomputable def assigned (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (i : Pin) (v : assignedPath p fit W position free count M bottom installed y hy pos hg packet cubePos bank i) :=
  Assigned.numbered (network p fit position free count M bottom installed) packet
    (tags p fit W position free count M bottom installed y hy pos hg)
    (fun i _ => bank i) cubePos ord (SewnTape.teamNumber _ T copies R count) i v

/-- Equation (11.2) on the original wired parse table. The same named
fine verifier is used on every substituted pin, on all subsequent choices
of literal tails and at every finite scalar specialization. -/
theorem numbered_expansion (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (cube : ValidTables (values ∘ cubePos)) (i : Pin)
    (delivered : ∀ z, let a := freeLane hg (gridRoom (SewnTape.wiring p fit free pins) Fintype.card_pos) z
      bank i a.1 a.2 = freeBits (SewnTape.wiring p fit free pins) (encode i) z) :
    numberedSubstituted E k s ord (SewnTape.wiring p fit free pins).slot (encode i) =
      ∑ v : assignedPath p fit W position free count M bottom installed y hy pos hg packet cubePos bank i,
        monomial (assigned p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord i v).exponents
          ((assigned p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord i v).coefficient values) :=
by
  have row := Assigned.numbered_row (network p fit position free count M bottom installed) packet
    (tags p fit W position free count M bottom installed y hy pos hg) (fun i _ => bank i) cubePos
    ord (SewnTape.teamNumber _ T copies R count) (SewnTape.wiring p fit free pins).slot encode values cube i
  have sewn := substituted_eq p fit W position free count M bottom installed y hy pos hg
    values lookup (encode i) (bank i) delivered
  refine Eq.trans ?_ (Eq.trans (row (sewn.trans ?_)) ?_)
  · unfold numberedSubstituted
    exact Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _)) fun _ _ => rfl
  · apply Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _))
    intro q _
    exact Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _)) fun _ _ => rfl
  · exact Finset.sum_congr (congrArg (@Fintype.elems _) (Subsingleton.elim _ _)) fun _ _ => rfl

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
