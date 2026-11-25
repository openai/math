import OAI.Computability.BorderVNP.DiagonalNumberedEnrichedTape
import OAI.Computability.BorderVNP.DiagonalEnrichedTerminalPayload
import OAI.Computability.BorderVNP.DiagonalBottomScalarCounts
import OAI.Computability.BorderVNP.DiagonalAssignedGadgetBounds

/-! # Real parameter and scalar counts on the public program's own assigned paths -/

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
set_option maxHeartbeats 850000

/-- Enumerate the true original batch numbers in the nested public history. -/
noncomputable local instance payloadBatchFinite {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j

variable {cn cd cb ch cK cs : ℕ} {Pin : Type}
    (packet : ∀ q, PacketPlacement (Port (EnrichedOuter.fan S) (Fin copies × Unit) T)
      cn cd cb ch cK (network p fit position free count M bottom installed q))
    (cubePos : TableEntry cn cb ch cK cs → Gadget)
    (bank : Pin → Ports (fun _ : FreeBlock R (tileCount axes gridDepth) =>
      inputBlockWidth r (k+1) axes gridDepth))

/-- On the original wired parse network every hidden fine assignment has zero
scalar occurrences. Subdivision, the selected sorted stages, their saved
public records and exterior sewing preserve the true expanded payload bound. -/
theorem tags_payload (fields : Epoch.Round.RecordData bottom.val.pack.layout)
    (q : (packHistory bottom M.epoch T).Index)
    (z : Fin ((EnrichedOuter.fan S)^T) → Fin copies → W.Hidden position) :
    PayloadBound (tags p fit W position free count M bottom installed y hy pos hg q z).tags
      (M.historyFields bottom fields T q).payload := by
  let seed := base (Gadget := Gadget) p fit W position bottom installed
  have leaf : ∀ z, PayloadBound (seed z).tags fields.payload := by
    intro leaf v zz x g
    have hz := Tracked.cast_no_gadgets (W.bundle (Gadget := Gadget) position copies leaf) installed.symm
      (W.bundle_no_gadgets (Gadget := Gadget) position leaf) v zz x
    change (counters (((W.bundle (Gadget := Gadget) position copies leaf).castLayout installed.symm).tags v zz x)).2 g ≤ _
    rw [hz]
    exact Nat.zero_le _
  exact enrichedSewn_payloadBound (SewnTape.wiring p fit free pins) axes gridDepth order position count M bottom
    installed y hy pos seed hg q z (M.historyFields bottom fields T q).payload
    (EnrichedOuterReplay.terminal_payloadBound M y hy pos bottom seed fields leaf q z)

/-- Exact numerical certificate for the scalar coordinates of a numbered
path in (11.2), on the evaluator's own physical profile and packed cube. -/
theorem assigned_counts_bound (fields : Epoch.Round.RecordData bottom.val.pack.layout)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (i : Pin)
    (u : assignedPath p fit W position free count M bottom installed y hy pos hg packet cubePos bank i)
    (g : Gadget) :
    (∑ t, (assigned p fit W position free count M bottom installed y hy pos hg packet cubePos bank ord i u).counts t g) ≤
      (∑ v, (M.historyFields bottom fields T u.1).payload v) +
        Fintype.card (Packet cn cd (packet u.1).blocks × Vertex (cn+1)) :=
  Assigned.numbered_counts_le (network p fit position free count M bottom installed) packet
    (tags p fit W position free count M bottom installed y hy pos hg) (fun i _ => bank i) cubePos ord
    (SewnTape.teamNumber (EnrichedOuter.fan S) T copies R count) (fun q => (M.historyFields bottom fields T q).payload)
    (tags_payload p fit W position free count M bottom installed y hy pos hg fields) i u g

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
