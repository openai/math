import OAI.Computability.BorderVNP.DiagonalEnrichedReaderBounds
import OAI.Computability.BorderVNP.DiagonalNativeWiredFiber
import OAI.Computability.BorderVNP.DiagonalSpecializedChart

/-! # Realization on the common tape used by the native program and the parsed verifier -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedTape

open Branch Crossing Shortening Adaptive Packing Packing.DeckGrid Cover TeamContraction ProcessorSlots ExternalSew GridHosts
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PublicCapacity VPVNP BorderVNP.Cube
open RoutingISA RoutingISA.Evaluator CompactMachine CellMacro.Generator VPVNP.BurstRAM ResidueBox ResidueIndex ResiduePins
open scoped BigOperators Classical

universe u

variable {D m start T : ℕ} [NeZero D] {K₀ K : Type} [Field K₀] [Field K] {e : PaidIdentity K D m}
    (cube : FixedCube K₀) (φ : K₀ →+* K) {S : Normalized.SiteSchedule e}
    {shape : ℕ → Shape} {Word₀ : ℕ → Type} [∀ t, Fintype (Word₀ t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w₀ : ℕ → ℕ → ℕ}
    {R r link k axes gridDepth a regs w ec width s copies mult tally pin cd q : ℕ}
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    {C : CommonField e (φ ∘ cube.table) q k s ord} (chart : AdvisedBranch C)
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    (reader : ChosenReader chart (R+1) r mult tally w pin)

local notation "h" => pairedTableParameters (k+1) s
local notation "Raw" => Fin ((h+2)*pin) → Bool
local notation "Idx" => Index (Fin (Module.finrank (ZMod C.p) chart.E)) (Fin h) (chart.pinRadius (R+1) r)
local notation "codec" => boxPinCodec h reader.rankFits reader.boxFits

variable (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs w ec width ≤ k+1)
    {order : Fin (tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2))}
    (W : WiredWitness (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin)) (Fin.last k) D axes gridDepth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (free : Fin (R+1) → Fin r → Fin a → Bool)
    {deep : S.floor+1+S.drop*T ≤ start} (count : (EnrichedOuter.fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (tileCount axes gridDepth))
      (fun _ => copies*inputBlockWidth r (k+1) axes gridDepth) shape Word₀ j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w₀) (bottom : EnrichedOuter.Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid (tapeTemplate p fit ((pairedTableParameters (k+1) s+2)*pin))
      axes gridDepth order position).groupedRepeat
      (fun _ : Fin (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth) order copies)
    (hg : 0 < inputBlockWidth r (k+1) axes gridDepth)

set_option synthInstance.maxSize 4000
set_option maxHeartbeats 2000000

/-- Row-major original team indices of the wired bottom network. -/
noncomputable local instance columnBatchFinite {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j

variable (packet : ∀ hist, PacketPlacement (Port (EnrichedOuter.fan S) (Fin copies × Unit) T)
      cube.pred cd cube.b cube.h cube.copies (network p fit position free count M bottom installed hist))
    (bank : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → Ports (fun _ : FreeBlock R (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth))

local notation "G" => SewnTape.wiring p fit free ((h+2)*pin)
local notation "scalarIDs" => e.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width
local notation "Y" => (chart.gadgets ∘ Sum.inl)
local notation "Paths" => assignedPath (Gadget := scalarIDs) (cs := cube.width) p fit W position free count M bottom installed Y chart.preserves_paid
  Sum.inl hg packet Sum.inr bank
local notation "Terms" => assigned (Gadget := scalarIDs) (cs := cube.width) p fit W position free count M bottom installed Y chart.preserves_paid
  Sum.inl hg packet Sum.inr bank ord

/-- Combine the true numbered expansion and the accepted wired execution on exactly
the same pins, literal data, sorter, public history and private assignments. The
producer of a live column must supply its returning physical path bijections. -/
noncomputable def realizationOfWiredRuns
    (delivered : ∀ (raw : Raw) z, let lane := freeLane hg (gridRoom G Fintype.card_pos) z
      bank raw lane.1 lane.2 = freeBits G raw z)
    (id : TableEntry cube.pred cube.b cube.h cube.copies cube.width → ℕ) (gen : Fragment IO)
    (args : Fin (R+1) → UnitAddresses) (mac : TeamOpcode.Macros w 8)
    (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w) (limit burst : ℕ)
    (modes : ∀ j : Idx, signedContraction (G).slot ((codec).encode j) =
      (if (codec).encode j = (codec).encode reader.star then 1 else 0) +
        ∑ ext, ∏ u, positiveMaskedNativeValue G (signedBody id) mac pub reg args
          ((codec).encode j) limit burst ((k+1)^25) ext u)
    (reject : ∀ (j : Idx) ext, ¬ PositiveExterior G args ((codec).encode j) w ext →
      (∏ u, positiveMaskedNativeValue G (signedBody id) mac pub reg args
        ((codec).encode j) limit burst ((k+1)^25) ext u) = 0)
    (runs : ∀ j : Idx, reader.WiredPinExecution id gen G args mac pub reg limit burst Paths Terms j)
    (bounds : ∀ (raw : Raw) (a : Paths raw), let z := Terms raw a
      Fits (chart.pinRadius (R+1) r) (parameterShift z.exponents) ∧
      (∀ i, z.exponents i < 2^tally) ∧ (∀ g, ∑ u, z.counts u g < 2^mult) ∧ (∀ g, ∑ u, z.counts u g < 2^tally)) :
    reader.Realization (TeamContraction.cutWidth (k+1)+a) link (Wires.innerWidth r regs w ec width)
      (Wires.Edge r regs w ec width) where
  wiring := G
  Path i := Paths ((codec).encode i)
  pathFinite _ := inferInstance
  assigned i := Terms ((codec).encode i)
  expansion i := numbered_expansion (Gadget := scalarIDs) (cs := cube.width) p fit W position free count M bottom installed Y chart.preserves_paid
    Sum.inl hg packet Sum.inr _root_.id bank ord chart.gadgets (fun _ => rfl) (cube.chart_valid φ chart)
    ((codec).encode i) (delivered ((codec).encode i))
  column j := (runs j).column (modes j) (reject j) bounds

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
