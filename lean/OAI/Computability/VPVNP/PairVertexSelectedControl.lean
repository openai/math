import OAI.Computability.VPVNP.PairTraversalPreorderBounds
import OAI.Computability.VPVNP.PairTraversalReadFootprint
import OAI.Computability.VPVNP.PairSelectedPacketOrders

/-! # Control and root packets on the actual selected descriptor layers -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open BurstRAM DFS Compression LocalHistory NetworkKernel TreeDecode
open CompressorRecords.SourceTransport TerminalFootprint
open scoped Fin.CommRing
open private addTree from OAI.Computability.VPVNP.PairTraversalHistory

variable {k A : Type*} [Field k] [CommRing A] {S : BlockSchedule k}
    (B : S.Templates) (κ : B.Entry → A) (hκ : B.IsSolution κ) {lanes : ℕ}
    (T : ℕ) (hT : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute κ hκ T hT X).Choices) (base : ℕ)

/-- The branch-specific chain of DFS row pointers after the initial layer, using the actual
selected site orders and record pitch. -/
noncomputable abbrev selectedPointers :=
  let E := B.execute κ hκ T hT X
  let recs := B.records κ hκ T hT X
  chainPointers B.recordLimit (E.termChain recs z) (branchOrders E recs z)
    (address B.recordLimit base (siteOrder X).length)

private theorem root_address {L : Type} [Fintype L] {f : L → A} {N Y : Network}
    (c : TermChain A N Y) (r : ChainParsers f c) (ptr : RowPointers c) (trees : N.Site → VertexTree)
    (v : Y.Site) : (chainTrees c r ptr trees v).address = lastRowAddresses c ptr (fun u => (trees u).address) v := by
  induction c with
  | done => rfl
  | more t rec tail ih => exact ih r.2 ptr.2 (addTree r.1 ptr.1 trees) v

/-- The packet consumed at the physical final root has the selected address
and the actual independent half-wire bits in numerical slot order. -/
theorem selected_rootPacket :
    let E := B.execute κ hκ T hT X
    let c := E.termChain (B.records κ hκ T hT X) z
    let r := selectedParsers B κ hκ T hT X z
    let ptr := selectedPointers B κ hκ T hT X z base
    let leaf := sitePointers B.recordLimit base (siteOrder X)
    let frames := fromRows c r ptr (fun v => (leaf v).1) (NodeArguments.packed (E.finalState z))
    ∀ v y, finalPackets c frames.2 frames.1 v y =
      ⟨(selectedTrees B κ hκ T hT X z base v).address, NodeArguments.packed (E.finalState z) v y⟩ := by
  intro E c r ptr leaf frames v y
  rw [show finalPackets c frames.2 frames.1 = _ from fromRows_final c r ptr _ _]
  exact congrArg (fun a => NodeArguments.Packet.mk a _) (root_address c r ptr (fun u => leafTree (leaf u)) v).symm

/-- The real preimage table supplies a DFS visit on the caller's stack.
Its exact control trace fits the worker address space and visits at most
the occurrence budget of the selected compression branch. -/
theorem selected_control {w : ℕ} (m : Memory w) (H : Word w) (stack : ℕ)
    (rows : AllRows w m B.recordLimit base base (selectedLayers B κ hκ T hT X z))
    (space : base+words B.recordLimit (selectedLayers B κ hκ T hT X z) ≤ H.val)
    (fit : H.val+31 < 2^w) (capacity : B.growthConstant^T ≤ stack) :
    let E := B.execute κ hκ T hT X
    let c := E.termChain (B.records κ hκ T hT X) z
    let trees := selectedTrees B κ hκ T hT X z base
    ∀ v, ∃ es, Visits m stack [((trees v).address : Word w)]
        ((trees v).preorder.map (fun a : ℕ => (a : Word w))) es ∧
      Reads (TerminalLink.workerCell H) es ∧ (trees v).preorder.length ≤ c.occurrences (fun _ => 1) v ∧
      es.length + 5 = 15*(trees v).preorder.length+1 ∧ countProbes es + 1 = 3*(trees v).preorder.length := by
  intro E c trees v
  let r := selectedParsers B κ hκ T hT X z
  let ptr := selectedPointers B κ hκ T hT X z base
  let initial := siteOrder X
  let leaf := sitePointers B.recordLimit base initial
  let old := fun u => leafTree (leaf u)
  have hl : ∀ u, (old u).rows w m := fun u => leafTree_rows (rows.1 (initial.entries.symm u)).1
    (rows.1 (initial.entries.symm u)).2
  have hr := chainPointers_rowsAt c r (branchOrders E (B.records κ hκ T hT X) z) initial
    B.recordLimit base (address B.recordLimit base initial.length) m rows.2
  have len := chainTrees_length c r ptr old (fun _ => 1) (fun _ => le_rfl) v
  have room := (B.branch_bounds κ hκ T hT X z).2.2.2.1 v
  obtain ⟨es,run⟩ := (trees v).visits stack (chainTrees_rows c r ptr m old hl hr v) (len.trans (room.trans capacity))
  have support := run.reads_of_row_bounds (selected_preorder_word_bounds B κ hκ T hT X z base H.val m
    rows space H.isLt.le v)
  obtain ⟨probes,time⟩ := run.cost
  exact ⟨es, run, reads_mono support (fun _ => below H fit), len, by simpa using time, by simpa using probes⟩

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
