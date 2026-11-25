import OAI.Computability.BorderVNP.DiagonalNativeArgumentCells
import OAI.Computability.BorderVNP.DiagonalProducedRoster

/-! # Private cells at the actual sparse argument producer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch CompactMachine CellSparse CellPacket TypedTaskBuilder
open CellPacket.Supplement.Batch

variable {w n : ℕ} {Site : Type} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (a : SignedTaskArena.Layout) (l : CellControlRows.Layout) (raw : ℕ → ℕ)
    (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record) (cells : ℕ → SparseExterior.Owned)

set_option maxHeartbeats 1400000

/-- The native exterior writer keeps the frame count, team, call pointer and
every global owner word. This also holds before the last seven-word publication. -/
theorem SparseCallInput.compressed_roster (src : SparseCallInput pub m) (f : Frame) (owner : ℕ → ℕ)
    (old : OwnerTable pub (written m src.merge src.count) f owner)
    (registers : ∀ i < src.layout.count, ∀ k ∈ [0,14,15], (src.owned i).Outside src.layout i (src.layout.frame+k))
    (owners : ∀ i < src.layout.count, ∀ j < f.count, (src.owned i).Outside src.layout i (f.address j)) :
    OwnerTable pub src.compressed f owner := by
  let patched := written m src.merge src.count
  have keep (x : ℕ) (clear : ∀ i < src.layout.count, (src.owned i).Outside src.layout i x) :
      src.compressed x=patched x := by
    apply Fin.ext
    change readings src.compressed x=readings patched x
    rw [src.image]
    exact SparseExterior.written_preserve src.layout src.owned (readings patched) (i:=0) (Nat.zero_le _) x
      (fun i _ hi => clear i hi)
  exact old.kept (fun k hk => keep _ (src.root ▸ fun i hi => registers i hi k hk))
    (fun i hi => keep _ (fun j hj => owners j hj i hi))

/-- The burst slot at a compact ordinal contains the supplemented logical
cell at the native global owner row. Its suffix is the physical span and
report encoding selected by that row. -/
theorem produced_call_burst (j : ℕ) :
    let i := globalCell l.toLayout raw j
    let row := produced l raw p geom extra j
    let layout := SparseExterior.batchLayout a l.frame l.control (l.before raw l.cells)
    let input := SparseExterior.logicalCell (p i) (extra i) (cells i).field
    (((cells i).typed layout row.typed).cell.burst w) =
      CompactFrame.pack w (Packet.input input.directory input.privateWires (cells i).field.bytes) := by
  intro i row layout input
  exact congrArg (fun packet => CompactFrame.pack w
    (RationalHitting.StackLanguage.codeWord packet ++ (cells i).field.bytes))
    (SparseExterior.supplemented_packet (l.atCell raw p i) (extra i) (cellLayout l raw i) (geom i))

/-- The scheduled physical word allowance on the owner rows supplies the
burst hypothesis of the native argument producer for its complete table. -/
theorem produced_call_cap
    (cap : ∀ i < l.cells, l.owner raw i=l.team →
      let input := SparseExterior.logicalCell (p i) (extra i) (cells i).field
      (CompactFrame.pack w (Packet.input input.directory input.privateWires (cells i).field.bytes)).length ≤
        TeamScales.width n (1/2)) :
    let layout := SparseExterior.batchLayout a l.frame l.control (l.before raw l.cells)
    ∀ j < l.before raw l.cells, let i := globalCell l.toLayout raw j
      (((cells i).typed layout (produced l raw p geom extra j).typed).cell.burst w).length ≤ TeamScales.width n (1/2) := by
  intro layout j hj i
  have ordinal := global_spec l.toLayout raw hj
  exact (congrArg List.length (produced_call_burst (w := w) a l raw p geom extra cells j)).le.trans
    (cap i ordinal.1 ordinal.2.1)

/-- Read the global roster in any sparse memory returned with the producer's
actual occupied row names and layout. No identity of the input witness
constructed by a prior existential choice is needed. -/
theorem ProducedRoster.compressed {src : SparseCallInput pub m} (roster : ProducedRoster a l raw p geom extra src)
    (fp : (pub 0).val=l.frame) (image : readings m=l.toLayout.published raw)
    (calls : l.calls=a.before.limit) (cellsFit : l.cells≤a.cube.cells) :
    OwnerTable pub src.compressed ⟨l.team,l.calls,l.cells⟩ (l.owner raw) := by
  let f := Frame.mk l.team l.calls l.cells
  have old : OwnerTable pub (written m src.merge src.count) f (l.owner raw) := by
    rw [roster.merge,roster.count]
    exact ownerTable_supplemented l raw p geom extra fp roster.fields roster.room image roster.span roster.frameLow roster.callsHigh
  have protectedRows := SparseExterior.frame_owners_outside a l.frame l.control src.count src.owned f
    roster.globals roster.widths roster.early calls cellsFit
  exact src.compressed_roster pub m f _ old (by
    rw [roster.layout]
    intro i hi j member
    exact protectedRows.1 i hi j (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega))
    (by rw [roster.layout]; exact protectedRows.2)

/-- The actual compressed memory retains the entire global owner column. -/
theorem SparseCallInput.ofOwned_compressed
    {fp fields room image word hdr fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh
      controlLo controlHi ctrlSorted ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap} :
    let src := SparseCallInput.ofOwned (n:=n) pub mac s m a l raw p geom extra cells fp fields room image
      word hdr fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh controlLo controlHi
      ctrlSorted ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap
    OwnerTable pub src.compressed ⟨l.team,l.calls,l.cells⟩ (l.owner raw) := by
  let src := SparseCallInput.ofOwned (n:=n) pub mac s m a l raw p geom extra cells fp fields room image word hdr
    fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh controlLo controlHi ctrlSorted
    ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap
  have kept : ProducedRoster a l raw p geom extra src := SparseCallInput.ofOwned_roster a l raw p geom extra cells
  exact kept.compressed pub m a l raw p geom extra fp image callBase cellCount.le

/-- The actual owned-row producer determines the typed source, physical
compressed operand, and its logical supplemented input at the same global
cell. Only owned rows require the private time bound. -/
noncomputable def SparseCallInput.ofOwnedCells
    {fp fields room image word hdr fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh
      controlLo controlHi ctrlSorted ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap}
    (paid : ∀ i < l.cells, l.owner raw i=l.team →
      let c := SparseExterior.logicalCell (p i) (extra i) (cells i).field
      c.directory.ProfileWidths ∧ SparseExterior.clock w c.directory c.privateWires (cells i).field ≤ n^25) :
    SparseArgumentCells n (SparseCallInput.ofOwned (n:=n) pub mac s m a l raw p geom extra cells fp fields room image
      word hdr fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh controlLo controlHi
      ctrlSorted ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap) := by
  let src := SparseCallInput.ofOwned (n:=n) pub mac s m a l raw p geom extra cells fp fields room image word hdr
    fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh controlLo controlHi ctrlSorted
    ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap
  have roster : OwnerTable pub src.compressed ⟨l.team,l.calls,l.cells⟩ (l.owner raw) :=
    SparseCallInput.ofOwned_compressed pub mac s m a l raw p geom extra cells
  refine ⟨Site,p,extra,(fun i => (cells i).field),rfl,?_,?_,?_⟩
  · rw [roster.frame]
    exact (Nat.le_of_lt room.calls)
  · intro i _ _
    rfl
  · intro i hi mine
    change i < (Frame.ofMemory pub src.compressed).count at hi
    change readings src.compressed ((Frame.ofMemory pub src.compressed).address i)=(Frame.ofMemory pub src.compressed).team at mine
    rw [roster.frame] at hi mine
    exact paid i hi ((roster.atRow i hi).symm.trans mine)

/-- The same logical cells for a producer supplied with a full array of fields. -/
noncomputable def SparseCallInput.ofProducedCells
    {fp fields room image word hdr fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh
      controlLo controlHi ctrlSorted ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap}
    (paid : ∀ i < l.cells, l.owner raw i=l.team →
      let c := SparseExterior.logicalCell (p i) (extra i) (cells i).field
      c.directory.ProfileWidths ∧ SparseExterior.clock w c.directory c.privateWires (cells i).field ≤ n^25) :
    SparseArgumentCells n (SparseCallInput.ofProduced (n:=n) pub mac s m a l raw p geom extra cells fp fields room image
      word hdr fourRoom table four callBase cellCount reportCount controller span frameLow callsHigh controlLo controlHi
      ctrlSorted ctrlMerged early mergeFields ranges global extent spans tails inputs intervals region arenas cap) :=
  SparseCallInput.ofOwnedCells pub mac s m a l raw p geom extra cells paid

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
