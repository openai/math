import OAI.Computability.BorderVNP.DiagonalSignedSlottedNetwork
import OAI.Computability.BorderVNP.PackedHistoryDemandPublication

/-! # The actual signed demand publication and its slotted writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Packing.Directory Packing.Directory.PrivateBank
open scoped Classical BigOperators

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1600000 in
/-- The same true terminal image produces the two native publication runs, their
time bound, their exact final RAM, and the bounded sparse writer for this team.
The global addressing extent and the local cell stride can be charged separately. -/
theorem signed_publication {D s p depth k b w d : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    {σ : Type*} [Fintype σ] (task : SignedTaskArena.Layout) (dir : Directory.Layout)
    (N : Network D P bits) (cell : N.Site → Fin task.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
    (F : Fields s task.cube.cables p task.cube.cells depth k b σ) (x : σ → Bool)
    (net : CellAddressPhysical.Represents N cell aux siteID edgeID portID F x) (ids : ∀ c, (F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ t, bits (live t)=dir.block) (arena : StartupArena) (u : Fin arena.teams)
    (slot : ℕ) (packet : ReferencePacket w d) (other : Arg → Word w) (origin gap : ℕ)
    {f : BroadcastFrame} {advice : AdviceLayout} {hdr : List Bool} {z : Bank w} {saved profile : Memory w}
    (guess : ℕ → Bool) (extent : ℕ) (mac : TeamOpcode.Macros w 8) (reg : Bank w) :
    let B := arena.operands u slot packet
    let args := core (withDemandBase (task.routeBank arena.frame other) arena.next) origin task.cube.cables task.cube.cells
    let pub := B.bank args
    let pl := privateLayout arena.frame origin task.cube.cables task.cube.cells dir.entries dir.description gap
    let lo := (bases origin task.cube.cables task.cube.cells dir.entries).livePairs
    let sc := Sum.elim (fun v : SuppliedWord N cell => v.1) (id : Fin task.cube.cells → Fin task.cube.cells)
    let sw := Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)
    let si := reserveID (C := task.cube.cells) (suppliedID N cell edgeID portID)
    B.Fits w → arena.next+7*dir.candidates ≤ origin → task.cube.records < 2^w →
    (packet.extension (41 : Fin 81)).val = task.cube.hostDirectory →
    arena.next+7*dir.candidates ≤ task.cube.header.header →
    dir.teams=arena.teams → dir.processors=arena.processors → dir.literal=arena.literal → dir.link=arena.link → 0<dir.fields →
    dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2) → dir.DestinationBounds →
    (∀ c, suppliedSize N cell c+gap+(∑ j, if cell (original j)=c then dir.description else 0) ≤ task.cube.cellStride) →
    ∀ {fields : Pins.ProcessorFields B.layout}, JointHeader.BootHeaderState fields f advice packet pub hdr z saved →
    (∀ j < arena.next, profile j=Pins.preparedMemory B.layout guess saved B.layout.count j) →
    Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings profile) →
    Header arena.frame origin task.cube.cables task.cube.cells dir.entries (readings profile) →
    DirectoryHeader dir arena.frame profile →
    let controls := controlsBase origin task.cube.cables task.cube.cells dir.entries (dir.teams*dir.sites)
    readings profile (arena.frame+92) = controls → readings profile (controls+8) = gap →
    controls+8 < 2^w → 0 < dir.teams → dir.processors ≤ dir.sites → dir.entries ≤ dir.teams*dir.sites →
    (∀ c, suppliedSize N cell c+gap+dir.entries*dir.description ≤ extent) →
    Directory.ISA.wordBound (Directory.ISA.placementBound dir pl.raw lo extent) < 2^w →
    ∃ (es fs : List (TeamRAM.Event w)) (r₁ r₂ : Bank w) (mid : Memory w),
      let pp := Directory.ISA.placement (readings mid) pl.raw
      let lp := Directory.ISA.placement (readings mid) lo
      let final := Directory.ISA.publish mid arena.frame arena.next (dir.directory pp lp)
      Runs pub mac PrivatePlacement.program reg profile es r₁ mid ∧
      pl.Fits w (readings profile) ∧ pl.Image (readings profile) dir.entries (readings mid) ∧
      Runs pub mac Directory.ISA.program r₁ mid fs r₂ final ∧
      Runs pub mac (.seq PrivatePlacement.program Directory.ISA.program) reg profile (es++fs) r₂ final ∧
      traceCost (es++fs) ≤ deliveryScanTicks dir.entries dir.teams dir.sites ∧
      (∀ e ∈ es++fs, e.choices = [] ∧ e.sign = .plus) ∧
      ∃ writer : SlottedWriter task.cube dir pp lp B.layout pub mid arena.next (Sum.elim sc (cell ∘ original))
        (numbered si) (Sum.elim sw (fun _ => dir.description)), ∀ key,
          writer.placement.key key = key.elim Sum.inr (fun j => Sum.inl (Sum.inl (suppliedPort N cell (live j)))) := by
  intro B args pub pl lo sc sw si fits reserve recordsFit host rawRoom dt dp dl link fieldsPos tail bound
    localCap fields boot resident img header directory controls ptr gapAt controlRoom teams sites originals globalCap enough
  have same : (pub 0).val = arena.frame := B.frameBase_word _ fits
  have start : arena.frame+112 ≤ arena.next := by
    dsimp [StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]
    omega
  have prior : arena.next ≤ origin := (Nat.le_add_right ..).trans reserve
  have low : lo ≤ controls := by dsimp only [lo,controls,controlsBase]; omega
  have o : origin ≤ lo := by dsimp only [lo,bases]; omega
  have nextFit : arena.next < 2^w := (prior.trans (o.trans low)).trans_lt (by omega)
  let live₀ := live ∘ finProdFinEquiv.symm
  let num := Directory.ISA.placementBound dir pl.raw lo extent
  have small : num < 2^w := by
    refine lt_of_le_of_lt ?_ enough
    change num ≤ Directory.ISA.wordBound num
    unfold Directory.ISA.wordBound
    nlinarith [Nat.zero_le (num^4),Nat.zero_le (num^3),Nat.zero_le (num^2)]
  have extentRoom : extent < 2^w := (show extent ≤ num by dsimp only [num,Directory.ISA.placementBound]; omega).trans_lt small
  have frameRoom : arena.frame+92 < 2^w := by omega
  have fr := (resident_frames arena u slot packet guess same boot resident).1
  have dims : dir.teams=B.layout.teams ∧ dir.processors=B.layout.processors ∧
      dir.literal=B.layout.literal ∧ dir.link=B.layout.link := ⟨dt,dp,dl,link⟩
  obtain ⟨shape,base⟩ := decoded_demand_header dir B (task.routeBank arena.frame other) arena.next origin
    task.cube.cables task.cube.cells profile dims fits nextFit fieldsPos fr (same ▸ directory)
  have ready := img.privateFit N cell aux siteID edgeID portID F net ids wireFit original live₀ arena.frame origin
    dir.description gap (readings profile) frameRoom (ptr ▸ controlRoom) (low.trans_lt (by omega))
    (fun c => (globalCap c).trans_lt extentRoom)
  have made := img.publish_directory dir N cell aux siteID edgeID portID F net ids wireFit original live₀ origin
    arena.next gap extent pub mac reg profile (same ▸ header) shape base (by rw [same,ptr]; exact gapAt)
    (by rw [same,ptr]; exact controlRoom) (by rw [same]; omega) reserve bound teams fieldsPos sites originals globalCap enough
  rw [same] at made
  obtain ⟨es,fs,r₁,r₂,mid,first,middle,second,both,cost,events⟩ := made
  refine ⟨es,fs,r₁,r₂,mid,first,ready,middle,second,both,cost,events,?_⟩
  refine ⟨signedSlottedWriter task dir N cell aux siteID edgeID portID F x net ids wireFit original live liveWidth
    arena u slot packet other origin gap guess fits prior nextFit recordsFit host rawRoom dt dp dl fieldsPos tail
    bound localCap boot resident img ready middle,?_⟩
  intro key
  cases key <;> rfl

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
