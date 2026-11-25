import OAI.Computability.BorderVNP.FiniteProfilePinnedHeaders
import OAI.Computability.BorderVNP.FiniteProfilePublishedLabels

/-! # Slotted writer and chooser returned by the actual finite publication program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open PackedHistoryCircuit Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Packing.Directory Packing.Directory.PrivateBank GeometryAdvice DiagonalResidueRAM CubeHeaderInstall
open BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex
open scoped Classical

variable {R r lit link inner n w nt ng : ℕ} {Edge : Type} {Q Γ : Type} {K : Type*} [Field K]
variable (G : Wiring R r lit 0 link inner n Edge) (L : Routing.WireLayout (R+1) r link) (u : Fin (R+1))
variable (ext : Exterior R r link → Bool) (bank : Bank w)
variable (lib : Fin 8 → TeamSite.Macro Q Γ nt ng) (ret : FieldProcessor.Returns Q Γ K nt 8) (fuel : ℕ)

set_option maxRecDepth 7000 in
set_option maxHeartbeats 2500000 in
/-- For every actual accepted field profile, execute the two publication passes
on its own native memory, yielding the complete writer input and the corresponding
physical chooser placement, on exactly the same private placement return. -/
theorem FrontReceipt.published_writer {D s p depth k b v : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (task : SignedTaskArena.Layout) (dir : Directory.Layout) (N : Network D P bits) (cell : N.Site → Fin task.cube.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
    (F : Fields s task.cube.cables p task.cube.cells depth k b σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c,guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^b)
    (hk : k ≤ b) (widthFit : b ≤ w) (positive : 0<task.cube.cells)
    (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ t,bits (live t)=dir.block)
    (other : Arg → Word w) (old : Fin 81 → Word w) (gapIndex : 8<v) (controls : Fin v → Fin (2^b))
    (raw subt o start clock profile gates off ell : ℕ) (hdr : List Bool) (len : hdr.length=L.header) :
    let a := task.cube
    let A := ProfileArena.arena G L ([] : List (Word w))
    let outputs := a.cables*3+(RoutingOutputs.count a.cables a.cells dir.entries (dir.teams*dir.sites)+
      ((a.cells+(dir.entries+a.cells))+(v+o)))
    let fresh := A.next+7*dir.candidates
    let origin := Allocation.dest fresh profile gates outputs b
    let extra := signedProfileExtension task old dir origin a.cables a.cells raw u.val subt fresh profile gates outputs b off ell
    let B := ProfileArena.operands G L ([] : List (Word w)) extra Fin.elim0 start u
    let params := core (withDemandBase (task.routeBank A.frame other) A.next) origin a.cables a.cells
    let pub := B.bank params
    let fields := G.processorFields u Fin.elim0 ext A.ibase A.hbase A.dense
    let mac := TeamSiteEvents.macros lib fuel
    let f := G.transferFrame u L.header A.broadcastBase
    let h := privateLayout A.frame origin a.cables a.cells dir.entries dir.description (controls ⟨8,gapIndex⟩).val
    let tables := bases origin a.cables a.cells dir.entries
    let sc := Sum.elim (fun j : SuppliedWord N cell => j.1) (id : Fin a.cells → Fin a.cells)
    let sw := Sum.elim (supplyWidth N cell) (fun _ : Fin a.cells => (controls ⟨8,gapIndex⟩).val)
    let si := reserveID (C:=a.cells) (suppliedID N cell edgeID portID)
    B.Fits w → A.next < 2^w → a.stop < 2^w → fresh ≤ a.header.header →
    controlsBase origin a.cables a.cells dir.entries (dir.teams*dir.sites)+8<2^w →
    dir.teams=R+1 → dir.processors=r → dir.literal=G.program.length+lit → dir.link=link →
    dir.DestinationBounds → 0<dir.fields → dir.processors≤dir.sites → dir.entries≤dir.teams*dir.sites →
    dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2) →
    (∀ c, suppliedSize N cell c+(controls ⟨8,gapIndex⟩).val+dir.entries*dir.description ≤ a.cellStride) →
    ISA.wordBound (ISA.placementBound dir tables.privatePairs tables.livePairs a.cellStride)<2^w →
    a.cells ≤ 2^w → ∀ words : Fin outputs → ℕ, ∀ z : Returns profileFront pub mac bank (processorMemory fields w),
    FrontReceipt G u ext A.ibase A.hbase A.dense L.header A.broadcastBase pub bank lib ret fuel z A.copied extra
      hdr clock fresh origin words →
    Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings z.val.2.2) →
    readings z.val.2.2 (controlsBase origin a.cables a.cells dir.entries (dir.teams*dir.sites)+8)=(controls ⟨8,gapIndex⟩).val →
    ∃ (es fs : List (TeamRAM.Event w)) (mr fr : Bank w) (mid : Memory w),
      let pp := ISA.placement (readings mid) h.raw
      let lp := ISA.placement (readings mid) tables.livePairs
      let rows := dir.directory pp lp
      let out := ISA.publish mid A.frame A.next rows
      let lab := LabelIndex.layout A.frame (readings out)
      Runs pub mac PrivatePlacement.program z.val.2.1 z.val.2.2 es mr mid ∧
      h.Image (readings z.val.2.2) dir.entries (readings mid) ∧ h.Fits w (readings z.val.2.2) ∧
      Runs pub mac ISA.program mr mid fs fr out ∧
      Runs pub mac (.seq PrivatePlacement.program ISA.program) z.val.2.1 z.val.2.2 (es++fs) fr out ∧
      traceCost (es++fs) ≤ deliveryScanTicks dir.entries dir.teams dir.sites ∧
      (∀ e∈es++fs,e.choices=[] ∧ e.sign=.plus) ∧
      ProfileRouteInputs fields f pub (Pins.extendGuess (noPin G u A.ibase A.hbase A.dense)) out ∧
      LocalRow.BootPins pub f extra hdr out ∧
      (∃ writer : SlottedWriter a dir pp lp B.layout pub mid A.next (Sum.elim sc (cell ∘ original))
        (numbered si) (Sum.elim sw (fun _ => dir.description)), ∀ key,
        writer.placement.key key = key.elim Sum.inr (fun j => Sum.inl (Sum.inl (suppliedPort N cell (live j))))) ∧
      ∃ (count : lab.cells=a.cells) (ep : Endpoints lab (readings out))
        (edges : N.CrossingEdge cell ↪ Fin lab.cableCount) (del : Fin rows.length ≃ Fin lab.deliveryCount)
        (recv : Fin rows.length → Fin a.cells), (∀ i,(recv i).val=rows[i.val].cell) ∧
        RowPlacement (networkRows N cell recv (fun i => rows[i.val].width)) (fromTables lab (readings out) ep)
          (finCongr count.symm) (edges.sumMap del.toEmbedding) := by
  intro a A outputs fresh origin extra B params pub fields mac f h tables sc sw si fitted nextFit cubeFit
    headerFloor control dt dp dl dlink bounds fieldsPos procs entries tail cellRoom wordRoom cells words z receipt img gap
  let prev := pinFields (task.extension raw u.val subt old) (Allocation.stop fresh profile gates outputs b w)
    a.header.d (a.n+1) (a.h*a.b) a.header.blocks profile (declarationCap a.n a.header.d a.header.blocks a.b a.h a.s)
  have geom : extra=Allocation.fields (controlsExtension (directoryFields prev dir) origin a.cables a.cells dir.entries
      (dir.teams*dir.sites)) fresh profile gates outputs b off ell := signedProfileExtension_geometry ..
  have fd : fresh ≤ origin := by dsimp only [origin,Allocation.dest,Allocation.temp]; omega
  have nf : A.next ≤ fresh := Nat.le_add_right ..
  have ht : dir.teams ≤ 2^w := by rw [dt]; exact (fitted B.layout.teams (by simp [PacketOperands.values])).le
  have hp : dir.processors ≤ 2^w := by rw [dp]; exact (fitted B.layout.processors (by simp [PacketOperands.values])).le
  have hl : dir.literal < 2^w := by rw [dl]; exact fitted B.layout.literal (by simp [PacketOperands.values])
  have small : ISA.placementBound dir tables.privatePairs tables.livePairs a.cellStride < 2^w := by
    let v := ISA.placementBound dir tables.privatePairs tables.livePairs a.cellStride
    change 32*(v+1)^4 < 2^w at wordRoom
    nlinarith only [wordRoom,Nat.zero_le (v^4),Nat.zero_le (v^3),Nat.zero_le (v^2)]
  have wide : tables.livePairs<2^w ∧ a.cellStride<2^w := by dsimp only [ISA.placementBound] at small; omega
  have hf : dir.fields ≤ 2^w := by
    have count := bounds.fields
    have two : 2 ≤ 2^w := by
      dsimp only [StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense] at nextFit
      omega
    omega
  obtain ⟨base,host,head,controlAt,_⟩ := receipt.routing_headers G L u ext bank lib ret fuel task dir other old raw subt
    start clock fresh origin profile gates outputs b off ell hdr words fitted nf nextFit cubeFit control z
  have primary : A.frame+92<2^w := by
    dsimp only [StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense] at nextFit
    omega
  have ready := img.privateFit N cell aux siteID edgeID portID F net ids wireFit original (live ∘ finProdFinEquiv.symm)
    A.frame origin dir.description (controls ⟨8,gapIndex⟩).val (readings z.val.2.2) primary (by rw [controlAt]; exact control)
    wide.1 (fun c => (cellRoom c).trans_lt wide.2)
  have receipt' := receipt
  rw [geom] at receipt'
  obtain ⟨es,fs,mr,fr,mid,first,placed,second,joined,paid,ordinary,source,boot⟩ :=
    FrontReceipt.publish_image G L u ext bank lib ret fuel o v gapIndex dir N cell aux siteID edgeID portID F x net ids wireFit
      original (live ∘ finProdFinEquiv.symm) controls (task.routeBank A.frame other) prev start profile gates off ell
      a.cellStride clock hdr len fitted ⟨dt,dp,dl,dlink⟩ bounds (dt ▸ Nat.zero_lt_succ R) fieldsPos procs entries
      (by omega) control cellRoom wordRoom words z receipt' img gap
  rw [←geom] at boot
  let W := receipt.slottedNetwork G L u ext bank lib ret fuel task dir N cell aux siteID edgeID portID F x net
    ids wireFit original live liveWidth other extra start clock fresh origin (controls ⟨8,gapIndex⟩).val hdr words fitted nf
    (nf.trans fd) nextFit cubeFit host headerFloor dt dp dl fieldsPos tail bounds cellRoom z img ready mid placed
  refine ⟨es,fs,mr,fr,mid,first,placed,ready,second,joined,paid,ordinary,source,boot,⟨W,fun key => by cases key <;> rfl⟩,?_⟩
  have labels := slotted_label_placement a dir N cell aux siteID edgeID portID F x net ids wireFit hk widthFit positive
    original live liveWidth pub A.next origin (controls ⟨8,gapIndex⟩).val z.val.2.2 mid W img
    (base ▸ placed) (base ▸ ready) (base ▸ head) fd (by dsimp only [controlsBase,bases] at control; omega)
    ht hp hf hl cells wide.2.le
  rw [←base]
  exact labels

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
