import OAI.Computability.BorderVNP.FiniteProfileRouteSources
import OAI.Computability.BorderVNP.FiniteProfileArena
import OAI.Computability.BorderVNP.PackedHistoryDemandPublication
import OAI.Computability.BorderVNP.CubeISALocalRowPinnedBoot

/-! # Publishing the real finite candidate's delivery rows after its unique prefix

The finite bootstrap installs its ordinary demand pointer and all routing extension words.
Its guarded geometry outputs the actual network arrays and secondary controls. Two native
passes then place the immutable private data and publish the occupied seven-word requests.
The next scheduler reads the original processor rows and the same broadcast declaration.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM VerifierNetwork RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open Crossing Packing Packing.RoutingOutputs Diagonal.ExternalSew.FieldExport PackedHistoryCircuit GeometryAdvice
open GeometryFrameEncoding DiagonalResidueRAM

variable {R r lit link inner n W nt ng : ℕ} {Edge : Type} {Q Γ : Type} {K : Type*} [Field K]
variable (G : Wiring R r lit 0 link inner n Edge) (L : Routing.WireLayout (R+1) r link) (u : Fin (R+1))
variable (ext : Exterior R r link → Bool) (bank : Bank W) (lib : Fin 8 → TeamSite.Macro Q Γ nt ng)
variable (ret : FieldProcessor.Returns Q Γ K nt 8) (fuel : ℕ)
variable {dim s m p C d k b o : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {S Z : Type*} [Fintype S] [Fintype Z]

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1600000 in
/-- On an actual accepted finite profile, run the private placement and demand scanner
in one RAM, retaining the routed inputs and cube header at their real addresses. -/
theorem FrontReceipt.publish_image (o v : ℕ) (gapIndex : 8<v) (D : Directory.Layout) (N : Network dim P bits) (cell : N.Site → Fin C)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin p)
    (F : CellAddressCircuit.Fields s m p C d k b Z) (input : Z → Bool)
    (rep : CellAddressPhysical.Represents N cell aux siteID edgeID portID F input)
    (ids : ∀ c, (F.cells c).val = c.val) (wireFit : ∀ c,
      CellAddresses.guessedSize N cell c+CellAddresses.siteSize N cell c aux+CellAddresses.suppliedSize N cell c < 2^b)
    (original : Fin D.entries → N.Site) (live : Fin (D.teams*D.sites) → P)
    (controls : Fin v → Fin (2^b))
    (other : Arg → Word W) (old : Fin 81 → Word W) (start reserve gates off ell extent pinClock : ℕ)
    (headerBits : List Bool) (length : headerBits.length=L.header) :
    let a := ProfileArena.arena G L ([] : List (Word W))
    let liveCount := D.teams*D.sites
    let outputs := m*3+(RoutingOutputs.count m C D.entries liveCount+((C+(D.entries+C))+(v+o)))
    let fresh := a.next+7*D.candidates
    let origin := Allocation.dest fresh reserve gates outputs b
    let extra := Allocation.fields (controlsExtension (directoryFields old D) origin m C D.entries liveCount)
      fresh reserve gates outputs b off ell
    let ops := ProfileArena.operands G L ([] : List (Word W)) extra Fin.elim0 start u
    let pub := ops.bank (core (withDemandBase other a.next) origin m C)
    let f := G.transferFrame u L.header a.broadcastBase
    let fields := G.processorFields u Fin.elim0 ext a.ibase a.hbase a.dense
    let native := TeamSiteEvents.macros lib fuel
    let t := bases origin m C D.entries
    let pl := privateLayout a.frame origin m C D.entries D.description (controls ⟨8,gapIndex⟩).val
    ops.Fits W → D.teams = ops.layout.teams ∧ D.processors = ops.layout.processors ∧
      D.literal = ops.layout.literal ∧ D.link = ops.layout.link →
    D.DestinationBounds → 0<D.teams → 0<D.fields → D.processors≤D.sites → D.entries≤liveCount →
    D.fields-1<2^W → controlsBase origin m C D.entries liveCount+8<2^W →
    (∀ c, CellAddresses.suppliedSize N cell c+(controls ⟨8,gapIndex⟩).val+D.entries*D.description ≤ extent) →
    Directory.ISA.wordBound (Directory.ISA.placementBound D t.privatePairs t.livePairs extent) < 2^W →
    ∀ words : Fin outputs → ℕ, ∀ z : Returns profileFront pub native bank (processorMemory fields W),
      FrontReceipt G u ext a.ibase a.hbase a.dense L.header a.broadcastBase pub bank lib ret fuel z a.copied extra
        headerBits pinClock fresh origin words →
      Image F (siteID ∘ original) (portID ∘ live) input origin (readings z.val.2.2) →
      readings z.val.2.2 (controlsBase origin m C D.entries liveCount+8) = (controls ⟨8,gapIndex⟩).val → ∃ (es fs : List (TeamRAM.Event W)) (midReg finalReg : Bank W) (mid : Memory W),
      let rows := D.directory (Directory.ISA.placement (readings mid) t.privatePairs) (Directory.ISA.placement (readings mid) t.livePairs)
      let result := Directory.ISA.publish mid a.frame a.next rows
      Runs pub native PrivatePlacement.program z.val.2.1 z.val.2.2 es midReg mid ∧ pl.Image (readings z.val.2.2) D.entries (readings mid) ∧
      Runs pub native Directory.ISA.program midReg mid fs finalReg result ∧
      Runs pub native (.seq PrivatePlacement.program Directory.ISA.program) z.val.2.1 z.val.2.2 (es++fs) finalReg result ∧
      traceCost (es++fs) ≤ deliveryScanTicks D.entries D.teams D.sites ∧ (∀ ev ∈ es++fs, ev.choices = [] ∧ ev.sign = .plus) ∧
      ProfileRouteInputs fields f pub (Pins.extendGuess (noPin G u a.ibase a.hbase a.dense)) result ∧
      LocalRow.BootPins pub f extra headerBits result := by
  intro a liveCount outputs fresh origin extra ops pub f fields native t pl fit dims bounds teams positive sites originalCap fieldFit
    controlRoom cap wordRoom words z receipt img reportGap
  have base : (pub 0).val = a.frame := ops.frameBase_word _ fit
  have fr : a.frame+112 ≤ a.broadcastBase := by change a.frame+112≤a.frame+112+a.copied; omega
  have index : a.broadcastBase+L.header = a.ibase := rfl
  have last : a.ibase+a.count = a.hbase := rfl
  have limit : a.hbase+a.count = a.next := rfl
  have count : (G.pinLayout u a.ibase a.hbase a.dense).count = a.count := rfl
  have prior : a.next+7*D.candidates ≤ origin := by dsimp only [origin,fresh,Allocation.dest,Allocation.temp]; omega
  have sourceData := receipt.route_sources G u ext a.ibase a.hbase a.dense L.header a.broadcastBase pub bank lib ret fuel
    (base ▸ fr) (by omega) (by omega) (by dsimp only [fresh]; rw [count]; omega)
  obtain ⟨inputs,ordinary,extension⟩ := sourceData
  have routing := routing_frame_of_words ops (withDemandBase other a.next) (directoryFields old D) origin m C D.entries liveCount
    fresh reserve gates outputs b off ell z.val.2.2 (by omega) ordinary extension
  let upper := Directory.ISA.placementBound D t.privatePairs t.livePairs extent
  have small : upper < 2^W := by
    have bound : 32*(upper+1)^4<2^W := wordRoom
    nlinarith only [bound,Nat.zero_le (upper^4),Nat.zero_le (upper^3),Nat.zero_le (upper^2)]
  have size : D.entries<2^W ∧ D.sites<2^W ∧ D.block<2^W ∧ D.description<2^W ∧ D.fields-1<2^W := by
    dsimp only [upper,Directory.ISA.placementBound,Directory.Layout.candidates] at small; omega
  obtain ⟨head,ptr,dh⟩ := routing_directory old D routing size
  have low : a.next < 2^W := by dsimp only [controlsBase,bases] at controlRoom; omega
  obtain ⟨shape,demandBase⟩ := decoded_demand_header D ops other a.next origin m C z.val.2.2 dims fit low positive ordinary dh
  have made := img.publish_directory D N cell aux siteID edgeID portID F rep ids wireFit original live origin a.next
    (controls ⟨8,gapIndex⟩).val extent pub native z.val.2.1 z.val.2.2 head shape demandBase (by rw [ptr]; exact reportGap)
    (by rw [ptr]; exact controlRoom) (by rw [base]; omega) prior bounds teams positive sites originalCap cap wordRoom
  rw [base] at made
  obtain ⟨es,fs,midReg,finalReg,mid,p1,place,p2,joined,paid,plain⟩ := made
  refine ⟨es,fs,midReg,finalReg,mid,p1,place,p2,joined,paid,plain,?_⟩
  let rows := D.directory (Directory.ISA.placement (readings mid) t.privatePairs) (Directory.ISA.placement (readings mid) t.livePairs)
  have keep := directoryPublished_low rows place ((Nat.le_add_right ..).trans prior)
  have inputLength : fields.header.length = a.frame := by
    rw [Pins.ProcessorFields.header_length]
    change r*((G.program.length+lit)+(R+1-1)*link+(G.program.length+lit)) = r*(2*(G.program.length+lit)+(R+1-1)*link)
    ring
  have pinInput : ProfileRouteInputs fields f pub (Pins.extendGuess (noPin G u a.ibase a.hbase a.dense))
      (Directory.ISA.publish mid a.frame a.next rows) := by
    apply inputs.congr
    · intro i hi; rw [inputLength] at hi; exact keep i (by omega) (by omega)
    · intro i hi; change i<a.count at hi; exact keep _ (by change a.ibase+i<a.next; omega) (by change a.ibase+i ≠ a.frame+9; omega)
    · intro j hj; rw [base]; simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; exact keep _ (by omega) (by omega)
  refine ⟨pinInput,⟨pinInput.broadcast.1,pinInput.broadcast.2.1,pinInput.broadcast.2.2.2.2.2.2,fun j => ?_,fun j => ?_⟩⟩
  · have hj := j.isLt
    rw [base] at extension ⊢
    exact (keep _ (by omega) (by omega)).trans (extension j)
  · have hj := j.isLt
    have valid : j.val < L.header := hj.trans_eq length
    exact (keep _ (by change a.broadcastBase+j.val<a.next; omega) (by change a.broadcastBase+j.val ≠ a.frame+9; omega)).trans
      (receipt.headerAt j)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1600000 in
/-- On an actual accepted finite profile, run the private placement and demand scanner
in one RAM, retaining the routed inputs and cube header at their real addresses. -/
theorem FrontReceipt.publish_demands (D : Directory.Layout) (N : Network dim P bits) (cell : N.Site → Fin C)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin p)
    (F : CellAddressCircuit.Fields s m p C d k b (S ⊕ Bool)) (source : Frame Z S) (input : Z → Bool)
    (rep : CellAddressPhysical.Represents N cell aux siteID edgeID portID F ((withSewnFields source).eval input))
    (ids : ∀ c, (F.cells c).val = c.val) (wireFit : ∀ c,
      CellAddresses.guessedSize N cell c+CellAddresses.siteSize N cell c aux+CellAddresses.suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (width : b ≤ W) (original : Fin D.entries → N.Site) (live : Fin (D.teams*D.sites) → P)
    (controls : Fin 28 → Fin (2^b)) (rest : Frame (S ⊕ Bool) (Outputs o b))
    (other : Arg → Word W) (old : Fin 81 → Word W) (start reserve gates off ell extent pinClock : ℕ)
    (headerBits : List Bool) (length : headerBits.length=L.header) :
    let a := ProfileArena.arena G L ([] : List (Word W))
    let liveCount := D.teams*D.sites
    let outputs := m*3+(RoutingOutputs.count m C D.entries liveCount+((C+(D.entries+C))+(28+o)))
    let fresh := a.next+7*D.candidates
    let origin := Allocation.dest fresh reserve gates outputs b
    let extra := Allocation.fields (controlsExtension (directoryFields old D) origin m C D.entries liveCount)
      fresh reserve gates outputs b off ell
    let ops := ProfileArena.operands G L ([] : List (Word W)) extra Fin.elim0 start u
    let pub := ops.bank (core (withDemandBase other a.next) origin m C)
    let f := G.transferFrame u L.header a.broadcastBase
    let fields := G.processorFields u Fin.elim0 ext a.ibase a.hbase a.dense
    let native := TeamSiteEvents.macros lib fuel
    let words := fun i => ParseBatchSort.value (fun j => (controlEmitter F hk (siteID ∘ original) (portID ∘ live)
      rest source controls).eval input (i,j))
    let t := bases origin m C D.entries
    let pl := privateLayout a.frame origin m C D.entries D.description (controls 8).val
    ops.Fits W → D.teams = ops.layout.teams ∧ D.processors = ops.layout.processors ∧
      D.literal = ops.layout.literal ∧ D.link = ops.layout.link →
    D.DestinationBounds → 0<D.teams → 0<D.fields → D.processors≤D.sites → D.entries≤liveCount →
    D.fields-1<2^W → controlsBase origin m C D.entries liveCount+8<2^W →
    (∀ c, CellAddresses.suppliedSize N cell c+(controls 8).val+D.entries*D.description ≤ extent) →
    Directory.ISA.wordBound (Directory.ISA.placementBound D t.privatePairs t.livePairs extent) < 2^W →
    ∀ z : Returns profileFront pub native bank (processorMemory fields W),
      FrontReceipt G u ext a.ibase a.hbase a.dense L.header a.broadcastBase pub bank lib ret fuel z a.copied extra
        headerBits pinClock fresh origin words → ∃ (es fs : List (TeamRAM.Event W)) (midReg finalReg : Bank W) (mid : Memory W),
      let rows := D.directory (Directory.ISA.placement (readings mid) t.privatePairs) (Directory.ISA.placement (readings mid) t.livePairs)
      let result := Directory.ISA.publish mid a.frame a.next rows
      Runs pub native PrivatePlacement.program z.val.2.1 z.val.2.2 es midReg mid ∧ pl.Image (readings z.val.2.2) D.entries (readings mid) ∧
      Runs pub native Directory.ISA.program midReg mid fs finalReg result ∧
      Runs pub native (.seq PrivatePlacement.program Directory.ISA.program) z.val.2.1 z.val.2.2 (es++fs) finalReg result ∧
      traceCost (es++fs) ≤ deliveryScanTicks D.entries D.teams D.sites ∧ (∀ ev ∈ es++fs, ev.choices = [] ∧ ev.sign = .plus) ∧
      ProfileRouteInputs fields f pub (Pins.extendGuess (noPin G u a.ibase a.hbase a.dense)) result ∧
      LocalRow.BootPins pub f extra headerBits result := by
  intro a liveCount outputs fresh origin extra ops pub f fields native words t pl fit dims bounds teams positive sites originalCap fieldFit
    controlRoom cap wordRoom z receipt
  obtain ⟨img,_,control⟩ := profile_controls F hk (siteID ∘ original) (portID ∘ live) rest source controls input origin z.val.2.2 width receipt.rows
  exact FrontReceipt.publish_image G L u ext bank lib ret fuel o 28 (by decide) D N cell aux siteID edgeID portID F
    ((withSewnFields source).eval input) rep ids wireFit original live controls other old start reserve gates off ell extent
    pinClock headerBits length fit dims bounds teams positive sites originalCap fieldFit controlRoom cap wordRoom words z receipt img (control 8)

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
