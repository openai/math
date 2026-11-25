import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenProfile

/-! # Reading the physical control and sort operands appended to the frozen terminal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM VerifierNetwork GeometryFrameEncoding ParseBatchSort Packing PackedHistoryCircuit
open CellPacketGeometry BottomReports BundleSort RoutingOutputs Crossing CellAddresses CellAddressCircuit
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport

variable {Z : Type*} [Fintype Z] {W r s n d k bits b frame origin next gap team R : ℕ}
variable {P : Type} [Fintype P] {len : P → ℕ} {N M : Network r P len}
variable (t : SignedTaskArena.Layout) (D : Directory.Layout) (axis : Fin (t.cube.n+1))
variable (pp lp : ℕ → ℕ × ℕ) (retain : Retains N M) (cell : M.Site → Fin t.cube.cells)
variable (aux : M.Site → ℕ) (siteID : M.Site ↪ Fin s) (edgeID : M.Edge ↪ Fin t.cube.cables) (portID : P ↪ Fin n)
variable (original : Fin D.entries → N.Site) (live : Fin (D.teams*D.sites) → P)
variable (F : Fields s t.cube.cables n t.cube.cells d k bits Z) (x : Z → Bool)
variable (shape : Fin D.entries → Shape) (valid : Frame Z Unit)
variable (profile placed : Memory W) (entry : ℕ → ℕ)

local notation "ctrl" => controlsBase origin t.cube.cables t.cube.cells D.entries (D.teams*D.sites)
local notation "tables" => bases origin t.cube.cables t.cube.cells D.entries
local notation "l" => privateLayout frame origin t.cube.cables t.cube.cells D.entries D.description gap
local notation "banks" => t.cube.cellWriter frame ctrl axis
local notation "pubMem" => readings (Directory.ISA.publish placed frame next (D.directory pp lp))

/-- The signed geometry producer may append its two pre-sorted bundle banks
after the complete cell packet. Their actual emitted words, together with the
routing image and the 37 controls on that same profile run, determine all
original absolute slot and incidence fields in the post-directory RAM. -/
theorem NativeEntry.open_sources_of_frozen_words {inputMem : ℕ → ℕ}
    (native : NativeEntry t.cube frame ctrl axis R inputMem pubMem entry)
    (room : t.OpenRoom frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries (2^b) W)
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin)
    (payload : ctrl ≤ t.p.bundlePayload) (rank : t.p.bundleInverse=t.p.bundlePayload+2^b)
    (fitControls : ∀ i : Fin 37, t.controls i.val < 2^bits)
    (frameWords : t.OpenFields team frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries (readings profile))
    (place : (l).Image (readings profile) D.entries (readings placed))
    (positive : 0<t.cube.header.d) (keysFit : t.cube.cells < 2^k)
    (descFit : D.description < 2^bits) (scanFit : 2^Nat.clog 2 D.entries*D.description < 2^bits)
    (copies : ∀ i, (shape i).copies < 2^bits)
    (stride : ∀ i, bottomStride ((shape i).fine+(shape i).incoming) (shape i).cap < 2^bits)
    (codes : ∀ c, (F.cells c).val=c.val)
    (cellFit : ∀ c, guessedSize M cell c+siteSize M cell c aux+suppliedSize M cell c < 2^bits)
    (capacity : ∀ c, suppliedSize M cell c+gap+Directory.DataSlabs.size (cell ∘ retain.site ∘ original)
      (fun _ => D.description) c ≤ t.cube.cellStride) :
    let host := fun i => retain.site (original i)
    let old := siteID ∘ host
    let header := fun i => geometryHeader retain siteID F (x:=x) (l) entry t.cube.hostDirectory original i
      (shape i).copies (shape i).fine (shape i).incoming (shape i).cap
    let up := geometryHeaders F old D.description (bankConfig (banks) gap valid) shape
    CellAddressPhysical.Represents M cell aux siteID edgeID portID F x →
    Image F old (portID ∘ live) x origin (readings profile) →
    (∀ j : Fin 37, readings profile (ctrl+j.val)=t.controls j.val) →
    (∀ j : Fin (2^b+2^b), readings profile (t.p.bundlePayload+j.val) =
      value (fun h => (geometry (source t.cube.cells b up)).eval x (.inl (j,h)))) →
      t.OpenFields team frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries entry ∧ (∀ i : Fin 37, entry (ctrl+i.val)=t.controls i.val) ∧
        SectionSpec room.markers (cell ∘ host) header entry t.p.bundlePayload := by
  intro host old header up net geo ctl sorted
  have bound := room.controlEnd
  have start : origin ≤ ctrl := by dsimp only [controlsBase,bases]; omega
  have firstWord : frame+112 ≤ t.cube.header.header := by omega
  have fitBanks := signed_cellWriter_fit t axis positive firstWord bound (fitControls 11)
  have fitWord : t.before.four < 2^bits := fitControls 11
  have before : t.before.start ≤ t.before.four := by
    dsimp only [DiagonalTallyAllocation.BeforeTasks.four,DiagonalTallyAllocation.BeforeTasks.merged,
      DiagonalTallyAllocation.BeforeTasks.counters,DiagonalTallyAllocation.BeforeTasks.supplement,
      DiagonalTallyAllocation.BeforeTasks.tailWidths]; omega
  have headerFit := (t.open_table_order.1.trans (t.open_table_order.2.2.trans before)).trans_lt fitWord
  have liveEnd : (tables).livePairs ≤ ctrl := by dsimp only [controlsBase,bases]; omega
  have loc := frameWords.controlWord
  have layoutFit := geo.privateFit_of_census M cell aux siteID edgeID portID F net codes cellFit host live
    frame origin D.description gap (by omega) (by rw [loc]; omega) (by omega) (fitControls 10) capacity
  obtain ⟨separate,scheduled,keep,same⟩ := native.open_placement axis pp lp place layoutFit low reserve bound
  have positioned : 2^b ≤ 2^bits := by have := room.payloadEnd; omega
  have fitsCell c := (geo.private_census M cell aux siteID edgeID portID F net codes cellFit host live
    frame origin D.description gap c).trans_le (capacity c)
  let after := (banks).written scheduled t.cube.cells
  let publishedHeader := fun i => geometryHeader retain siteID F (x:=x) (l) after (banks).dest original i
    (shape i).copies (shape i).fine (shape i).incoming (shape i).cap
  have placedSort : SectionSpec room.markers (cell ∘ host) publishedHeader (readings profile) t.p.bundlePayload := by
    refine SectionSpec.of_cellBanks retain (banks) cell aux siteID edgeID portID F net codes cellFit frame origin
      D.description gap original live valid shape (readings profile) (readings placed) scheduled (readings profile)
      t.p.bundlePayload room.markers keysFit positioned
      (fun c => bankConfig_fits (banks) fitBanks gap (by change gap ≤ t.cube.cellStride; have h := capacity c; omega) c)
      descFit scanFit copies stride geo place layoutFit keep (.inl separate) ?_ sorted
    intro i
    exact bankHeader_fits (banks) (l) fitBanks (readings profile) (readings placed) scheduled layoutFit rfl place
      keep (.inl separate) fitsCell i _ _ _ _ _
  have originalSort : SectionSpec room.markers (cell ∘ host) header (readings profile) t.p.bundlePayload := by
    apply Eq.mp _ placedSort
    congr 1
    funext i
    exact same i _ _ _ _ _
  obtain ⟨f,actual,sort⟩ := open_directory_published pp lp (cell ∘ host) header room.markers place low reserve
    frameWords ctl originalSort (by omega)
  refine ⟨f.transfer t (fun i hi => native.low _ (by simp at hi; omega)),fun i => ?_,
    sort.transfer (fun a _ hi => native.low a (by have := room.rankEnd; omega))⟩
  · exact (native.low _ (by have := i.isLt; omega)).trans (actual i)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
