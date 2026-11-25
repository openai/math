import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenPlacement
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenCensus

/-! # Original signed bundle headers and controls at the native data-writer entry

The signed geometry output gives both marked sort banks. The physical placement
of the private originals and the native receiving-bank writer give the actual
six fields of each header at data-writer entry. The emitter's controls, sort
and required frame fields all survive into that same memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM VerifierNetwork GeometryFrameEncoding ParseBatchSort Packing PackedHistoryCircuit
open BottomReports BundleSort RoutingOutputs Crossing CellAddresses CellAddressCircuit
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport

variable {S Z : Type*} [Fintype S] [Fintype Z] {W r s n d k bits b q o frame origin next gap team R : ℕ}
variable {P : Type} [Fintype P] {len : P → ℕ} {N M : Network r P len}
variable (t : SignedTaskArena.Layout) (D : Directory.Layout) (axis : Fin (t.cube.n+1))
variable (pp lp : ℕ → ℕ × ℕ) (retain : Retains N M) (cell : M.Site → Fin t.cube.cells)
variable (aux : M.Site → ℕ) (siteID : M.Site ↪ Fin s) (edgeID : M.Edge ↪ Fin t.cube.cables) (portID : P ↪ Fin n)
variable (original : Fin D.entries → N.Site) (live : Fin (D.teams*D.sites) → P)
variable (F : Fields s t.cube.cables n t.cube.cells d k bits (S ⊕ Bool)) (hk : k ≤ bits)
variable (shape : Fin D.entries → Shape) (valid : Frame (S ⊕ Bool) Unit)
variable (first : Frame (S ⊕ Bool) (Fin q × Fin bits)) (rest : Frame (S ⊕ Bool) (Outputs o bits))
variable (sewn : Frame Z S) (input : Z → Bool) (profile placed : Memory W) (entry : ℕ → ℕ)

local notation "ctrl" => controlsBase origin t.cube.cables t.cube.cells D.entries (D.teams*D.sites)
local notation "tables" => bases origin t.cube.cables t.cube.cells D.entries
local notation "l" => privateLayout frame origin t.cube.cables t.cube.cells D.entries D.description gap
local notation "banks" => t.cube.cellWriter frame ctrl axis
local notation "pubMem" => readings (Directory.ISA.publish placed frame next (D.directory pp lp))

/-- All three pre-writer sources on the genuine checked-group return, with
the absolute bundle fields read from the returned physical RAM. The global
signed frame can be supplied by the chosen-profile boot and the output bounds
by the signed arena's length ceiling. -/
theorem NativeEntry.open_sources_of_profile {inputMem : ℕ → ℕ}
    (native : NativeEntry t.cube frame ctrl axis R inputMem pubMem entry)
    (room : t.OpenRoom frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries (2^b) W)
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin)
    (payload : t.p.bundlePayload=ctrl+37+q) (rank : t.p.bundleInverse=t.p.bundlePayload+2^b)
    (fitControls : ∀ i : Fin 37, t.controls i.val < 2^bits)
    (frameWords : t.OpenFields team frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries (readings profile))
    (place : (l).Image (readings profile) D.entries (readings placed))
    (positive : 0<t.cube.header.d) (word : bits ≤ W) (keysFit : t.cube.cells < 2^k)
    (descFit : D.description < 2^bits) (scanFit : 2^Nat.clog 2 D.entries*D.description < 2^bits)
    (copies : ∀ i, (shape i).copies < 2^bits)
    (stride : ∀ i, bottomStride ((shape i).fine+(shape i).incoming) (shape i).cap < 2^bits)
    (codes : ∀ c, (F.cells c).val=c.val)
    (cellFit : ∀ c, guessedSize M cell c+siteSize M cell c aux+suppliedSize M cell c < 2^bits)
    (capacity : ∀ c, suppliedSize M cell c+gap+Directory.DataSlabs.size (cell ∘ retain.site ∘ original)
      (fun _ => D.description) c ≤ t.cube.cellStride) :
    let x := (withSewnFields sewn).eval input
    let host := fun i => retain.site (original i)
    let old := siteID ∘ host
    let header := fun i => geometryHeader retain siteID F (x:=x) (l) entry t.cube.hostDirectory original i
      (shape i).copies (shape i).fine (shape i).incoming (shape i).cap
    let vector := allTaskControls t bits fitControls
    let head := fun i : Fin 28 => vector (i.castAdd 9)
    let tail := fun i : Fin 9 => vector (Fin.natAdd 28 i)
    let headers := withHeaderBanks (banks) F b old D.description gap shape valid rest
    let suffix := GeometryOutput.prepend first headers
    let emit := controlEmitter F hk old (portID ∘ live) (withControls tail suffix) sewn head
    CellAddressPhysical.Represents M cell aux siteID edgeID portID F x →
    (∀ i, readings profile (origin+i.val)=value (fun j => emit.eval input (i,j))) →
      t.OpenFields team frame (tables).ends ctrl (tables).livePairs (D.teams*D.sites) D.entries entry ∧ (∀ i : Fin 37, entry (ctrl+i.val)=t.controls i.val) ∧
        SectionSpec room.markers (cell ∘ host) header entry t.p.bundlePayload := by
  intro x host old header vector head tail headers suffix emit net words
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
  have geo := (profile_headerBanks (banks) F hk old (portID ∘ live) D.description gap shape valid first rest sewn
    head tail input origin profile word words).1
  have loc := frameWords.controlWord
  have layoutFit := geo.privateFit_of_census M cell aux siteID edgeID portID F net codes cellFit host live
    frame origin D.description gap (by omega) (by rw [loc]; omega) (by omega) (fitControls 10) capacity
  obtain ⟨separate,scheduled,keep,same⟩ := native.open_placement axis pp lp place layoutFit low reserve bound
  have positioned : 2^b ≤ 2^bits := by have := room.payloadEnd; omega
  have fitsCell c := (geo.private_census M cell aux siteID edgeID portID F net codes cellFit host live
    frame origin D.description gap c).trans_le (capacity c)
  have h := profile_header_sections (banks) F hk D.description gap shape valid first rest sewn head tail input
    origin profile word retain cell aux siteID edgeID portID original live frame (readings placed) scheduled
    room.markers keysFit positioned fitBanks descFit scanFit copies stride codes cellFit net place layoutFit
    keep (.inl separate) fitsCell words
  have originalSort : SectionSpec room.markers (cell ∘ host) header (readings profile) t.p.bundlePayload := by
    rw [payload]
    apply Eq.mp _ h
    congr 1
    funext i
    exact same i _ _ _ _ _
  have ctl := profile_open_controlWords t fitControls F hk old (portID ∘ live) suffix sewn input word profile words
  obtain ⟨f,actual,sort⟩ := open_directory_published pp lp (cell ∘ host) header room.markers place low reserve
    frameWords ctl originalSort (by omega)
  refine ⟨f.transfer t (fun i hi => native.low _ (by simp at hi; omega)),fun i => ?_,
    sort.transfer (fun a _ hi => native.low a (by have := room.rankEnd; omega))⟩
  · exact (native.low _ (by have := i.isLt; omega)).trans (actual i)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
