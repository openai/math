import OAI.Computability.BorderVNP.DiagonalSignedPublishedIntervalRows
import OAI.Computability.BorderVNP.DiagonalSignedCandidateSite
import OAI.Computability.BorderVNP.DiagonalSignedCommonPlacement
import OAI.Computability.BorderVNP.DiagonalPublishedSlottedReadback

/-! # The physical interval pass of a returned signed candidate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP BurstRAM TeamContraction ProcessorSlots PackedHistoryCircuit Packing RoutingOutputs Crossing
open CellAddresses CellAddressCircuit CellAddressPhysical Packing.Directory BorderVNP.Cube
open Cube.Physical Cube.MeanChoice Cube.LabelIndex
open Cube.NativeIntervals Cube.HostScatter TeamContraction.JointHeader LocalRow CubeHeaderInstall
open scoped Classical

variable {D s n d k b w : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (a : CubeArena.Layout) (dir : Directory.Layout) (N : Network D P bits) (cell : N.Site → Fin a.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin a.cables) (portID : P ↪ Fin n)
    (F : Fields s a.cables n a.cells d k b σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (wordFit : b ≤ w) (positive : 0<a.cells)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ j,bits (live j)=dir.block) (bounds : dir.DestinationBounds)
    (pub : Arg → Word w) (base origin gap : ℕ)
    {pp lp : ℕ → ℕ × ℕ} {R X frame : ℕ} (word : Broadcast a.n a.header.d a.header.cap)
    {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration a.n a.header.d} {group : Fin a.header.d → Fin (R+1)}
    {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame} {guess : ℕ → Bool}
    {mac : TeamOpcode.Macros w 8} {reg : Bank w} {mem : Memory w} {I : Type} [Fintype I]
    {host : I → Fin a.cells} {key : I ↪ ℕ} {amount : I → ℕ} {A : Type} {dest : A → Fin a.cells} {size : A → ℕ}
    (site : SignedPrep.CandidateSite (X:=X) a dir pp lp word owner decl group frame base pins fields f guess pub mac reg mem
      host key amount N cell dest size)

local notation3 (prettyPrint := false) "before" => site.geometry
local notation3 (prettyPrint := false) "mid" => site.middle

local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "pr" => privateLayout head origin a.cables a.cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tables" => bases origin a.cables a.cells dir.entries
local notation3 (prettyPrint := false) "rawPlace" => ISA.placement (readings mid) (pr).raw
local notation3 (prettyPrint := false) "livePlace" => ISA.placement (readings mid) (tables).livePairs
local notation3 (prettyPrint := false) "rows" => dir.directory rawPlace livePlace
local notation3 (prettyPrint := false) "published" => readings (ISA.publish mid head base rows)
local notation3 (prettyPrint := false) "geometry" => LabelIndex.layout head published
local notation3 (prettyPrint := false) "list" => NativeDemands.rows N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "recv" => NativeDemands.receiver N cell edgeID portID dir original live gap bounds

local notation3 (prettyPrint := false) "il" => signedChooserLayout a head origin
local notation3 (prettyPrint := false) "sizes" => (fun i : Fin (list).length => list[i.val].width)

include net ids wireFit hk wordFit positive liveWidth in
/-- Read back the very interval pass in the selected header receipt. The
public reference rows and the native private-pair array may have different
unused entries, so only their populated directory lists are transported. -/
theorem candidate_interval_rows
    (common : dir.directory pp lp=NativeDemands.rows N cell edgeID portID dir original live gap)
    {J : Type} [Fintype J] {owner' : J → Fin a.cells} {key' : J ↪ ℕ} {width' : J → ℕ}
    (writer : SlottedWriter a dir rawPlace livePlace pins pub mid base owner' key' width')
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings before))
    (placed : (pr).Image (readings before) dir.entries (readings mid)) (fit : (pr).Fits w (readings before))
    (hdr : Header head origin a.cables a.cells dir.entries (readings before))
    (scratch : base+7*dir.candidates ≤ origin) (originFit : origin<2^w)
    (teams : dir.teams≤2^w) (procs : dir.processors≤2^w) (fieldsFit : dir.fields≤2^w) (lit : dir.literal<2^w)
    (cells : a.cells≤2^w) (stride : a.cellStride≤2^w) (below : origin+3*a.cables≤a.header.header) :
    let lab := meanPackedLabel N cell recv sizes (List.finRange a.cells) a.n a.header.d (Nat.zero_lt_of_lt site.input.alphabet)
    ∃ m : Memory w, (il).Image (readings m) (il).count (readings site.receipt.labeling.val.2.2) ∧
      (il).Fits w (readings m) ∧ (il).Fields (readings m) ∧ CableColumns a head il (readings m) ∧
      (∀ z<a.publicBase, readings site.receipt.labeling.val.2.2 z=readings site.published.val.2.2 z) ∧
      ∃ ord : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin a.cables,
        (∀ e, ord (NativeDemands.cableOrder N cell edgeID e)=edgeID e.val) ∧
        PhysicalRows N cell il (readings m) (NativeDemands.cableOrder N cell edgeID) ord Fin.valEmbedding lab
          (productCode a.n a.header.d a.alphabet rfl) := by
  intro lab
  have eqn := common.trans (NativeDemands.rows_eq_native N cell edgeID portID dir original live gap aux siteID F x
    head origin (readings before) (readings mid) net ids wireFit bounds liveWidth img placed fit)
  have pubEq := site.actual.trans (congrArg (ISA.publish mid head base) eqn)
  have room := site.input.commonPlacement eqn
  have scan := Eq.mp (congrArg (fun m : Memory w => Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare)
    site.published.val.2.1 m site.receipt.labeling.val.1 site.receipt.labeling.val.2.1 site.receipt.labeling.val.2.2)
    pubEq) site.receipt.labeling.property
  obtain ⟨m,im,fits,fields₀,space,lower,order,aligned,physical⟩ := signed_published_interval_rows a dir N cell aux siteID
    edgeID portID F x net ids wireFit hk wordFit positive original live liveWidth bounds pub base origin gap before mid
    writer img placed fit hdr scratch originFit teams procs fieldsFit lit cells stride room below scan
  exact ⟨m,im,fits,fields₀,space,fun z hz => (lower z hz).trans (congrArg (fun m => readings m z) pubEq).symm,
    order,aligned,physical⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
