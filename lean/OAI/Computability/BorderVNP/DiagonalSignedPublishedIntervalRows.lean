import OAI.Computability.BorderVNP.DiagonalSignedChooserLayout
import OAI.Computability.BorderVNP.CubeHostScatterChooserReceipt
import OAI.Computability.BorderVNP.PackedNativeDemandIntervals

/-! # Intervals on the actual signed cable addresses after the native chooser -/

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
    (pub : Arg → Word w) (base origin gap : ℕ) (before mid : Memory w)

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
set_option maxHeartbeats 1200000 in
/-- An actual signed chooser and interval return yields the signed history's
fixed cable order, its true mean label and the common interval geometry.
The original post-chooser RAM is retained for subsequent owned reads. -/
theorem signed_published_interval_rows {I : Type} [Fintype I] {sc : I → Fin a.cells} {sid : I ↪ ℕ} {sw : I → ℕ} {pins}
    (write : SlottedWriter a dir rawPlace livePlace pins pub mid base sc sid sw)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings before))
    (placed : (pr).Image (readings before) dir.entries (readings mid)) (fit : (pr).Fits w (readings before))
    (hdr : Header head origin a.cables a.cells dir.entries (readings before))
    (scratch : base+7*dir.candidates ≤ origin) (originFits : origin<2^w)
    (teams : dir.teams≤2^w) (procs : dir.processors≤2^w) (fields : dir.fields≤2^w) (literal : dir.literal<2^w)
    (cells : a.cells≤2^w) (stride : a.cellStride≤2^w)
    {f : BroadcastFrame} {old : Fin 81 → Word w} {fresh gates outputs width off ell controls R X : ℕ}
    {G : List Bool} {claims : List (List Bool)} {pad : ℕ} {raw : Broadcast a.n a.header.d a.header.cap}
    (room : PinnedRawInput (ar := a) (D := dir) (pp := rawPlace) (lp := livePlace) (pub := pub) (slotted := mid) (base := base)
      f old fresh gates outputs width off ell controls G claims pad raw R X)
    (below : origin+3*a.cables≤a.header.header)
    {mac : TeamOpcode.Macros w 8} {r z : Bank w} {tr : List (TeamRAM.Event w)} {endMem : Memory w}
    (run : Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) r (ISA.publish mid head base rows) tr z endMem) :
    let alphabet : 0<a.header.d := by have := room.alphabet; omega
    let labels := meanPackedLabel N cell recv sizes (List.finRange a.cells) a.n a.header.d alphabet
    ∃ memory : Memory w, (il).Image (readings memory) (il).count (readings endMem) ∧
      (il).Fits w (readings memory) ∧ (il).Fields (readings memory) ∧ CableColumns a head il (readings memory) ∧
      (∀ x<a.publicBase, readings endMem x=published x) ∧
      ∃ row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin a.cables,
        (∀ e, row (NativeDemands.cableOrder N cell edgeID e)=edgeID e.val) ∧
        PhysicalRows N cell il (readings memory) (NativeDemands.cableOrder N cell edgeID) row
          Fin.valEmbedding labels (productCode a.n a.header.d a.alphabet rfl) := by
  intro alphabet labels
  obtain ⟨cables,slots,deliveries,number,count,ep,edges,data,aligned,model⟩ :=
    signed_published_cable_rows a dir N cell aux siteID edgeID portID F x net ids wireFit hk wordFit positive
      original live liveWidth bounds pub base origin gap before mid write img placed fit hdr scratch originFits
      teams procs fields literal cells stride
  let loc := chooserLayout geometry head (published (head+48)) (published (head+57)) (published (head+58))
  have fixed : loc=il := room.signed_chooser_layout origin cables slots
  have labs : loc.labels=a.publicBase := congrArg NativeIntervals.Layout.labels fixed
  have offsets : loc.ordinals=a.ordinalBase := congrArg NativeIntervals.Layout.ordinals fixed
  have letters : a.header.d^(a.n+1)=(geometry).labels := (congrArg NativeIntervals.Layout.alphabet fixed).symm
  have rowsEq := NativeDemands.rows_eq_native N cell edgeID portID dir original live gap aux siteID F x
    head origin (readings before) (readings mid) net ids wireFit bounds liveWidth img placed fit
  have dataEnd : (geometry).deliveries+(geometry).deliveryCount*7≤loc.labels := by
    rw [deliveries,number,rowsEq,labs]
    have lower := a.writer_order.1
    exact write.rawEnd.trans (by omega)
  obtain ⟨memory,image,fits,headers,space,low,ord,row,rowEdges,physical⟩ :=
    HostScatter.chooser_columns (ar := a) N cell recv sizes room.labels run (finCongr count.symm) edges data.toEmbedding
      alphabet letters model dataEnd (by rw [cables]; exact write.rawStart.trans (by omega))
      (by rwa [cables,slots]) count slots.le labs offsets
  have ascending {m n : ℕ} (h : m=n) : (List.finRange n).map (finCongr h).symm=List.finRange m := by
    subst n
    simp
  have codes {m n : ℕ} (h : m=n) : (finCongr h).toEmbedding.trans Fin.valEmbedding=Fin.valEmbedding := by
    subst n
    rfl
  rw [ascending count.symm,codes count.symm] at physical
  let columns (l : NativeIntervals.Layout) := ∃ mem : Memory w, l.Image (readings mem) l.count (readings endMem) ∧
    l.Fits w (readings mem) ∧ l.Fields (readings mem) ∧ CableColumns a head l (readings mem) ∧
    (∀ x<a.publicBase, readings endMem x=published x) ∧
    ∃ (order : N.CrossingEdge cell ≃ Fin (Fintype.card (N.CrossingEdge cell)))
      (table : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin l.count),
      (∀ e,(table (order e)).val=(edgeID e.val).val) ∧ ∀ h : a.header.d^(a.n+1)=l.alphabet,
        PhysicalRows N cell l (readings mem) order table Fin.valEmbedding labels (productCode a.n a.header.d l.alphabet h)
  have actual : columns loc := ⟨memory,image,fits,headers,space,low,ord,row,
    fun e => (congrArg Fin.val (rowEdges e)).trans (aligned e), fun _ => physical⟩
  obtain ⟨mem,img,fit,hdr,room',low',order,table,slots,rows'⟩ := (congrArg columns fixed).mp actual
  have exactRows : ∀ e, table (order e)=edgeID e.val := fun e => Fin.ext (slots e)
  obtain rfl := (NativeDemands.cableOrder_eq_of_aligned N cell edgeID order table exactRows).symm
  exact ⟨mem,img,fit,hdr,room',low',table,exactRows,rows' rfl⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
