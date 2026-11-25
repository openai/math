import OAI.Hierarchy.DescentTerminalScalarDispatch
import OAI.Hierarchy.DescentTerminalScalarInput
import OAI.Hierarchy.DescentTerminalScalarHeader
import OAI.Hierarchy.DescentTerminalBundleMenu

namespace OAI
/-! # Physical scalar keys for the actual terminal graph and affine histories -/
namespace Hierarchy.DescentTerminalScalarChip
open DescentKernelHistory DescentBundleHistory DescentEpochTagKeys DescentTerminalGraphPositions
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow DescentTerminalPorts DescentTerminalCableOrder
open DescentTerminalBinReaddress DescentTerminalRecipeRows DescentTerminalScalarTransposes
open ThreeFlat.Routing ThreeFlat.RAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open Computability.BorderVNP.Crossing
open scoped Fin.CommRing Classical BigOperators
noncomputable section
variable {P U : Type} [Fintype P] {ew : P→ℕ}
    {D S p W q piece bitsW H nodesN addrN verts total rawRows initial arity groups stride : ℕ}
    (N : Network D P ew) (home : N.Site→Fin S) (nativeOrder : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ)
    (bit : SiteBits (U:=U) N) (s : ∀v,Shape p (bit v)) (hp : 0<p)
    (birth : ∀v,(bit v).Node ↪ ℕ) (old : Codec U initial) (wp : 0<W) (qp : 0<q)
local notation "L" => order N home nativeOrder p external nodes ops
local notation "rsite" => fun v=>DescentBundleHistory.Shape.recipe hp (s v)
local notation "sites" => DescentTerminalBundleRows.site L rsite hp birth
local notation "K" => Bins (W:=W) (q:=q) sites
local notation "T" => DescentBundleTagKeys.capacity initial arity groups p stride
local notation "book" => DescentBundleTagKeys.codec old arity groups p stride
set_option quotPrecheck false
local notation "recipes" => DescentTerminalBundleRows.recipes L rsite hp birth (book).store
variable (same : p=W*piece) (machine : sliceWidth W q piece ≤ bitsW)
    (space : DescentTerminalBinPack.purchased W (counts (q:=q)
      (DescentTerminalBundleRows.site (order N home nativeOrder p external nodes ops) (fun v=>(s v).recipe hp) hp birth)) ≤ total)
    (hidden : ∀v,Fintype.card (Private (bit v) p) ≤ H) (atoms : ∀v,Fintype.card (bit v).Node ≤ nodesN)
    (refs : ∀v u,(∑j,∑g,((s v).chunk u j g).count) ≤ addrN)
    (vertsFit : ∀i,(DescentTerminalBundleRows.site (order N home nativeOrder p external nodes ops)
      (fun v=>(s v).recipe hp) hp birth i).nodes ≤ verts)
    (fit : ∀i,(DescentTerminalBundleRows.site (order N home nativeOrder p external nodes ops)
      (fun v=>(s v).recipe hp) hp birth i).rows q ≤ W)
local notation "hH" => fun i v=>hidden ((L).node i v)
local notation "hN" => fun i v=>atoms ((L).node i v)
local notation "hA" => fun i v u=>((s ((L).node i v)).recipe_refs hp u).symm ▸ refs ((L).node i v) u
local notation "hw" => fun i v u=>le_refl p

include fit in
/-- The incoming tape fields are the reached physical raw-pair input
pointers and formats, the two fixed-layout proposal comparisons, and the
bounded literal row descriptors with their presence flags. Every reached
word contains the exact requested number for that paid row. -/
theorem native (layout : DescentTerminalScalarDispatch.Layout) (dst rawOut : ℕ)
    (indices : Fin (K*W)→ℕ) (formats : Fin (K*W)→Format q p)
    (head : DescentTerminalScalarInput.Headers (rawRows:=rawRows) N home nativeOrder external nodes ops rsite hp birth wp qp indices formats)
    (pay : RowBit rawRows (q*p)→Bool) (outer : Ports ew)
    (volume : (∑e,N.width e) ≤ rawRows*(q*p)) (clustered : DescentTerminalPublicGroup.Clustered N home external)
    (rawMem current : Memory bitsW) (X Y : Proposal K W q piece) (wordRoom : q*p ≤ bitsW)
    (sourceChecked : ∀i, rowWord X i=low (same ▸ wordRoom)
      (fillSegment rawOut (K*W) (DescentTerminalDenseWindowRAM.file rawOut indices formats
        (DescentTerminalScalarInput.raw external pay outer)) rawMem (rawOut+i.val)))
    (routeChecked : wide ∘ chunks Y=sliceOutput (bits:=bitsW) (DescentTerminalBinFormat.address W q)
      (DescentTerminalRecipeRows.control sites wp qp) X)
    (bounds : ∀b∈[layout.header,layout.payload,layout.pointer],b.Fits bitsW dst)
    (room : dst+total<2^bitsW) (tableFit : DescentTerminalScalarHeader.range q T H nodesN addrN p verts+1 ≤ 2^bitsW)
    (keyFit : DescentTerminalRowBooks.Keys q T H nodesN addrN p verts (W*piece) ≤ 2^bitsW)
    (tape : DescentTerminalScalarDispatch.Reads sites wp qp space recipes hH hN hA hw vertsFit
      DescentTerminalScalarHeader.encode DescentTerminalScalarHeader.decode layout Y current) :
    let a:=takeBits N (denseBits N (edgeCode N home nativeOrder) volume) pay
    let req:=DescentTerminalBundleMenu.requests (A:=arity) (G:=groups) (R:=stride) L bit s hp birth old wp qp same
      machine space hidden atoms refs vertsFit a outer
    let empty:=DescentTerminalRowBooks.emptyKey q T H nodesN addrN p verts (W*piece)
    ∃after,(DescentTerminalScalarDispatch.program layout bitsW dst total empty.val).Exec current after (4+64*total) ∧
      (∀i : Fin total,(after (dst+i.val)).val=(req i).val) ∧ (∀j<dst,after j=current j) ∧
      after=ProtocolRAM.image dst total (DescentTerminalScalarDispatch.fetch layout empty.val) current := by
  intro a req empty
  let actual : Proposal K W q piece := DescentTerminalBundleRows.payload L rsite hp birth wp qp same a outer
  have readback := DescentTerminalScalarInput.observed N home nativeOrder external nodes ops rsite hp birth wp qp
    pay outer same volume clustered wordRoom indices formats head rawMem rawOut X sourceChecked
  have sameRoute := DescentTerminalScalarTransposes.output_congr sites wp qp machine fit X actual readback
  obtain ⟨after, exec, written, earlier, exactMem⟩ := DescentTerminalScalarDispatch.native_exec
    sites wp qp machine space recipes hH hN hA hw vertsFit
    DescentTerminalScalarHeader.encode DescentTerminalScalarHeader.decode DescentTerminalScalarHeader.back
    layout dst current actual Y (routeChecked.trans sameRoute) bounds room tableFit tape
  refine ⟨after, exec, ?_, earlier, exactMem⟩
  intro i
  have word : after (dst+i.val)=((req i).val : Computability.VPVNP.BurstRAM.Word bitsW) := written i
  exact (congrArg Fin.val word).trans (Fin.val_cast_of_lt ((req i).isLt.trans_le keyFit))

end
end Hierarchy.DescentTerminalScalarChip

end OAI
