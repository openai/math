import OAI.Hierarchy.DescentTerminalScalarPadded
import OAI.Hierarchy.DescentTerminalScalarChip
import OAI.Hierarchy.DescentTerminalRestrictedRows

namespace OAI
/-! # Fixed proposal banks and their reached terminal scalar issues -/
namespace Hierarchy.DescentTerminalRestrictedScalar
open DescentKernelHistory DescentBundleHistory DescentEpochTagKeys DescentTerminalGraphPositions
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow DescentTerminalPorts DescentTerminalCableOrder
open DescentTerminalBinReaddress DescentTerminalRecipeRows DescentTerminalScalarTransposes
open ThreeFlat.Routing ThreeFlat.RAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators Fin.CommRing
noncomputable section
private theorem observed_front {K cap W q p piece w : ℕ} (same : p = W*piece)
    (fit : K ≤ cap) (room : q*p ≤ w) (idx : Fin (K*W) → ℕ) (fmt : Fin (K*W) → Format q p)
    (raw : ℕ → Computability.VPVNP.BurstRAM.Word (q*p)) (m : Memory w) (out : ℕ) (x : Proposal cap W q piece)
    (checked : ∀i, rowWord x i = low (same ▸ room) (fillSegment out (cap*W)
      (DescentTerminalDenseWindowRAM.file (n:=cap*W) out (DescentTerminalScalarPadded.pad idx 0)
        (DescentTerminalScalarPadded.pad fmt (DescentTerminalScalarPadded.blank q p)) raw) m (out+i.val))) :
    ∀i : Fin (K*W), rowWord (DescentTerminalScalarPadded.front fit x) i = low (same ▸ room)
      (fillSegment out (K*W) (DescentTerminalDenseWindowRAM.file out idx fmt raw) m (out+i.val)) := by
  subst p
  exact DescentTerminalScalarPadded.source_front fit room idx fmt raw m out x (funext checked)

variable {P U : Type} [Fintype P] {ew : P→ℕ}
    {D S p W q piece bitsW H nodesN addrN verts total rawRows initial arity groups stride : ℕ}
    (N : Network D P ew) (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ)
    (bit : SiteBits (U:=U) N) (s : ∀v,Shape p (bit v)) (hp : 0<p)
    (birth : ∀v,(bit v).Node ↪ ℕ) (old : Codec U initial) (wp : 0<W) (qp : 0<q)
local notation "L" => order N home native p external nodes ops
local notation "rsite" => fun v=>Recipe.restricted (Shape.recipe hp (s v))
local notation "sites" => DescentTerminalBundleRows.site L rsite hp birth
local notation "K" => Bins (W:=W) (q:=q) sites
local notation "T" => DescentBundleTagKeys.capacity initial arity groups p stride
local notation "book" => DescentBundleTagKeys.codec old arity groups p stride
local notation "recipes" => DescentTerminalBundleRows.recipes L rsite hp birth (Codec.store book)
variable (same : p=W*piece) (machine : sliceWidth W q piece ≤ bitsW)
    (space : DescentTerminalBinPack.purchased W
      (counts (q:=q) (order N home native p external nodes ops).site) ≤ total)
    (countsFit : ∀v,DescentTerminalRestrictedRows.operandCount bit s v ≤ H) (atoms : ∀v,Fintype.card (bit v).Node ≤ nodesN)
    (refs : ∀v u,(∑j,∑g,((s v).chunk u j g).count) ≤ addrN)
    (vertsFit : ∀i,((order N home native p external nodes ops).site i).nodes ≤ verts)
    (fit : ∀i,((order N home native p external nodes ops).site i).rows q ≤ W)
local notation "hH" => fun i v=>Nat.le_trans
  (DescentTerminalRestrictedRows.hidden_bound bit s hp (Order.node L i v)) (countsFit (Order.node L i v))
local notation "hN" => fun i v=>atoms (Order.node L i v)
set_option quotPrecheck false in
local notation "hA" => fun i v u=>(Eq.symm (Shape.recipe_refs hp (s (Order.node L i v)) u)) ▸ refs (Order.node L i v) u
local notation "hw" => fun i v u=>le_refl p

include fit in
/-- The incoming tape fields are the reached physical raw-pair input
pointers and formats, the two fixed-layout proposal comparisons, and the
bounded literal row descriptors with their presence flags. Every reached
word contains the exact requested number for that paid row. -/
theorem native_padded_read {K₀ : ℕ} (fitsBins : K ≤ K₀) (layout : DescentTerminalScalarDispatch.Layout) (dst rawOut : ℕ)
    (indices : Fin (K*W)→ℕ) (formats : Fin (K*W)→Format q p)
    (head : DescentTerminalScalarInput.Headers (rawRows:=rawRows) N home native external nodes ops rsite hp birth wp qp indices formats)
    (pay : RowBit rawRows (q*p)→Bool) (outer : Ports ew)
    (volume : (∑e,N.width e) ≤ rawRows*(q*p)) (clustered : DescentTerminalPublicGroup.Clustered N home external)
    (rawMem current : Memory bitsW) (X Y : Proposal K₀ W q piece) (wordRoom : q*p ≤ bitsW)
    (sourceChecked : ∀i, rowWord X i=low (same ▸ wordRoom)
      (fillSegment rawOut (K₀*W) (DescentTerminalDenseWindowRAM.file (n:=K₀*W) rawOut
        (DescentTerminalScalarPadded.pad indices 0) (DescentTerminalScalarPadded.pad formats (DescentTerminalScalarPadded.blank q p))
        (DescentTerminalScalarInput.raw external pay outer)) rawMem (rawOut+i.val)))
    (routeChecked : wide ∘ chunks Y=sliceOutput (bits:=bitsW) (DescentTerminalBinFormat.address W q)
      (DescentTerminalScalarPadded.gates (DescentTerminalRecipeRows.control sites wp qp)) X)
    (bounds : ∀b∈[layout.header,layout.payload,layout.pointer],b.Fits bitsW dst)
    (room : dst+total<2^bitsW) (tableFit : DescentTerminalScalarHeader.range q T H nodesN addrN p verts+1 ≤ 2^bitsW)
    (_keyFit : DescentTerminalRowBooks.Keys q T H nodesN addrN p verts (W*piece) ≤ 2^bitsW)
    (tape : DescentTerminalScalarDispatch.Reads sites wp qp space recipes hH hN hA hw vertsFit
      DescentTerminalScalarHeader.encode DescentTerminalScalarHeader.decode layout (DescentTerminalScalarPadded.front fitsBins Y) current) :
    let a:=takeBits N (denseBits N (edgeCode N home native) volume) pay
    let req:=DescentTerminalRestrictedRows.requests (A:=arity) (G:=groups) (R:=stride) L bit s hp birth old wp qp same
      machine space countsFit atoms refs vertsFit a outer
    let empty:=DescentTerminalRowBooks.emptyKey q T H nodesN addrN p verts (W*piece)
    ∀i : Fin total,(DescentTerminalScalarDispatch.fetch layout empty.val).eval current (i.val:Computability.VPVNP.BurstRAM.Word bitsW)=
      ((req i).val:Computability.VPVNP.BurstRAM.Word bitsW) := by
  intro a req empty
  have xc := observed_front same fitsBins wordRoom indices formats
    (DescentTerminalScalarInput.raw external pay outer) rawMem rawOut X sourceChecked
  have yc:=DescentTerminalScalarPadded.slice_front fitsBins
    (DescentTerminalRecipeRows.control sites wp qp) X Y routeChecked
  let actual : Proposal K W q piece :=DescentTerminalBundleRows.payload L rsite hp birth wp qp same a outer
  have readback:=DescentTerminalScalarInput.observed N home native external nodes ops rsite hp birth wp qp pay outer same
    volume clustered wordRoom indices formats head rawMem rawOut (DescentTerminalScalarPadded.front fitsBins X) xc
  have sameRoute:=output_congr sites wp qp machine fit (DescentTerminalScalarPadded.front fitsBins X) actual readback
  obtain ⟨after,exec,written,earlier,exactMem⟩:=DescentTerminalScalarDispatch.native_exec sites wp qp machine space recipes
    hH hN hA hw vertsFit DescentTerminalScalarHeader.encode DescentTerminalScalarHeader.decode
    DescentTerminalScalarHeader.back layout dst current actual (DescentTerminalScalarPadded.front fitsBins Y)
    (yc.trans sameRoute) bounds room tableFit tape
  intro i
  rw [←DescentTerminalDenseHeaderRAM.at_image dst _ current i,←exactMem]
  exact written i

end
end Hierarchy.DescentTerminalRestrictedScalar

end OAI
