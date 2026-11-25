import OAI.Hierarchy.DescentTerminalChipSource

namespace OAI
/-! # Genuine surviving graph-row keys at the universal static chip address -/
namespace Hierarchy.DescentTerminalChipSource
open DescentTerminalChipRuntime DescentTerminalChipPins
open DescentKernelHistory DescentBundleHistory DescentEpochTagKeys DescentTerminalGraphPositions
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow DescentTerminalPorts DescentTerminalCableOrder
open DescentTerminalBinReaddress DescentTerminalRecipeRows DescentTerminalScalarTransposes
open ThreeFlat.Routing ThreeFlat.RAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
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
theorem restricted_key {K₀ : ℕ} (fitsBins : K ≤ K₀) (banks : Banks) (dst : ℕ)
    (pay : RowBit rawRows (q*p)→Bool) (outer : Ports ew)
    (volume : (∑e,N.width e) ≤ rawRows*(q*p)) (clustered : DescentTerminalPublicGroup.Clustered N home external)
    (current : Memory bitsW) (z : Inputs K₀ W q piece→Bool) (wordRoom : q*p ≤ bitsW)
    (accept : (content N home native external nodes ops rsite hp birth wp qp same pay outer).accepts bitsW z)
    (emptyKey : banks.empty=(DescentTerminalRowBooks.emptyKey q T H nodesN addrN p verts (W*piece)).val)
    (bounds : ∀b∈[banks.scalar.header,banks.scalar.payload,banks.scalar.pointer],b.Fits bitsW dst)
    (room : dst+total<2^bitsW) (tableFit : DescentTerminalScalarHeader.range q T H nodesN addrN p verts+1 ≤ 2^bitsW)
    (keyFit : DescentTerminalRowBooks.Keys q T H nodesN addrN p verts (W*piece) ≤ 2^bitsW)
    (tape : DescentTerminalScalarDispatch.Reads sites wp qp space recipes hH hN hA hw vertsFit
      DescentTerminalScalarHeader.encode DescentTerminalScalarHeader.decode banks.scalar
      (DescentTerminalScalarPadded.front fitsBins (planes z true)) current) :
    let a:=takeBits N (denseBits N (edgeCode N home native) volume) pay
    let req:=DescentTerminalRestrictedRows.requests (A:=arity) (G:=groups) (R:=stride) L bit s hp birth old wp qp same
      machine space countsFit atoms refs vertsFit a outer
    ∀i : Fin total,(DescentTerminalChipRuntime.key banks).eval current (i.val:Computability.VPVNP.BurstRAM.Word bitsW)=((req i).val:Computability.VPVNP.BurstRAM.Word bitsW) := by
  intro a req
  obtain ⟨hx,hy⟩:=(accepts_iff N home native external nodes ops rsite hp birth wp qp same pay outer wordRoom current 0 z).mp accept
  rw [DescentTerminalChipRuntime.key,emptyKey]
  exact DescentTerminalRestrictedScalar.native_padded_read N home native external nodes ops bit s hp birth old wp qp same
    machine space countsFit atoms refs vertsFit fit fitsBins banks.scalar dst 0
    (first (rawRows:=rawRows) N home native external nodes ops rsite hp birth wp qp)
    (format N home native external nodes ops rsite hp birth wp qp)
    (headers N home native external nodes ops rsite hp birth wp qp)
    pay outer volume clustered current current (planes z false) (planes z true) wordRoom hx hy
    bounds room tableFit keyFit tape

end
end Hierarchy.DescentTerminalChipSource

end OAI
