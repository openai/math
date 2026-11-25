import OAI.Hierarchy.DescentTerminalChronologicalIssue
import OAI.Hierarchy.DescentTerminalRestrictedScalar

namespace OAI
/-! # Genuine surviving graph-row keys at the universal static chip address -/
namespace Hierarchy.DescentTerminalChronologicalChip
open private observed_front from OAI.Hierarchy.DescentTerminalRestrictedScalar
open DescentTerminalChipRuntime DescentTerminalChipPins DescentTerminalChipSource
open DescentKernelHistory DescentBundleHistory DescentEpochTagKeys DescentTerminalGraphPositions
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow DescentTerminalPorts DescentTerminalCableOrder
open DescentTerminalBinReaddress DescentTerminalRecipeRows DescentTerminalScalarTransposes
open ThreeFlat.Routing Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
variable {P U : Type} [Fintype P] {ew : P→ℕ}
    {D S p W q piece bitsW H nodesN addrN verts total rawRows initial arity groups stride : ℕ}
    (N : Network D P ew) (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ)
    (bit : SiteBits (U:=U) N) (s : ∀v,Shape p (bit v)) (hp : 0<p)
    (birth : ∀v,(bit v).Node ↪ ℕ) (privateRank : ∀v,((s v).recipe hp).restricted.Hidden ↪ ℕ) (old : Codec U initial) (wp : 0<W) (qp : 0<q)
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

def charts (i : Fin S) : DescentTerminalChronologicalBooks.Birth (recipes i) :=
  ⟨fun v=>privateRank (Order.node L i v),fun v=>birth (Order.node L i v)⟩
local notation "ranked" => charts (arity:=arity) (groups:=groups) (stride:=stride) N home native external nodes ops bit s hp birth privateRank old

def requests (a : N.Assignment) (x : Ports ew) :=
  DescentTerminalChronologicalBooks.requests sites wp qp machine
    (DescentTerminalBundleRows.payload L rsite hp birth wp qp same a x) space recipes ranked hH hN hA hw vertsFit

include fit in
theorem key_read {K₀ : ℕ} (fitsBins : K ≤ K₀) (banks : Banks) (dst : ℕ)
    (pay : RowBit rawRows (q*p)→Bool) (outer : Ports ew)
    (volume : (∑e,N.width e) ≤ rawRows*(q*p)) (clustered : DescentTerminalPublicGroup.Clustered N home external)
    (current : Memory bitsW) (z : Inputs K₀ W q piece→Bool) (wordRoom : q*p ≤ bitsW)
    (accept : (content N home native external nodes ops rsite hp birth wp qp same pay outer).accepts bitsW z)
    (emptyKey : banks.empty=(DescentTerminalChronologicalBooks.empty q T H nodesN addrN p verts (W*piece)).val)
    (_bounds : ∀b∈[banks.scalar.header,banks.scalar.payload,banks.scalar.pointer],b.Fits bitsW dst)
    (_room : dst+total<2^bitsW) (tableFit : DescentTerminalScalarHeader.range q T H nodesN addrN p verts+1 ≤ 2^bitsW)
    (_keyFit : DescentTerminalChronologicalBooks.Keys q T H nodesN addrN p verts (W*piece) ≤ 2^bitsW)
    (tape : DescentTerminalChronologicalIssue.Reads sites wp qp space recipes ranked hH hN hA hw vertsFit banks.scalar
      (DescentTerminalScalarPadded.front fitsBins (planes z true)) current) :
    let a:=takeBits N (denseBits N (edgeCode N home native) volume) pay
    let req:=requests (arity:=arity) (groups:=groups) (stride:=stride) N home native external nodes ops bit s hp birth privateRank old wp qp same
      machine space countsFit atoms refs vertsFit a outer
    ∀i : Fin total,(DescentTerminalChipRuntime.key banks).eval current (i.val:Computability.VPVNP.BurstRAM.Word bitsW)=((req i).val:Computability.VPVNP.BurstRAM.Word bitsW) := by
  intro a req
  obtain ⟨hx,hy⟩:=(accepts_iff N home native external nodes ops rsite hp birth wp qp same pay outer wordRoom current 0 z).mp accept
  let x:=DescentTerminalScalarPadded.front fitsBins (planes z false)
  let y:=DescentTerminalScalarPadded.front fitsBins (planes z true)
  let actual : Proposal K W q piece := DescentTerminalBundleRows.payload L rsite hp birth wp qp same a outer
  have hxf:=observed_front same fitsBins wordRoom
    (first (rawRows:=rawRows) N home native external nodes ops rsite hp birth wp qp)
    (format N home native external nodes ops rsite hp birth wp qp) _ current 0 (planes z false) hx
  have hyf:=DescentTerminalScalarPadded.slice_front fitsBins (DescentTerminalRecipeRows.control sites wp qp) _ _ hy
  have genuine:=DescentTerminalScalarInput.observed N home native external nodes ops rsite hp birth wp qp pay outer same
    volume clustered wordRoom _ _ (headers N home native external nodes ops rsite hp birth wp qp)
    current 0 x hxf
  have sameRoutes:=output_congr sites wp qp machine fit x actual genuine
  rw [DescentTerminalChipRuntime.key,emptyKey]
  exact DescentTerminalChronologicalIssue.read sites wp qp machine space recipes ranked hH hN hA hw vertsFit
    banks.scalar current actual y (hyf.trans sameRoutes) tableFit tape

include fit in
theorem graph_product {F : Type} [Field F] (small : ∀i v,(sites i).arity v ≤ q)
    (scalar : U→List (List Bool)→F) (T0 : N.Tables F) (valid : ReadsBits N scalar bit T0)
    (born : ∀v u,old.fits ((bit v).tag u)) (num : ∀v u,(bit v).arity u ≤ arity)
    (grp : ∀v u,(∑j,(s v).groups u j) ≤ groups) (steps : ∀v u j g,((s v).chunk u j g).stride ≤ stride)
    (a : N.Assignment) (x : Ports ew) (k : ℕ) (mulFits : (∑v,((s v).recipe hp).deadBits)<2^k) :
    let req:=requests (arity:=arity) (groups:=groups) (stride:=stride) N home native external nodes ops bit s hp birth privateRank old wp qp same
      machine space countsFit atoms refs vertsFit a x
    (∏v,N.read T0 a x v)=
      (∏j : Fin k,if (∑v,((s v).recipe hp).deadBits).testBit j.val then (2:F)^(2^j.val) else 1)*
      (∏i,DescentTerminalChronologicalBooks.menu (fun j args=>bundleScalar p scalar ((book).read j) args) (req i)) := by
  intro req
  rw [fixed_powers hp N scalar bit T0 valid s a x k mulFits]
  apply congrArg (_*·)
  symm
  rw [show (∏i,DescentTerminalChronologicalBooks.menu (fun j args=>bundleScalar p scalar ((book).read j) args) (req i))=_
    from DescentTerminalChronologicalBooks.requests_product sites wp qp machine
      (DescentTerminalBundleRows.payload L rsite hp birth wp qp same a x) space recipes ranked hH hN hA hw vertsFit
      fit small (fun j args=>bundleScalar p scalar ((book).read j) args)]
  apply DescentTerminalBundleRows.site_product L rsite hp birth wp qp same (book).store _
    (bundleScalar p scalar) _ _ _ a x
  · intro v u args
    exact DescentBundleTagKeys.value old arity groups p stride scalar _
      (DescentTerminalBundleMenu.tag_fits hp (s v) old u (born v u) (num v u) (grp v u) (steps v u)) args
  · intros; rfl

end
end Hierarchy.DescentTerminalChronologicalChip

end OAI
