import OAI.Hierarchy.DescentTerminalOperandTilesRAM
import OAI.Hierarchy.DescentBundleTerminal
import OAI.Hierarchy.DescentBundleTagKeys
import OAI.Hierarchy.DescentTerminalSparseHeader
import OAI.Hierarchy.DescentTerminalControlBits

namespace OAI
/-! # Paid terminal scalar requests directly from the genuine retained bundle chart -/

namespace Hierarchy.DescentTerminalBundleMenu
open Computability.BorderVNP.Crossing DescentKernelHistory DescentBundleHistory DescentEpochTagKeys
open DescentTerminalGraphPositions DescentTerminalRecipeRows DescentTerminalBinReaddress
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

variable {U B : Type} {ww : B→ℕ} {p A G R baseTags : ℕ} {r : BitRecipe U B ww}

/-- Every purchased argument is one actual aligned referenced block.
The estimate counts the read words, including duplicates, and folds in
the incoming bit volume without a multiplier depending on cable length. -/
theorem operand_bits (hp : 0<p) (s : Shape p r) (stride : ∀u j g,(s.chunk u j g).stride ≤ R) :
    DescentTerminalOperandScan.Rows (s.recipe hp)*p ≤ (R+1)*(∑u,r.nodeBits u) := by
  have rows : DescentTerminalOperandScan.Rows (s.recipe hp) =
      ∑u : r.Node, ∑j, ∑g, (s.chunk u j g).count := by
    apply Finset.sum_congr (congrArg (@Finset.univ r.Node) (Subsingleton.elim _ _))
    intro u _
    exact s.recipe_refs hp u
  rw [rows]
  exact s.addresses_bound R stride

theorem tile_fee (hp : 0<p) (s : Shape p r) (stride : ∀u j g,(s.chunk u j g).stride ≤ R) (q : ℕ) :
    DescentTerminalOperandTiles.tileCount (s.recipe hp) q*(q*p) ≤ (R+1)*(∑u,r.nodeBits u)+q*p := by
  have divide:=Nat.div_mul_le_self (DescentTerminalOperandScan.Rows (s.recipe hp)+q-1) q
  have cover : DescentTerminalOperandTiles.tileCount (s.recipe hp) q*q ≤ DescentTerminalOperandScan.Rows (s.recipe hp)+q :=
    divide.trans (Nat.sub_le ..)
  calc
    _ = (DescentTerminalOperandTiles.tileCount (s.recipe hp) q*q)*p := (Nat.mul_assoc ..).symm
    _ ≤ _ := (Nat.mul_le_mul_right p cover).trans (by rw [Nat.add_mul]; exact Nat.add_le_add_right (operand_bits hp s stride) _)

theorem use_bits (hp : 0<p) (s : Shape p r) (stride : ∀u j g,(s.chunk u j g).stride ≤ R) :
    DescentTerminalBundleRows.useCount (s.recipe hp)*p ≤ (R+1)*(∑u,r.nodeBits u) :=
  (Nat.mul_le_mul_right p (DescentTerminalBundleRows.use_le (s.recipe hp))).trans (operand_bits hp s stride)

theorem tag_fits (hp : 0<p) (s : Shape p r) (old : Codec U baseTags) (u : r.Node)
    (born : old.fits (r.tag u)) (arity : r.arity u ≤ A) (groups : (∑j,s.groups u j) ≤ G)
    (stride : ∀j g,(s.chunk u j g).stride ≤ R) :
    DescentBundleTagKeys.Fits old A G p R ((s.recipe hp).tag u) := by
  refine ⟨born,?_,?_,?_⟩
  · simpa [Shape.recipe,Shape.rows] using arity
  · simpa [Shape.recipe,Shape.rows,List.length_flatten,List.map_ofFn,List.sum_ofFn] using groups
  · intro code hc
    simp only [Shape.recipe,Shape.rows,List.map_ofFn,List.mem_flatten,List.mem_ofFn] at hc
    obtain ⟨_,⟨j,rfl⟩,inRow⟩:=hc
    change code ∈ (List.ofFn (fun g=>s.chunk u j g)).map Slice.code at inRow
    obtain ⟨chunk,member,rfl⟩:=List.mem_map.mp inRow
    obtain ⟨g,rfl⟩:=List.mem_ofFn.mp member
    exact ⟨(s.chunk u j g).residue.le,stride j g,(s.chunk u j g).bound.trans (Nat.succ_le_succ (stride j g))⟩

variable {F P : Type} [Field F] [Fintype P] {D S H atoms addresses vertices total W q piece bitsW : ℕ}
    {bits : P→ℕ} {N : Network D P bits} (order : Order N S p) (bit : SiteBits (U:=U) N)
    (s : ∀v,Shape p (bit v)) (hp : 0<p) (birth : ∀v,(bit v).Node ↪ ℕ) (old : Codec U baseTags)
local notation "book" => DescentBundleTagKeys.codec old A G p R
local notation "rsite" => fun v=>DescentBundleHistory.Shape.recipe hp (s v)
local notation "sites" => DescentTerminalBundleRows.site order rsite hp birth

def keys (q baseTags A G p R H atoms addresses vertices : ℕ) :=
  DescentTerminalRowBooks.Keys q (DescentBundleTagKeys.capacity baseTags A G p R) H atoms addresses p vertices p

/-- One finite scalar alphabet for every paid row; its budget uses the old
birth tag and affine slice integers, independent of absolute graph ids. -/
theorem alphabet (tagBits machineBits : ℕ) (initial : baseTags ≤ 2^tagBits)
    (small : DescentTerminalControlBits.rowBits q (DescentBundleTagKeys.width tagBits A G p R)
      H atoms addresses p vertices+q*p ≤ machineBits/2) :
    keys q baseTags A G p R H atoms addresses vertices ≤ 2^(machineBits/2) := by
  have code := DescentBundleTagKeys.code_width baseTags tagBits A G p R initial
  have tag := (Nat.le_pow_clog (by decide : 1<2) (DescentBundleTagKeys.capacity baseTags A G p R)).trans
    (Nat.pow_le_pow_right (by decide) code)
  change 2^(DescentTerminalRowBooks.controlBits _ _ _ _ _ _ _)*2^(q*p) ≤ _
  rw [←pow_add]
  exact Nat.pow_le_pow_right (by decide)
    ((Nat.add_le_add_right (DescentTerminalControlBits.row_key tag) _).trans small)

def menu (scalar : U→List (List Bool)→F) :=
  DescentTerminalRowBooks.menu q H atoms addresses p vertices p
    (fun i xs=>bundleScalar p scalar ((book).read i) xs)

variable (wp : 0<W) (qp : 0<q) (widthEq : p=W*piece) (machine : sliceWidth W q piece ≤ bitsW)
    (space : DescentTerminalBinPack.purchased W (counts (q:=q)
      (DescentTerminalBundleRows.site order (fun v=>(s v).recipe hp) hp birth)) ≤ total)
    (hidden : ∀v,Fintype.card (Private (bit v) p) ≤ H)
    (atomCount : ∀v,Fintype.card (bit v).Node ≤ atoms)
    (operands : ∀v u,(∑j,∑g,((s v).chunk u j g).count) ≤ addresses)
    (positions : ∀i,(DescentTerminalBundleRows.site order (fun v=>(s v).recipe hp) hp birth i).nodes ≤ vertices)

def requests (a : N.Assignment) (x : Ports bits) :=
  DescentTerminalRowBooks.request sites wp qp machine
    (DescentTerminalBundleRows.payload order rsite hp birth wp qp widthEq a x)
    space (DescentTerminalBundleRows.recipes order rsite hp birth (book).store)
    (fun i v=>hidden (order.node i v)) (fun i v=>atomCount (order.node i v))
    (fun i v u=>((s (order.node i v)).recipe_refs hp u).symm ▸ operands (order.node i v) u)
    (fun _ _ _=>le_refl p) positions

/-- The end-graph truth value, the row payload, and its common scalar
alphabet are all calculated by the actual bounded recipes. -/
theorem requests_product (fit : ∀i,(sites i).rows q ≤ W) (small : ∀i v,(sites i).arity v ≤ q)
    (scalar : U→List (List Bool)→F) (T : N.Tables F) (valid : ReadsBits N scalar bit T)
    (born : ∀v u,old.fits ((bit v).tag u)) (arity : ∀v u,(bit v).arity u ≤ A)
    (groups : ∀v u,(∑j,(s v).groups u j) ≤ G) (stride : ∀v u j g,((s v).chunk u j g).stride ≤ R)
    (a : N.Assignment) (x : Ports bits) :
    let req:=requests (A:=A) (G:=G) (R:=R) order bit s hp birth old wp qp widthEq machine space hidden atomCount operands positions a x
    (∏key,DescentTerminalRowBooks.menu q H atoms addresses p vertices (W*piece)
      (fun i xs=>bundleScalar p scalar ((book).read i) xs) (req key))=∏v,N.read T a x v := by
  intro req
  apply DescentTerminalBundleRows.requests_graph_product order rsite hp birth wp qp widthEq
    (book).store _ (bundleScalar p scalar) _ T _ machine space fit small hidden atomCount
    (fun v u=>((s v).recipe_refs hp u).symm ▸ operands v u) (fun _ _=>le_refl p) positions a x
  · intro v u xs
    exact DescentBundleTagKeys.value old A G p R scalar _ (tag_fits hp (s v) old u (born v u)
      (arity v u) (groups v u) (stride v u)) xs
  · intro v a x
    exact DescentBundleHistory.site_read hp N scalar bit T valid s v a x

theorem argument_volume :
    (∑i,∑v,(sites i).arity v) ≤ DescentTerminalGraphVolume.bundleBudget (p:=p) N := by
  change (∑i,∑v,(order.site i).arity v) ≤ DescentTerminalGraphVolume.bundleBudget (p:=p) N
  exact (DescentTerminalGraphVolume.total_arity order).le.trans
    (DescentTerminalGraphVolume.incidence_le (p:=p) N)

include wp in
/-- Dense source requests remain bounded after reducing the target-table
arguments to their actual block references. -/
theorem headers_paid (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ) (limit : ℕ) :
    let L:=DescentTerminalCableOrder.order N home native p external nodes ops
    let genuine:=DescentTerminalBundleRows.site L rsite hp birth
    (DescentTerminalHeaderGroups.stream N home native external nodes ops q hp limit).length ≤
      DescentTerminalBinPack.purchased W (counts (q:=q) genuine) := by
  intro L genuine
  apply (DescentTerminalHeaderGroups.stream_packets N home native external nodes ops hp limit).trans
  apply DescentTerminalDenseCableFetch.packet_count_of N home native external nodes ops wp genuine
  intro i
  change (L.site i).portRows q ≤ (L.site i).portRows q+(L.site i).tableRows q+1
  omega

end
end Hierarchy.DescentTerminalBundleMenu

end OAI
