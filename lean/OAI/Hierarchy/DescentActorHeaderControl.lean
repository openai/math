import OAI.Hierarchy.DescentResetActorBook
import OAI.Hierarchy.DescentResetActorIssued
import OAI.Hierarchy.DescentActorHeaderImage

namespace OAI
/-! # The shared-book scalar and measured base depth for a physical actor opcode -/
namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentGL DescentColonies DescentContacts DescentChosenRouter
open DescentRelativeContacts DescentFallbackLeafScan DescentPlainTerminal DescentSharedBookScan
open DescentDenseHostOrder DescentCommonHost DescentFallbackShapeTable
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentActorRaster hiding Block
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

def zeroField (r Y Δ : ℕ) (z : Endpoint Y) (valid : z.1.2<2^z.1.1 ∧ z.1.1≤r) : Fields r Y Δ :=
  (⟨cell r z,cell_fit _ _ valid.2 valid.1⟩,0,⟨0,by dsimp [rows];positivity⟩)
def headerControl {Y : ℕ} {J : Type} (r Δ : ℕ) : Node Unit (Unit×Endpoint Y) J→Headers.Control
  | .good ..=>.rotor
  | .trunk ..=>.one
  | .fall _ (_,z) _=>if ok:z.1.2<2^z.1.1 ∧ z.1.1≤r then .tree (fieldId (zeroField r Y Δ z ok)).val else .one

variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
variable {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
variable {H w Δ : ℕ} (f : ℕ) (vertex : V↪Fin H) (peer : V→Fin Δ→Option V)
local notation "Y" => 2^Z.n
local notation "m" => T.commonDepth
local notation "r" => Z.k-m
local notation "cap" => (2^Ht:ℕ)
local notation "D" => 32*Nat.clog 2 (2*Δ)
local notation "hw" => DescentCommonPalette.rotor Z.graph
local notation "shape" => Node Unit (Unit×Endpoint Y) (hw).Site
variable (book : Chart) (src : Memory w) (out : ℕ)
local notation "totalRows" => H*DescentSharedBookScan.width r Y Δ
local notation "cpu" => ProtocolRAM.image out totalRows (DescentSharedBookScan.expr book H Δ cap) src
local notation "counted" => fun (v:Fin H) j=>(cpu (out+(v.val*DescentSharedBookScan.width r Y Δ+j))).val

omit [Fintype V] [DecidableEq V] in
/-- The source of the dynamic scalar header is the shared book produced by
the physical scanner, including all unused legal terminal shapes. -/
theorem root_level (used : ℕ) (v : V) (present : (vertex v).val<used) (q : shape)
    (depth : Fin H→ℕ) (measured : depth (vertex v)=Z.placement.b (frame.host v))
    (rom : fixed book r Y Δ H src) (room : Room book r Y Δ H w out)
    (data : DescentNativeFallbackShapes.Stored book.shapes r D g f Y cap src)
    (old : ∀u j,src (book.neighbors.base+((vertex u).val*Δ+j.val))=
      (DescentFallbackRankRAM.hostDigit vertex (peer u j):Word w))
    (flags : ∀u,src (book.isHub.base+(vertex u).val)=((hub u).toNat:Word w))
    (ww : 0<w) (totalFit : Δ*cap<2^w)
    (available : ∀z : Endpoint Y,z.1.2<2^z.1.1→z.1.1≤r→∀i h',
      h'∈DescentFallbackLeafScan.localShape r D g f z i→DescentFallbackShapeTable.shapeNumber h'+1<2^w) :
    Headers.value used m depth counted (headerControl r Δ q) (vertex v)=levelAt frame f peer v q+1 := by
  cases q with
  | good s tag j=>simp [Headers.value,headerControl,present,levelAt,measured]
  | trunk s tag=>simp [Headers.value,headerControl,present,levelAt]
  | fall s tag path=>
    obtain ⟨_,z⟩:=tag
    by_cases valid : z.1.2<2^z.1.1 ∧ z.1.1≤r
    · let p:=zeroField r Y Δ z valid
      have code:decode r Y p.1.val=z:=decode_cell _ _ valid.2 valid.1
      have att:=candidate_count frame f vertex peer book src out v p rfl (by simpa [code] using And.intro valid.2 valid.1)
        rom room data old flags ww (by simpa [code] using available z valid.1 valid.2)
      have height:=candidate_height frame f vertex peer book src out v p totalFit att
      have address:(absolute (vertex v) p).val=(vertex v).val*DescentSharedBookScan.width r Y Δ+(fieldId p).val:=by
        simp [absolute,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
      simpa only [Headers.value,headerControl,dite_eq_left valid,levelAt,←frame.extent,ite_eq_left valid,ite_eq_left present,
        address,code,p,Nat.add_right_cancel_iff] using height
    · simp [Headers.value,headerControl,levelAt,←frame.extent,valid,present]

include frame in
omit [Fintype V] [DecidableEq V] in
theorem root_tree_size (q : shape) {field : ℕ} (tree : headerControl r Δ q=.tree field) (v : V)
    (rom : fixed book r Y Δ H src) (room : Room book r Y Δ H w out)
    (data : DescentNativeFallbackShapes.Stored book.shapes r D g f Y cap src)
    (old : ∀u j,src (book.neighbors.base+((vertex u).val*Δ+j.val))=
      (DescentFallbackRankRAM.hostDigit vertex (peer u j):Word w))
    (flags : ∀u,src (book.isHub.base+(vertex u).val)=((hub u).toNat:Word w))
    (ww : 0<w) (totalFit : Δ*cap<2^w)
    (available : ∀z : Endpoint Y,z.1.2<2^z.1.1→z.1.1≤r→∀i h',
      h'∈DescentFallbackLeafScan.localShape r D g f z i→DescentFallbackShapeTable.shapeNumber h'+1<2^w) :
    counted (vertex v) field≤Δ*cap := by
  cases q with
  | good s x y=>simp [headerControl] at tree
  | trunk s z=>simp [headerControl] at tree
  | fall s name path=>
    obtain ⟨_,z⟩:=name
    simp only [headerControl] at tree
    split at tree
    next ok=>
      cases tree
      let p:=zeroField r Y Δ z ok
      have code:decode r Y p.1.val=z:=decode_cell _ _ ok.2 ok.1
      have count:=candidate_count frame f vertex peer book src out v p rfl (by simpa only [code] using And.intro ok.2 ok.1)
        rom room data old flags ww (by simpa [code] using available z ok.1 ok.2)
      have sz {s : Fin Δ×Fin cap→Prop} [DecidablePred s] : (Finset.univ.filter s).card≤Δ*cap:=by
        simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin Δ×Fin cap)) s)
      have address:(absolute (vertex v) p).val=(vertex v).val*DescentSharedBookScan.width r Y Δ+(fieldId p).val:=by
        simp [absolute,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
      change (cpu (out+((vertex v).val*DescentSharedBookScan.width r Y Δ+(fieldId p).val))).val≤_
      rw [←address,count,Fin.val_cast_of_lt (sz.trans_lt totalFit)]
      exact sz
    next h=>cases tree

theorem root_field_fit (q : shape) {j : ℕ} (hit : headerControl r Δ q=.tree j) : j<DescentSharedBookScan.width r Y Δ :=by
  cases q with
  | good s x y=>simp [headerControl] at hit
  | trunk s z=>simp [headerControl] at hit
  | fall s tx list=>
    simp only [headerControl] at hit
    split at hit
    next valid=>cases hit;exact (fieldId (zeroField r Y Δ tx.2 valid)).isLt
    next h=>cases hit

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
