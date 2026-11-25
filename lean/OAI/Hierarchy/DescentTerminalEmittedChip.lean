import OAI.Hierarchy.DescentTerminalEmittedChipInputs
import OAI.Hierarchy.DescentTerminalEmittedShelfReads
import OAI.Hierarchy.DescentTerminalScatterColumns

namespace OAI
/-! # Authentic graph-wired inputs of the terminal five-scan machine -/
namespace Hierarchy.DescentTerminalEmitter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalChipRuntime DescentTerminalChipPins DescentTerminalChipSource DescentTerminalBinReaddress
open DescentTerminalDenseWindow DescentTerminalScalarPadded DescentTerminalRecipeRows DescentTerminalGraphPositions
open DescentTerminalDenseWindowRAM (radix)
open DescentKernelHistory DescentTerminalCableOrder DescentTerminalDenseGraphRead Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false

private theorem extend_cast {A B : Type} {n k : ℕ} (e : A ↪ Fin n) (data : A→B) (gap : B)
    (size : n=k) (i : Fin n) :
    Function.extend (e.trans (finCongr size).toEmbedding) data (fun _=>gap) (i.cast size)=
      Function.extend e data (fun _=>gap) i := by subst k;rfl

variable {P Tag : Type} [Fintype P] {D M K W q piece w : ℕ} {bits : P→ℕ}
    (S : Shape) (E : Layout) (m : Memory w) (room : Room S E w) (pos : 0<w)
    (N : Network D P bits) (home : N.Site→Fin M) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (ext : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ)
local notation "p" => W*piece
local notation "geom" => DescentTerminalCableOrder.order (S:=M) (D:=D) (P:=P) (bits:=bits)
  N home native p ext nodes ops
variable (r : ∀v,Recipe Tag (DescentTerminalBundleRows.SiteRef («p»:=W*piece) N v)) (hp : 0<W*piece)
    (birth : ∀v,(r v).Node ↪ ℕ) (wp : 0<W) (qp : 0<q)
local notation "sites" => DescentTerminalBundleRows.site (G:=N) (S:=M) («p»:=p) (Tag:=Tag) geom r hp birth
local notation "n" => K*W
variable (bins : Bins (W:=W) (q:=q)
    (DescentTerminalBundleRows.site (DescentTerminalCableOrder.order N home native (W*piece) ext nodes ops) r hp birth) ≤ K)
    (pay : Fin S.plane.rawRows × Fin (q*(W*piece))→Bool) (outer : Ports bits)
local notation "s" => content (K₀:=K) (W:=W) (q:=q) (piece:=piece) N home native ext nodes ops r hp birth wp qp rfl pay outer
local notation "B" => q*p

section
attribute [local irreducible] DescentTerminalCableOrder.order DescentTerminalBundleRows.site
  DescentTerminalScatterColumns.fixed

structure ControlColumns (b : Banks) where
  indexChart : K*W=E.indices.count
  fmtChart : K*W=E.formats.count
  firstMode : E.indices.blank=0
  blankMode : E.formats.blank=(formatIndex q (W*piece) (blank q (W*piece))).val
  indexBase : b.index.base=E.indices.output.base
  fmtBase : b.formats.base=E.formats.output.base
  first : Header.Emits E.indices (external S E m)
    ((DescentTerminalScatterColumns.fixed (K₀:=K) (q:=q)
      (DescentTerminalBundleRows.site (DescentTerminalCableOrder.order N home native (W*piece) ext nodes ops) r hp birth)
      wp bins).trans (finCongr indexChart).toEmbedding)
    (fun a=>(DescentTerminalScalarInput.index (rawRows:=S.plane.rawRows) (q:=q)
      N home native ext nodes ops r hp birth (anchor _ qp a):Computability.VPVNP.BurstRAM.Word w))
  format : Header.Emits E.formats (indexed S E m)
    ((DescentTerminalScatterColumns.fixed (K₀:=K) (q:=q)
      (DescentTerminalBundleRows.site (DescentTerminalCableOrder.order N home native (W*piece) ext nodes ops) r hp birth)
      wp bins).trans (finCongr fmtChart).toEmbedding)
    (fun a=>((formatIndex q (W*piece) (DescentTerminalScalarInput.control N home native ext nodes ops r hp birth qp
      (anchor _ qp a))).val:Computability.VPVNP.BurstRAM.Word w))
  checkIndex : ∀i : Fin (K*W),AfterNames E (b.index.base+i.val) ∧ b.index.base+i.val<E.formats.output.base
  checkFormat : ∀i : Fin (K*W),AfterNames E (b.formats.base+i.val)
end

variable (b : Banks) (z : DescentTerminalChipPins.Inputs K W q piece→Bool)
include room pos in
theorem columns (arr : ControlColumns S E m N home native ext nodes ops r hp birth wp qp bins b) :
    (∀i,result S E m (b.index.base+i.val)=((s).first i:Computability.VPVNP.BurstRAM.Word w)) ∧
    (∀i,result S E m (b.formats.base+i.val)=((formatIndex q p ((s).format i)).val:Computability.VPVNP.BurstRAM.Word w)) := by
  constructor
  · apply DescentTerminalScatterColumns.index_read (K:=K) (piece:=piece) wp N home native ext nodes ops r hp birth qp bins rfl pay outer
      b.index.base (result S E m)
    intro i
    obtain ⟨later,other⟩:=arr.checkIndex i
    rw [after_index S E m room later other,arr.indexBase,indexed]
    unfold DescentTerminalScatterColumns.recorded
    have found:=Header.read E.indices _ _ _ room.idx pos arr.first (i.cast arr.indexChart)
    simpa only [Fin.val_cast,arr.firstMode,Nat.cast_zero,extend_cast] using found
  · apply DescentTerminalScatterColumns.format_read (K:=K) (piece:=piece) wp N home native ext nodes ops r hp birth qp bins rfl pay outer
      b.formats.base (result S E m)
    intro i
    rw [after_format S E m room (arr.checkFormat i),arr.fmtBase,formatted]
    unfold DescentTerminalScatterColumns.recorded
    have found:=Header.read E.formats _ _ _ room.fmt pos arr.format (i.cast arr.fmtChart)
    simpa only [Fin.val_cast,arr.blankMode,extend_cast] using found

structure SourceRows (b : Banks) where
  rawBank : b.raw=E.plane.raw
  volume : (∑z,bits z)≤S.plane.publicRows*(q*(W*piece))
  cap : S.plane.rawRows+2+S.plane.publicRows≤E.plane.raw.size
  candidate : S.plane.rawRows≤E.plane.candidate.size
  «public» : S.plane.publicRows≤E.plane.output.size
  hidden : ∀i : Fin S.plane.rawRows,DescentTerminalDataPlane.exteriorRows S.plane E.plane m (E.plane.candidate.base+i.val)=
    ((dense (q*(W*piece)) (stream pay) i.val).val:Computability.VPVNP.BurstRAM.Word w)
  exterior : ∀i : Fin S.plane.publicRows,DescentTerminalDataPlane.exteriorRows S.plane E.plane m (E.plane.output.base+i.val)=
    ((dense (q*(W*piece)) (publicStream ext outer) i.val).val:Computability.VPVNP.BurstRAM.Word w)
  frame : ∀j<E.plane.raw.size,Later E (E.plane.raw.base+j) ∧ E.plane.raw.base+j<E.plane.header.rem.base

include room pos in
theorem tapes (controls : ControlColumns S E m N home native ext nodes ops r hp birth wp qp bins b)
    (cables : SourceRows (W:=W) (q:=q) (piece:=piece) S E m ext pay outer b)
    (gateRows : S.rows=K*W) (gateBank : E.route.gate.base=b.gate.base)
    (gateLife : ∀i : Fin n,b.gate.base+3*i.val<E.leaf.cells.base ∧ b.gate.base+3*i.val<E.scalar)
    {G V M0 A a : ℕ} (localFit : ∀i,DescentTerminalLocalPortBook.Room (sites i) G V M0 A)
    (size : ∀i,(sites i).rows q≤W) (names : ∀i,(sites i).Name ↪ Computability.VPVNP.BurstRAM.Word a) (args : ∀i,(sites i).Arg → Computability.VPVNP.BurstRAM.Word a)
    (matchNames : ∀i v,args i v=names i ((sites i).arg v.1 v.2))
    (route : DescentTerminalRouteIssue.Fits E.route w (K*W))
    (rows : DescentTerminalRouteIssue.Reads (K:=K) (W:=W) (q:=q) (a:=Nat.clog 2 (W*2^a)) E.route
      (DescentTerminalLocalPortBook.rows (K₀:=K) (q:=q) sites wp localFit names args) (named S E m))
    (boot : Boot b (result S E m) z) : Tapes b s (result S E m) z := by
  obtain ⟨firstCol,fmtCol⟩:=columns S E m room pos N home native ext nodes ops r hp birth wp qp bins pay outer b controls
  refine ⟨firstCol,fmtCol,?_,?_,boot.pins,boot.high,boot.menu,boot.lookup,boot.ptr,boot.route⟩
  · intro j bound
    rw [cables.rawBank] at bound ⊢
    exact rawWords S E m room ext outer pay cables.volume cables.cap cables.candidate cables.public cables.hidden cables.exterior cables.frame j bound
  · intro i
    rw [after_gate S E m room (gateLife i).1 (gateLife i).2,←gateBank,routed,gateRows]
    exact DescentTerminalLocalPortBook.authentic sites wp qp localFit size names args matchNames E.route _ route rows i

include room pos in
theorem chips (A0 : DescentTerminalChipRuntime.Layout) (controls : ControlColumns S E m N home native ext nodes ops r hp birth wp qp bins b)
    (cables : SourceRows (W:=W) (q:=q) (piece:=piece) S E m ext pay outer b)
    (gateRows : S.rows=K*W) (gateBank : E.route.gate.base=b.gate.base)
    (gateLife : ∀i : Fin n,b.gate.base+3*i.val<E.leaf.cells.base ∧ b.gate.base+3*i.val<E.scalar)
    {G V M0 A a : ℕ} (localFit : ∀i,DescentTerminalLocalPortBook.Room (sites i) G V M0 A)
    (size : ∀i,(sites i).rows q≤W) (names : ∀i,(sites i).Name ↪ Computability.VPVNP.BurstRAM.Word a) (args : ∀i,(sites i).Arg → Computability.VPVNP.BurstRAM.Word a)
    (matchNames : ∀i v,args i v=names i ((sites i).arg v.1 v.2))
    (route : DescentTerminalRouteIssue.Fits E.route w (K*W))
    (rows : DescentTerminalRouteIssue.Reads (K:=K) (W:=W) (q:=q) (a:=Nat.clog 2 (W*2^a)) E.route
      (DescentTerminalLocalPortBook.rows (K₀:=K) (q:=q) sites wp localFit names args) (named S E m))
    (boot : Boot b (result S E m) z) (wordFit : B≤w)
    (fits : ∀x∈[b.index,b.formats,b.raw,b.menuStart,b.highField,b.denseROM],x.Fits w A0.first)
    (sizes : n≤b.index.size ∧ n≤b.formats.size ∧ Menus q p≤b.menuStart.size ∧ radix q p≤b.highField.size ∧
      Menus q p*(radix q p*radix q p)≤b.denseROM.size)
    (seen : ∀i,(s).first i+1<b.raw.size)
    (routeFit : b.gate.Fits w A0.first ∧ b.joinedX.Fits w A0.first ∧ b.pointer.Fits w A0.first ∧ b.routeROM.Fits w A0.first)
    (routeSize : 3*n≤b.gate.size ∧ n≤b.joinedX.size ∧ 2^(DescentTerminalBinFormat.controlBits W q)≤b.pointer.size ∧
      2^(DescentTerminalBinFormat.controlBits W q)*2^(sliceWidth W q piece)≤b.routeROM.size) :
    Chips A0 b s (result S E m) z :=
  DescentTerminalChipSource.chips A0 b s (result S E m) z wordFit fits sizes seen routeFit routeSize
    (tapes S E m room pos N home native ext nodes ops r hp birth wp qp bins pay outer b z
      controls cables gateRows gateBank gateLife localFit size names args matchNames route rows boot)

end
end Hierarchy.DescentTerminalEmitter

end OAI
