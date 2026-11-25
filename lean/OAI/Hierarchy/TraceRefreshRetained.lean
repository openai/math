import OAI.Hierarchy.TraceRetainedRoom
import OAI.Hierarchy.TraceRecordInput
import OAI.ThreeFlat.Diagonal.PhysicalRefreshAdmission
import OAI.ThreeFlat.Diagonal.NavigationStageBounds
import OAI.ThreeFlat.Diagonal.NavigationArchiveFields

namespace OAI
/-! # Publishing a selected refresh at the width of the arithmetic trace

The refresh chooses its table from the incoming graph and widths. The native guard
then checks the packed selector words at the resulting histogram address. The archive
reads below use the same accepted branch and the memory produced by this procedure.
-/

noncomputable section
namespace Hierarchy.TraceRefreshRetained

open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan
open NavigationDirectory CompressorPacking Native RefreshDemandRows RefreshTies RefreshStageNav
open scoped Classical BigOperators Fin.CommRing

variable {F : Type} [Field F] {W s rem h pad K q : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ}
  {C γ : ℝ} (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))
  (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ)

set_option quotPrecheck false
local notation "M" => refreshBinary T A hm hh sym rows zero conn
local notation "Q" => refreshBinaryFamily T A hm hh sym rows zero conn
local notation "v" => Fintype.card A.Base
local notation "m" => 2^s
local notation "d" => 1+h+pad
local notation "stage" => Stage.refresh v m (2^rem) h pad

/-- The integer comparisons made by the refresh procedure also fit for `W=64*w`
when the public stage, table and incoming wire width obey their respective bounds. -/
theorem scalarRoom (room : TraceRetainedRoom.Room q W) (fixed : refreshFixedWords T≤q)
    (alphabet : K≤q) (arena : (stage).heapWords≤q) (wire : A.maxWidth+1≤q^4) :
    v*m≤2^W ∧ 2^rem<2^W ∧ 2*d<2^W ∧ 6<2^W ∧ m*h≤2^W ∧ 2*m<2^W ∧
      m*2^rem<2^W ∧ T.last+1≤2^W ∧ K<2^W ∧
      1+2*m*m*A.maxWidth+refreshBaseBound T<2^W ∧ refreshWidthFactor T*(1+A.maxWidth)<2^W := by
  let n := RefreshStageLayout.counts v m (2^rem) h pad
  have count : (v*m)*2^rem = n.nodes := rfl
  have nodes : (v*m)*2^rem≤q := by
    rw [count]
    have amount : n.nodes≤(15+8*d)*n.nodes := Nat.le_mul_of_pos_left _ (by positivity)
    exact (amount.trans (Nat.le_add_left _ _)).trans arena
  have oldRows := (Nat.le_mul_of_pos_right (v*m) (Nat.two_pow_pos rem)).trans nodes
  have lanes : m*2^rem≤q := by
    rw [Nat.mul_assoc] at nodes
    exact (Nat.le_mul_of_pos_left _ (Fintype.card_pos : 0<v)).trans nodes
  have residual := (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos s)).trans lanes
  unfold refreshFixedWords at fixed
  have mult : m*m≤q := by
    have eq : 2*(m*m)=2*m*m := (Nat.mul_assoc ..).symm
    omega
  have measured := room.measured oldRows (show refreshWidthFactor T≤q by omega) mult
    (show refreshBaseBound T≤q by omega) wire
  have tile : 1+2*m*m*A.maxWidth+refreshBaseBound T<2^W := by
    simpa only [Nat.mul_assoc] using measured.1
  have capacity := room.single
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega,
    tile,measured.2.1⟩

/-- Before checking the register, the native scan writes the table descriptor
from the incoming graph and leaves the selector's dense words at the mounted addresses. -/
theorem prepared (cur : Word W) (input : Memory W) (csr : Cursor)
    (space : CursorSpace cur input csr K v s rem h pad)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal (s+rem)) (oldColumns csr v m)
      (fun i=>(input i).val) A.width) (fit : (Q).Fits K W) (raw : ℕ→Bool) (first : ℕ)
    (packed : ∀ (i : Fin (Q).motifs) (j : Fin K),input (csr.dense+i.val*K+j.val)=
      TraceAdmission.inputRows (Q).motifs K raw first i j)
    (room : TraceRetainedRoom.Room q W) (fixed : refreshFixedWords T≤q) (alphabet : K≤q)
    (arena : (stage).heapWords≤q) (wire : A.maxWidth+1≤q^4) :
    let pre := preparation cur T.base (fun j=>Fintype.card (T.block j).Alphabet)
    let mid := pre.run input
    AdmissionBank.Fits cur.val K mid ∧ HistogramRegister.BankLayout cur.val ((Q).rows fit)
      (TraceAdmission.inputRows (Q).motifs K raw first) mid := by
  obtain ⟨_,lanes,_,_,_,rotation,_,tiles,kfit,limit,_⟩ := scalarRoom T A room fixed alphabet arena wire
  exact refresh_bank T A hm hh sym rows zero conn cur input csr space old fit
    (TraceAdmission.inputRows (Q).motifs K raw first) packed (by omega) lanes tiles kfit limit

/-- All reads of the typed archive refer to the memory that reached the native
continuation. The stage records contain the true child IDs and fresh per-site charges. -/
def Archived (cur : Word W) (csr : Cursor) (branch : Fin (M).rules.count) (input out : Memory W)
    (old : A.ArchiveSites) : Prop :=
  let en := allocate K csr stage
  let mem := fun i=>(out i).val
  let pre := ((refreshPre T cur).pipeline cur).run input
  RefreshOutput T A hm hh sym rows zero conn K cur csr branch pre out ∧
    (∀ (i : Fin (Q).motifs) (f : Fin 3), out (csr.heap+(i.val*3+f.val))=
      ((if f.val=0 then (Q).copies i else if f.val=1 then
        (T.winner (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A)
          ((refreshBlockOrder A).symm i)).val else Fintype.card ((Q).alphabet i):ℕ):Word W)) ∧
    (∀ i, i≠cur.val → (i<csr.heap ∨ en.next.heap≤ i) → out i=input i) ∧
    ∃ row : (M).ArchiveStep branch old (refreshBinaryCharge T A hm hh sym rows zero conn branch),
      row.sites.Numbered ∧ row.sites.layer=NavigationPass.nodeLayer K csr stage ∧ row.ownerPtr=en.words 44 ∧
      row.data.Reads mem ∧ row.data.Below en.next.heap mem ∧
      row.data.Footprint (fun i=>csr.heap≤ i ∧ i<en.next.heap) mem ∧
      NavigationNodeRows.ParentReads ⟨false,row.sites.layer.first,row.ownerPtr⟩
        (fun j:Fin old.layer.count=>(row.sites.ord ((M).parent branch (old.ord.symm j))).val) mem ∧
      (∀ j:Fin old.layer.count,csr.heap≤row.ownerPtr+j.val ∧ row.ownerPtr+j.val<en.next.heap) ∧
      (∀ j,(row.data.halfWidth j).length=2*d ∧ (row.data.motifCopies j).length=1)

/-- Reconstruct the typed charge and owner rows from an already reached native
continuation. This also applies when a schedule first selects every branch and
rereads its chronological archive afterwards. -/
theorem ofOutput (cur : Word W) (input out : Memory W) (csr : Cursor) (branch : Fin (M).rules.count)
    (native : RefreshOutput T A hm hh sym rows zero conn K cur csr branch
      (((refreshPre T cur).pipeline cur).run input) out)
    (desc : ∀ (i : Fin (Q).motifs) (f : Fin 3),out (csr.heap+(i.val*3+f.val))=
      ((if f.val=0 then (Q).copies i else if f.val=1 then
        (T.winner (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A)
          ((refreshBlockOrder A).symm i)).val else Fintype.card ((Q).alphabet i):ℕ):Word W))
    (frame : ∀ i,i≠cur.val → (i<csr.heap ∨ (allocate K csr stage).next.heap≤ i) → out i=input i)
    (fit : (Q).Fits K W) (sites : A.ArchiveSites) (numbered : sites.Numbered)
    (node : sites.layer.first=csr.node) (heap : (allocate K csr stage).next.heap≤2^W)
    (ids : csr.node+v*m*2^rem≤2^W) :
    Archived T A hm hh sym rows zero conn (K:=K) cur csr branch input out sites := by
  have copies (i : Fin (Q).motifs) : out (csr.heap+i.val*3)=((Q).copies i : Word W) := by
    simpa only [Fin.val_zero,Nat.add_zero,eq_self,ite_true] using desc i 0
  let row := refreshArchiveStep T A hm hh sym rows zero conn native fit copies sites numbered node
  obtain ⟨reads,below,foot⟩ := RefreshOutput.archiveWithFootprint T A hm hh sym rows zero conn native
    heap ids
  refine ⟨native,desc,frame,row,refreshArchiveSites_numbered T A hm hh sym rows zero conn K csr branch,
    rfl,rfl,reads,below,foot,?_,?_,?_⟩
  · exact refreshArchive_parentReads T A hm hh sym rows zero conn native sites numbered (by omega)
  · exact refreshArchive_ownerFootprint (A:=A) (K:=K) (h:=h) (pad:=pad) csr sites
  · intro j
    constructor
    · change (List.ofFn (fun f : Fin (2*d)=>_)).length=2*d
      exact List.length_ofFn
    · rfl

/-- Running the installed stage on the packed bits rejects a malformed record
with zero weight. On acceptance it retains the selected graph, its widths, and
the physical archive used in subsequent stages. -/
theorem admission (field : FieldCode F W) (width : 0<W) (cur : Word W) (input : Memory W) (csr : Cursor)
    (space : CursorSpace cur input csr K v s rem h pad)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal (s+rem)) (oldColumns csr v m)
      (fun i=>(input i).val) A.width) (fit : (Q).Fits K W) (raw : ℕ→Bool) (first : ℕ)
    (packed : ∀ (i : Fin (Q).motifs) (j : Fin K),input (csr.dense+i.val*K+j.val)=
      TraceAdmission.inputRows (Q).motifs K raw first i j)
    (room : TraceRetainedRoom.Room q W) (fixed : refreshFixedWords T≤q) (alphabet : K≤q)
    (arena : (stage).heapWords≤q) (wire : A.maxWidth+1≤q^4) (symbols : refreshSymbolBound T≤K)
    (sites : A.ArchiveSites) (numbered : sites.Numbered) (node : sites.layer.first=csr.node)
    (ids : csr.node+v*m*2^rem≤2^W) :
    let body := NavigationPass.refresh cur K s h pad T sym rows zero
    let bits := List.ofFn (fun j : Fin ((Q).motifs*K*W)=>raw (W*first+j.val))
    TickStageSpec.Admission field body.block body.publicData (·=input) (fun _=>(((Q).record fit).read bits).isSome)
      (fun _ out=>∃ branch,((Q).record fit).read bits=some branch ∧
        Archived T A hm hh sym rows zero conn (K:=K) cur csr branch input out sites)
      (refreshCallTime T A sym rows zero K cur csr) := by
  let x := TraceAdmission.inputRows (W:=W) (Q).motifs K raw first
  obtain ⟨bases,lanes,deg,small,rom,rot,full,tiles,kfit,limit,widthFit⟩ := scalarRoom T A room fixed alphabet arena wire
  have hx : HistogramRegister.bitTable x=fun j=>raw (W*first+j.val) :=
    TraceAdmission.raw_stage_bits (Q).motifs K raw first
  dsimp only
  intro np nr nk machine pc reg pub exit inst data config mem atPc initial
  obtain ⟨accept,reject⟩ := refresh_admission T A hm hh sym rows zero conn field width cur input csr space old fit x packed
    bases lanes deg small rom rot full tiles symbols kfit limit widthFit machine pc reg pub exit inst data config mem atPc initial
  constructor
  · intro valid
    obtain ⟨ticks,bounded,result,out,atExit,⟨branch,hit,native,desc,frame⟩,run⟩ :=
      accept (by simpa only [hx] using valid)
    exact ⟨ticks,bounded,result,out,atExit,⟨branch,by simpa only [hx] using hit,
      ofOutput T A hm hh sym rows zero conn cur input out csr branch native desc frame fit
        sites numbered node (space.controls.trans cur.isLt.le) ids⟩,run⟩
  · intro invalid
    exact reject (by simpa only [hx] using invalid)


set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The physically selected, degree-recast refresh move and its exact navigation banks.
The immutable output contains the children, widths, repeat counts, and predecessor owners. -/
theorem archiveRecast {tariff D : ℕ} (deg : 1+h+pad=D)
    (csr : Cursor) (cur : Word W) (branch : Fin (M).rules.count) (prepared out : Memory W)
    (result : RefreshOutput T A hm hh sym rows zero conn K cur csr branch prepared out) (fit : (Q).Fits K W)
    (copies : ∀ i : Fin (Q).motifs,out (csr.heap+i.val*3)=((Q).copies i : Word W))
    (heap : (allocate K csr stage).next.heap≤2^W) (ids : csr.node+v*m*2^rem≤2^W)
    (old : A.ArchiveSites) (numbered : old.Numbered) (first : old.layer.first=csr.node)
    (chargeBound : ∀ b,(∑ y,refreshBinaryCharge T A hm hh sym rows zero conn b y)≤
      tariff*(A.positions+A.widthSum+((M).next b).positions+((M).next b).widthSum)) :
    let R:=Program.recastMove deg M
    let b:=Program.degreeTerm deg M branch
    let funding : Program.siteCharge M tariff:=⟨refreshBinaryCharge T A hm hh sym rows zero conn,chargeBound⟩
    ∃ Rstep : R.ArchiveStep b old ((Program.siteRecast deg M funding).1 b),
      let en:=allocate K csr stage
      let mem:=fun i=>(out i).val
      let owner:=fun j:Fin old.layer.count=>(Rstep.sites.ord (R.parent b (old.ord.symm j))).val
      Rstep.sites.Numbered ∧ Rstep.sites.layer=NavigationPass.nodeLayer K csr stage ∧ Rstep.ownerPtr=en.words 44 ∧
      Rstep.data.Reads mem ∧ Rstep.data.Below en.next.heap mem ∧
      Rstep.data.Footprint (fun i=>csr.heap ≤ i ∧ i<en.next.heap) mem ∧
      NavigationNodeRows.ParentReads ⟨false,Rstep.sites.layer.first,Rstep.ownerPtr⟩ owner mem ∧
      (∀ j : Fin old.layer.count,csr.heap≤Rstep.ownerPtr+j.val ∧ Rstep.ownerPtr+j.val<en.next.heap) ∧
      (∀ j,(Rstep.data.halfWidth j).length≤ NavigationPass.stageHalves stage ∧
        (Rstep.data.motifCopies j).length≤ NavigationPass.stageMotifs stage) ∧
      Rstep=Program.recastArchiveStep deg M funding branch old
        (refreshArchiveStep T A hm hh sym rows zero conn result fit copies old numbered first) := by
  cases deg
  let data:=refreshArchiveStep T A hm hh sym rows zero conn result fit copies old numbered first
  let funding : Program.siteCharge M tariff:=⟨refreshBinaryCharge T A hm hh sym rows zero conn,chargeBound⟩
  refine ⟨Program.recastArchiveStep rfl M funding branch old data,?_,rfl,rfl,?_⟩
  · exact refreshArchiveSites_numbered T A hm hh sym rows zero conn K csr branch
  obtain ⟨reads,below,foot⟩:=RefreshOutput.archiveWithFootprint T A hm hh sym rows zero conn result heap ids
  refine ⟨reads,below,foot,?_,?_,?_,rfl⟩
  · exact refreshArchive_parentReads T A hm hh sym rows zero conn result old numbered (by omega)
  · exact refreshArchive_ownerFootprint (A:=A) (K:=K) (h:=h) (pad:=pad) csr old
  · intro j
    constructor
    · change (List.ofFn (fun q : Fin (2*(1+h+pad))=>_)).length≤2*(1+h+pad)
      simp only [List.length_ofFn,le_refl]
    · exact le_rfl


end Hierarchy.TraceRefreshRetained

end
end OAI
