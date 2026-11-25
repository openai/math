import OAI.Hierarchy.DescentTerminalPositionLeaf
import OAI.Hierarchy.DescentTerminalEmitterInputFrames

namespace OAI
/-! # Early paid position-gather reaches the scalar fold through the actual native emitter -/
namespace Hierarchy.DescentTerminalEmitter
open DescentTerminalSiteShelves DescentTerminalSpanBook DescentTerminalChronologicalBooks
open DescentTerminalRecipeRows DescentTerminalRowBooks DescentTerminalBinPack DescentTerminalDenseWindow
open DescentKernelHistory (Recipe)
open DescentTerminalHeaderScatter Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V W B S ℓ bits : ℕ} (state : Shape) (E : Layout) (D : Directory) (input : Memory bits)
def issued := image E.leaf.event.base state.pool (gather D) input
local notation "m" => issued state E D input
local notation "earlier" => routed state E m

section Execution
attribute [local irreducible] Procedure.Exec CheapCode

theorem issue_run (pos : 0<bits) (room : Room state E bits)
    (gatherFits : (gather D).Fits bits E.leaf.event.base) (endAt : E.leaf.event.base+state.pool<2^bits)
    (static : Static state E m) :
    ((scan bits E.leaf.event.base state.pool (gather D)).seq (program (w:=bits) state E)).Exec input (result state E m)
      ((4+state.pool*(2*(gather D).work+4))+time state E) ∧
    CheapCode ((scan bits E.leaf.event.base state.pool (gather D)).seq (program (w:=bits) state E)) := by
  obtain ⟨«prefix»,cheapPrefix⟩:=DescentTerminalSiteShelves.run D input E.leaf.event.base gatherFits endAt
  obtain ⟨suffix,cheapSuffix⟩:=run state E m pos room static
  let reader:=scan bits E.leaf.event.base state.pool (gather D)
  let machine:=program (w:=bits) state E
  exact ⟨@Procedure.Exec.then bits reader machine input m (result state E m)
      (4+state.pool*(2*(gather D).work+4)) (time state E) (@«prefix») (@suffix),
    @cheap_seq bits reader machine (@cheapPrefix) (@cheapSuffix)⟩

end Execution

variable (sites : Fin S→Site) (wp : 0<W) (qp : 0<q) (fit : ∀i,(sites i).rows q≤W)
    (recipes : ∀i,(v : Fin (sites i).nodes)→Recipe (Fin t) (Fin ((sites i).arity v))) (birth : ∀i,Birth (recipes i))
    (hH : ∀i v,Fintype.card (recipes i v).Hidden≤H) (hN : ∀i v,Fintype.card (recipes i v).Node≤N)
    (hA : ∀i v j,(recipes i v).arity j≤A) (hw : ∀i v j,(recipes i v).width j≤w)
    (hv : ∀i,(sites i).nodes≤V) (short : ∀i v,(sites i).arity v≤q)
    (space : purchased W (counts (q:=q) sites) ≤ state.pool)
local notation "books" => fun i=>actual (sites i) (recipes i) (birth i) (hH i) (hN i) (hA i) (hw i) (hv i) (short i)
local notation "tape" => DescentTerminalChronologicalIssue.leaf sites wp qp space recipes birth hH hN hA hw hv

theorem issued_cells (pos : 0<bits) (room : Room state E bits) (n : state.leaves=state.pool)
    (bp : 0<B) (start : Fin S→ℕ) (stream : ℕ→Bool) (leg : rowRange q t H N A w≤2^ℓ)
    (small : ∀i,(sites i).nodes*ℓ≤B) (texture : ∀i,Texture (books i) (start i) ℓ stream)
    (directory : Reached (pool:=state.pool) D input sites fit books start stream bp)
    (Wroom : W<2^bits) (readEvent : E.leaf.event.Fits bits E.leaf.cells.base) (eventRoom : state.pool≤E.leaf.event.size)
    (frames : ∀i : Fin state.pool,let p:=E.leaf.event.base+i.val
      BeforeKey state E p ∧ AfterFlights state E p ∧ p<E.scalar)
    (readRows : (DescentTerminalLeafFold.row E.leaf).Fits bits E.leaf.cells.base)
    (half : ∀(i : Fin state.pool) (j : Fin 2),E.leaf.half.read earlier ((field i j).val:Word bits)=(i.val:Word bits))
    (identity : ∀i : Fin state.pool,E.leaf.home.read earlier (i.val:Word bits)=(i.val:Word bits))
    (rom : ∀j : Fin (alphabet V W B),E.leaf.weight.read earlier (j.val:Word bits)=
      ((entry (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) qp ℓ j):Word bits)) (i : Fin state.pool) :
    E.leaf.cells.read (DescentTerminalLeafFold.reduced E.leaf earlier state.pool state.leaves E.scratch) (i.val:Word bits)=
      (DescentTerminalLeafFold.code (tape i):Word bits) := by
  rw [n]
  apply merge tape E.leaf earlier E.scratch room.leaf room.leafSize (by have:=room.endLeaf;omega) readRows half identity _ i
  intro j
  let p:=E.leaf.event.base+j.val
  have later:=frames j
  have low : p<E.leaf.cells.base:=by have:=readEvent.2.2;have:=j.isLt;dsimp [p];omega
  have frame : earlier p=m p:=(after_gate state E m room low later.2.2).symm.trans
    (printed_before state E m room later.1 later.2.1)
  rw [DescentTerminalDenseHeaderRAM.bank_nat _ readEvent (j.isLt.trans_le eventRoom),frame]
  change E.leaf.weight.read earlier (image E.leaf.event.base state.pool (gather D) input (E.leaf.event.base+j.val))=_
  rw [DescentTerminalDenseHeaderRAM.at_image,issue sites fit books start stream bp D input directory Wroom pos,rom,
    decoded sites wp qp fit recipes birth hH hN hA hw hv short space bp start stream leg small texture]

theorem field_cells (pos : 0<bits) (room : Room state E bits) (n : state.leaves=state.pool)
    (bp : 0<B) (start : Fin S→ℕ) (stream : ℕ→Bool)
    (small : ∀i,(sites i).nodes*DescentTerminalVertexFields.span q t H N A w≤B)
    (source : ∀i,DescentTerminalVertexFields.Source (books i) (start i) stream)
    (directory : Reached (pool:=state.pool) D input sites fit books start stream bp)
    (Wroom : W<2^bits) (readEvent : E.leaf.event.Fits bits E.leaf.cells.base) (eventRoom : state.pool≤E.leaf.event.size)
    (frames : ∀i : Fin state.pool,let p:=E.leaf.event.base+i.val
      BeforeKey state E p ∧ AfterFlights state E p ∧ p<E.scalar)
    (readRows : (DescentTerminalLeafFold.row E.leaf).Fits bits E.leaf.cells.base)
    (half : ∀(i : Fin state.pool) (j : Fin 2),E.leaf.half.read earlier ((field i j).val:Word bits)=(i.val:Word bits))
    (identity : ∀i : Fin state.pool,E.leaf.home.read earlier (i.val:Word bits)=(i.val:Word bits))
    (rom : ∀j : Fin (alphabet V W B),E.leaf.weight.read earlier (j.val:Word bits)=
      ((entryBy (DescentTerminalVertexFields.decode (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)) qp j):Word bits)) (i : Fin state.pool) :
    E.leaf.cells.read (DescentTerminalLeafFold.reduced E.leaf earlier state.pool state.leaves E.scratch) (i.val:Word bits)=
      (DescentTerminalLeafFold.code (tape i):Word bits) := by
  rw [n]
  apply merge tape E.leaf earlier E.scratch room.leaf room.leafSize (by have:=room.endLeaf;omega) readRows half identity _ i
  intro j
  let p:=E.leaf.event.base+j.val
  have later:=frames j
  have low : p<E.leaf.cells.base:=by have:=readEvent.2.2;have:=j.isLt;dsimp [p];omega
  have frame : earlier p=m p:=(after_gate state E m room low later.2.2).symm.trans
    (printed_before state E m room later.1 later.2.1)
  rw [DescentTerminalDenseHeaderRAM.bank_nat _ readEvent (j.isLt.trans_le eventRoom),frame]
  change E.leaf.weight.read earlier (image E.leaf.event.base state.pool (gather D) input (E.leaf.event.base+j.val))=_
  rw [DescentTerminalDenseHeaderRAM.at_image,issue sites fit books start stream bp D input directory Wroom pos,rom,
    decoded_fields sites wp qp fit recipes birth hH hN hA hw hv short space bp start stream small source]

end
end Hierarchy.DescentTerminalEmitter

end OAI
