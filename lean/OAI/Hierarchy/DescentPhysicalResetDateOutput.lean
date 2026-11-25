import OAI.Hierarchy.DescentPhysicalResetDate
import OAI.Hierarchy.DescentTerminalExecUnique
import OAI.Hierarchy.DescentDatedSavedRotation

namespace OAI
/-! # The original selected matrix survives a complete physical reset -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSIMDLookup DescentSixParty DescentSixParty.Chronology DescentGLPacked DescentColonies DescentCompiler DescentPlainTerminal.Suffix
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : FinalInputs u)
local notation "P₀" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "root" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "actorFloor" => (v).middle.stop b
local notation "stencil" => a.throughStencil u.shape floor u.count u.hub u.g u.Y u.src u.sourceRows u.oldDegree w
local notation "time_" => a.throughStencilTicks u.shape floor u.count u.hub u.g u.Y u.sourceRows u.oldDegree w

local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "rootTime" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits

namespace DateInputs
variable (u)

/-- Reads arbitrary words in the authenticated earlier root publication from
the same native operand result supplied to the subsequent funding pass. -/
theorem prefix_unchanged (ready : u.Ready) {before afterRoots out : Memory w}
    (toRoot : (head).Exec before afterRoots rootTime) (toOperands : u.throughOperandDate.Runs before out)
    (i : ℕ) (early : i<(root).preparedEnd u.book) : out i=afterRoots i := by
  obtain ⟨_,_,cheap,_⟩:=a.throughPublishedRoots_any_framed u.shape floor u.count u.hub u.g u.Y u.roots
    u.book u.src u.sourceRows u.oldDegree w u.bookFits before ready.prime ready.stencil
  obtain ⟨dst,runner,_,keep⟩:=u.run_to_operands_from_roots ready before afterRoots (@toRoot) (@cheap)
  exact (congrFun (exec_unique u.throughOperands before out dst (@toOperands) (@runner)) i).trans (keep i (Or.inl (early.trans_le ready.rootEnd.le)))

end DateInputs

theorem date_image (room : z.Room) {m mid dst : Memory w} (ran : (date z).Runs m dst)
    (operands : u.throughOperandDate.Runs m mid) : dst=z.finalImage mid := by
  have tailRun : z.tailCode.Exec mid (z.finalImage mid) z.tailTime := z.tail_image room mid
  exact exec_unique (u.throughOperands.seq z.tailCode) m dst (z.finalImage mid) (@ran)
    (@Procedure.Exec.then w u.throughOperands z.tailCode m mid (z.finalImage mid)
      u.throughOperandTicks z.tailTime (@operands) (@tailRun))

theorem date_output_below (ready : u.Ready) (room : z.Room) {m out : Memory w}
    (run : (date z).Runs m out) (i : ℕ) (outside : i<floor ∨ a.endAddress floor≤ i) :
    out i=m i := by
  obtain ⟨dst,other,_,frame⟩:=date_any z ready room m
  exact (congrFun (exec_unique (u.throughOperands.seq z.tailCode) m out dst (@run) (@other)) i).trans (frame i outside)

/-- All original measured stencil words can be read at the chronological date boundary. -/
theorem date_stencil_below (ready : u.Ready) (room : z.Room) {m measured out : Memory w}
    (run : (date z).Runs m out) (scanned : (stencil).Exec m measured time_) :
    ∀i,i<(P₀).endAddress→ out i=measured i := by
  obtain ⟨_,_,cheap,_⟩:=a.throughStencil_any_framed u.shape floor u.count u.hub u.g u.Y u.src
    u.sourceRows u.oldDegree w m ready.prime ready.stencil
  obtain ⟨rootExec,rootCheap,rootFrame⟩:=(root).prepared_any u.book u.bookFits measured
  let rootOut := (root).preparedImage u.book u.bookFits measured
  let rootCode := (root).preparedRoots u.book u.bookFits
  obtain ⟨mid,toMid,_,midFrame⟩ := u.run_to_operands_from_roots ready m rootOut
    (@Procedure.Exec.then w stencil rootCode m measured rootOut time_ ((root).preparedTicks u.book u.bookFits)
      (@scanned) (@rootExec))
    (@cheap_seq w stencil rootCode (@cheap) (@rootCheap))
  obtain ⟨dst,finish,_,endFrame⟩:=z.tail_any room mid
  have equal : out=dst := exec_unique (u.throughOperands.seq z.tailCode) m out dst (@run)
    (@Procedure.Exec.then w u.throughOperands z.tailCode m mid dst u.throughOperandTicks z.tailTime (@toMid) (@finish))
  have limits := u.book.limits (root).projectionEnd (v).middle.signedHosts (2^(v).middle.stencil.c)
    (v).middle.signedLanes
  have prepared : (P₀).endAddress ≤ (root).preparedEnd u.book :=
    (root).origin_le_projection.trans
      ((limits.1.trans (limits.2.1.trans limits.2.2)).trans (Nat.le_add_right ..))
  have before : (P₀).endAddress ≤ actorFloor := prepared.trans ready.rootEnd.le
  obtain ⟨_,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=ready.ordered
  intro i hi
  have early:=hi.trans_le before
  exact (congrFun equal i).trans ((endFrame i (Or.inl (by omega))).trans
    ((midFrame i (Or.inl early)).trans (rootFrame i (Or.inl hi))))

theorem stencil_saved_before : (P₀).saved<(P₀).endAddress := by
  have start : (P₀).saved<(P₀).first := Nat.lt_succ_self _
  have included : (P₀).first≤(P₀).base :=by
    unfold PackedFlow.ResetMiddle.base Subwords.finish Subwords.destination
    omega
  have top : (P₀).base≤(P₀).endAddress :=by
    rw [PackedFlow.ResetMiddle.endAddress,(P₀).S.extent]
    simp only [Nat.add_assoc]
    exact Nat.le_add_right _ _
  exact start.trans_le (included.trans top)

/-- Reads the chosen rotation at NativeDate.saved on the caller's actual completion. -/
theorem date_saved {F Pin : Type} [Field F] {base : ℕ} (stage : floor=a.stageStart base) (ready : u.Ready) (room : z.Room)
    {m measured out : Memory w} (run : (date z).Runs m out) (scanned : (stencil).Exec m measured time_)
    {value : Word w} (selected : measured (P₀).saved=value) :
    out ((NativeDate.reset (F:=F) (P:=Pin) a).saved base)=value := by
  have addr : (NativeDate.reset (F:=F) (P:=Pin) a).saved base=(P₀).saved := by cases stage; rfl
  rw [addr]
  exact (date_stencil_below z ready room run scanned _ (stencil_saved_before (u:=u))).trans selected

private theorem matrix_code_congr {n k : ℕ} {C : DescentGL.Layout n} {B : DescentGL.Layout k}
    (dim : n=k) (tied : HEq C B) : (DescentExterior.matrixCode C).val=(DescentExterior.matrixCode B).val := by
  subst k
  rw [eq_of_heq tied]

/-- The basis is the one chosen by the reached recorded reset. The stencil receipt
identifies it before the root, signed, primitive, and metadata programs execute. -/
theorem date_saved_basis {F Pin : Type} [Field F] {base : ℕ} (stage : floor=a.stageStart base) (ready : u.Ready) (room : z.Room)
    {m out : Memory w} (run : (date z).Runs m out) {k : ℕ} (basis : DescentGL.Layout k)
    (dim : (a.estimator floor).dim=k)
    (measured : ∃(C : DescentGL.Layout (a.estimator floor).dim) (st : Memory w), HEq C basis ∧
      (stencil).Exec m st time_ ∧ st (P₀).saved=((DescentExterior.matrixCode C).val:Word w)) :
    out ((NativeDate.reset (F:=F) (P:=Pin) a).saved base)=((DescentExterior.matrixCode basis).val:Word w) := by
  obtain ⟨C,st,tied,scanned,chosen⟩ := measured
  rw [←matrix_code_congr dim tied]
  exact date_saved z (F:=F) (Pin:=Pin) stage ready room run scanned chosen

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
