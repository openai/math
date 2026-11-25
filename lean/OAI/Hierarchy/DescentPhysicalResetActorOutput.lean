import OAI.Hierarchy.DescentPhysicalResetDateOutput
import OAI.Hierarchy.DescentStageVenueWireRoom
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # The emitted dense-rank directory survives a complete reset date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentGLPacked DescentCompiler
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "P₀" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "root" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "actorFloor" => (v).middle.stop b
local notation "A₀" => (v).actor
local notation "ds" => (A₀).directory actorFloor
local notation "scene" => (A₀).scene actorFloor
local notation "stencil" => a.throughStencil u.shape floor u.count u.hub u.g u.Y u.src u.sourceRows u.oldDegree w
local notation "scanTime" => a.throughStencilTicks u.shape floor u.count u.hub u.g u.Y u.sourceRows u.oldDegree w
local notation "publication" => (((root).preparedRoots u.book u.bookFits).seq ((A₀).classifier u.actor actorFloor w)).seq ((ds).program w scene)
local notation "ticks" => ((root).preparedTicks u.book u.bookFits+(A₀).classifierTime u.actor actorFloor w)+(ds).ticks scene

private theorem regroup {w : ℕ} (A B C D : Procedure w)
    {memA memB memC memD memE out : Memory w} {i j k l : ℕ}
    (scan : A.Exec memA memB i) (rootRun : B.Exec memB memC j) (classification : C.Exec memC memD k)
    (write : D.Exec memD memE l) (published : ((B.seq C).seq D).Exec memB out ((j+k)+l))
    (cheapAB : CheapCode (A.seq B)) (cheapCD : CheapCode (C.seq D)) :
    ((A.seq B).seq (C.seq D)).Exec memA out ((i+j)+(k+l)) ∧ CheapCode ((A.seq B).seq (C.seq D)) := by
  have same := exec_unique ((B.seq C).seq D) memB memE out
    (@Procedure.Exec.then w (B.seq C) D memB memD memE (j+k) l
      (@Procedure.Exec.then w B C memB memC memD j k @rootRun @classification) @write) @published
  subst out
  exact ⟨@Procedure.Exec.then w (A.seq B) (C.seq D) memA memC memE (i+j) (k+l)
      (@Procedure.Exec.then w A B memA memB memC i j @scan @rootRun)
      (@Procedure.Exec.then w C D memC memD memE k l @classification @write),
    @cheap_seq w (A.seq B) (C.seq D) @cheapAB @cheapCD⟩

set_option maxHeartbeats 1000000 in
/-- Reassociate the two genuine stage executions into the compiler's dated prefix. -/
theorem DateInputs.classified_prefix (ready : u.Ready) {initial measured actors : Memory w}
    (scanned : (stencil).Exec initial measured scanTime)
    (published : (publication).Exec measured actors ticks) :
    let head:=a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
    let time:=a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
    let body:=(A₀).actorBody u.actor actorFloor w
    (head.seq body).Exec initial actors (time+(A₀).actorTicks u.actor actorFloor w) ∧ CheapCode (head.seq body) := by
  dsimp only
  obtain ⟨rootExec,_,_⟩:=(root).prepared_any u.book u.bookFits measured
  obtain ⟨_,_,cheapHead,_⟩:=a.throughPublishedRoots_any_framed u.shape floor u.count u.hub u.g u.Y u.roots
    u.book u.src u.sourceRows u.oldDegree w u.bookFits initial ready.prime ready.stencil
  obtain ⟨intermediate,actual,scan,issue,cheapActors,_⟩:=(A₀).dated_parts u.actor actorFloor ((root).preparedImage u.book u.bookFits measured) ready.actor
  exact @regroup w stencil ((root).preparedRoots u.book u.bookFits)
    ((A₀).classifier u.actor actorFloor w) ((ds).program w scene)
    initial measured ((root).preparedImage u.book u.bookFits measured) intermediate actual actors
    scanTime ((root).preparedTicks u.book u.bookFits) ((A₀).classifierTime u.actor actorFloor w)
    ((ds).ticks scene) @scanned @rootExec @scan @issue @published @cheapHead @cheapActors

/-- At the operand snapshot the original published directory and actor scene still agree at every earlier word. -/
theorem DateInputs.operand_actor_below (ready : u.Ready) {initial measured actors out : Memory w}
    (run : u.throughOperandDate.Runs initial out) (scanned : (stencil).Exec initial measured scanTime)
    (published : (publication).Exec measured actors ticks) :
    ∀i,i<(v).actorEnd b→ out i=actors i := by
  obtain ⟨«prefix»,cheap⟩:=DateInputs.classified_prefix (u:=u) ready scanned published
  obtain ⟨mid,toMid,_,keep⟩:=u.run_to_operands_from_actors ready initial actors «prefix» cheap
  have finalEq : out=mid:=exec_unique _ initial out mid run toMid
  exact fun i hi=>(congrFun finalEq i).trans (keep i (Or.inl hi))

/-- The actor proof issues roots, then its classifier, then the directories. This
is the same RAM image as the regrouped native date instruction stream. -/
theorem date_actor_below (ready : u.Ready) (room : z.Room) {initial measured actors out : Memory w}
    (run : (date z).Runs initial out) (scanned : (stencil).Exec initial measured scanTime)
    (published : (publication).Exec measured actors ticks) :
    ∀i,i<(v).actorEnd b→ out i=actors i := by
  obtain ⟨mid,«prefix»,_,_⟩:=u.run_to_operands ready initial
  obtain ⟨dst,finish,_,last⟩:=z.tail_any room mid
  have finalEq : out=dst:=exec_unique _ initial out dst run («prefix».then finish)
  obtain ⟨_,_,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=ready.ordered
  intro i hi
  exact (congrFun finalEq i).trans ((last i (Or.inl (by omega))).trans
    (DateInputs.operand_actor_below (u:=u) ready «prefix» scanned published i hi))

theorem DateInputs.actor_rank_space (u : a.DateInputs floor w) (ready : u.Ready) :
    (ds).ranks.Fits w ((v).actorEnd b) := by
  have roof : (ds).endAddress<2^w := ready.actor.room
  have whole : (ds).ranks.base+(ds).ranks.size≤(ds).endAddress := by
    change (ds).first+2*(ds).pitch+(ds).pitch≤(ds).first+(4*(ds).pitch+1+4*(ds).sites)
    omega
  have small : (ds).ranks.size<2^w := (Nat.le_add_left ..).trans_lt (whole.trans_lt roof)
  exact ⟨Nat.two_pow_pos _,small,whole⟩

/-- Full padded rank-bank extent and genuine dynamic lookup, including when
the original graph has no hosts. -/
theorem actor_rank_read (ready : u.Ready) (room : z.Room) {initial measured actors out : Memory w}
    (run : (date z).Runs initial out) (scanned : (stencil).Exec initial measured scanTime)
    (published : (publication).Exec measured actors ticks) (i : Fin (ds).sites) :
    (ds).ranks.Fits w ((v).actorEnd b) ∧
    (ds).ranks.read out (i.val:Word w)=actors ((ds).ranks.base+i.val) := by
  have fit:=u.actor_rank_space ready
  have whole:=fit.2.2
  have idx : i.val<(ds).ranks.size := i.isLt.trans_le (ds).ordered.1
  exact ⟨fit,(DescentPackedZip.bank_read (ds).ranks out idx fit).trans
    (date_actor_below z ready room run scanned published _ ((Nat.add_lt_add_left idx _).trans_le whole))⟩

/-- The scalar count from the genuine directory publisher is still the scalar
count in the fully completed reset, at the same interior RAM word. -/
theorem date_actor_count (ready : u.Ready) (room : z.Room) {initial measured actors out : Memory w}
    (run : (date z).Runs initial out) (scanned : (stencil).Exec initial measured scanTime)
    (published : (publication).Exec measured actors ticks) {n : ℕ}
    (issued : actors (ds).count.base=(n:Word w)) :
    out (ds).count.base=(n:Word w) ∧ ∀r : Word w,(ds).count.read out r=(n:Word w):=by
  have safe:=(ds).fits ready.actor.room
  have countFit:=(safe.2.2.2.1)
  have low:(ds).count.base<(v).actorEnd b:=(Nat.lt_add_of_pos_right countFit.1).trans_le countFit.2.2
  have kept:out (ds).count.base=(n:Word w):=(date_actor_below z ready room run scanned published _ low).trans issued
  refine ⟨kept,?_⟩
  intro r
  simpa only [Bank.read,DescentResetNewActorDirectory.Layout.count,Bank.size,pow_zero,Nat.mod_one,Nat.add_zero] using kept

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
