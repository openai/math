import OAI.Hierarchy.DescentDatedOperandBankSlots
import OAI.Hierarchy.DescentDatedPriorOperand
import OAI.Hierarchy.DescentPriorOperandResolve
import OAI.Hierarchy.DescentPriorOperandHardware

namespace OAI
/-! # Fixed all-slot native code for an ordinary receiver's retained operand columns -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentOperandStateBanks ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

namespace Banks
variable {l : Layout} (t : Banks l)

def args (j : Fin l.jobs) (i : Fin 3) : Expr:=.lookup (t.route j i) .row

def fields (floor : ℕ) (j : Fin l.jobs) : Fin 10→Bank :=
  let ix:=(l.index).symm j
  DescentPriorOperandColumns.fields (fun f=>DescentPriorOperandColumns.fieldBank (l.projected floor) l.rows
    (DescentPriorOperandColumns.pageOf ix.2.2 f) ix.2.1) (t.side j)

def one (w floor : ℕ) (j : Fin l.jobs) :=
  (DescentPriorOperandColumns.program (t.book j) (l.size+2) l.nodes l.lanes l.rows w floor (l.projected floor)).seq
    (DescentOrdinaryLocalFragment.hardware (l.splice floor) l.size l.hosts l.groups l.lanes w (t.fields floor j) (t.args j 0) (t.args j 1) (t.args j 2))

def image {w : ℕ} (floor : ℕ) (j : Fin l.jobs) (m : Memory w) :=
  DescentOrdinaryLocalFragment.outputMemory (l.splice floor) l.size l.hosts l.groups l.lanes (t.fields floor j) (t.args j 0) (t.args j 1) (t.args j 2)
    (DescentPriorOperandColumns.image (t.book j) (l.size+2) l.nodes l.lanes l.rows floor (l.projected floor) m)

def time (floor : ℕ) (j : Fin l.jobs) :=
  DescentPriorOperandColumns.ticks (t.book j) (l.size+2) l.nodes l.lanes l.rows floor (l.projected floor)+
    DescentOrdinaryLocalFragment.time (l.splice floor) l.size l.hosts l.groups l.lanes (t.fields floor j) (t.args j 0) (t.args j 1) (t.args j 2)

theorem time_bound (floor : ℕ) (j : Fin l.jobs) : t.time floor j≤l.clockPer := by
  have a:=DescentPriorOperandColumns.tariff (t.book j) (l.size+2) l.nodes l.lanes l.rows floor (l.projected floor)
  have b:=DescentOrdinaryLocalFragment.time_bound (l.splice floor) l.size l.hosts l.groups l.lanes (t.fields floor j) (t.args j 0) (t.args j 1) (t.args j 2)
  have aspan : DescentOrdinaryLocalFragment.maxField (t.args j 0) (t.args j 1) (t.args j 2)=139:=rfl
  rw [aspan] at b
  unfold time Layout.clockPer
  apply Nat.add_le_add a
  simpa only [Layout.rows,Layout.splicePage,Layout.resolverPage,DescentOrdinaryLocalFragment.width,
    DescentPackedOperand.ROM.page,DescentPackedOperand.unit,Nat.mul_comm 282] using b

theorem names_bound (w floor : ℕ) (j : Fin l.jobs) : DescentStaticWordColumn.names (t.one w floor j)≤l.textPer := by
  have a:=DescentPriorOperandColumns.names (t.book j) (l.size+2) l.nodes l.lanes l.rows w floor (l.projected floor)
  have b:=DescentOrdinaryLocalFragment.names_bound (l.splice floor) l.size l.hosts l.groups l.lanes w (t.fields floor j) (t.args j 0) (t.args j 1) (t.args j 2)
  rw [one,DescentStaticWordColumn.names_seq]
  exact Nat.add_le_add a b

def code (t : Banks l) (w floor : ℕ) : List (Fin l.jobs)→Procedure w
  | []=>ProtocolRAM.program w []
  | j::js=>(t.one w (l.slot floor j.val) j).seq (code t w floor js)

def state (t : Banks l) {w : ℕ} (floor : ℕ) : List (Fin l.jobs)→Memory w→Memory w
  | [],m=>m
  | j::js,m=>state t floor js (t.image (l.slot floor j.val) j m)

def cost (t : Banks l) (floor : ℕ) : List (Fin l.jobs)→ℕ
  | []=>4
  | j::js=>t.time (l.slot floor j.val) j+cost t floor js

def program (w floor : ℕ) :=t.code w floor (List.finRange l.jobs)
def result {w : ℕ} (floor : ℕ) (m : Memory w) :=t.state floor (List.finRange l.jobs) m
def ticks (floor : ℕ) :=t.cost floor (List.finRange l.jobs)

theorem priced (w floor : ℕ) : t.ticks floor≤l.clockBudget ∧ DescentStaticWordColumn.names (t.program w floor)≤l.hardwareBudget := by
  have bound (jobs : List (Fin l.jobs)) : t.cost floor jobs≤jobs.length*l.clockPer+4 ∧
      DescentStaticWordColumn.names (t.code w floor jobs)≤jobs.length*l.textPer+15 := by
    induction jobs with
    | nil =>
      simp [cost,code,ProtocolRAM.program,DescentStaticWordColumn.names_scan,Expr.work]
    | cons j js ih=>
      have a:=t.time_bound (l.slot floor j.val) j;have b:=t.names_bound w (l.slot floor j.val) j
      have u:=ih.1;have v:=ih.2
      simp only [cost,code,DescentStaticWordColumn.names_seq,List.length_cons,Nat.succ_mul];omega
  simpa only [ticks,program,List.length_finRange,Layout.clockBudget,Layout.hardwareBudget] using bound (List.finRange l.jobs)

end Banks
end
end Hierarchy.DescentDatedPriorOperand

end OAI
