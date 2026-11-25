import OAI.Hierarchy.DescentPhysicalPreviousFieldFrame
import OAI.Hierarchy.DescentPhysicalResetDateOutput

namespace OAI
/-! The signed successor rows from the dated rank scan survive the operand book
and the funded final reset writes, at both endpoints and on padded lanes. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentNextSignedWindow DescentDyadicSpan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {a:PhysicalReset} {floor w:ℕ} (u:a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "head" => (v).linkedRankInputs u.sectors ((v).sheetsStart b)
local notation "book" => (v).rankBook head b
local notation "r₀" => (v).renderFromRanks head b
local notation "page" => Native.All.page ((v).fieldsEnd b) (A).blocks (A).capacity (A).signedBits (A).lanes (A).hosts (A).groups
local notation "N" => (A).hosts*chunks (A).groups (A).lanes
local notation "ranked" m:arg => (book).memory (((v).rankPortPhase b w).image m)
local notation "rendered" ok₀:arg actors:arg => (v).renderMemory r₀ b u.degree (ranked (u.candidateEntry ok₀ actors))

theorem DateInputs.rendered_page (x:Fin (A).blocks) (j:Fin (2*(A).capacity)) :
    (FinalInputs.predecessor u).signed x.val j.val=page x j :=by
  apply congrArg (fun base:ℕ=>(⟨base,Nat.clog 2 N⟩:Bank))
  rw [finProdFinEquiv_apply_val]
  ring

theorem DateInputs.rendered_page_room (x:Fin (A).blocks) (j:Fin (2*(A).capacity)) :
    (page x j).base+(page x j).size≤(v).controlFloor b:=by
  let t:=DescentDyadicSpan.span N
  let u₀:=Native.All.outputBase ((v).fieldsEnd b) (A).capacity (A).signedBits (A).lanes
  change u₀+(finProdFinEquiv (x,j)).val*t+t≤u₀+((A).blocks*(2*(A).capacity))*t
  rw [Nat.add_assoc,←Nat.succ_mul]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right t (Nat.succ_le_of_lt (finProdFinEquiv (x,j)).isLt)) u₀

private theorem render_le_start : (v).controlFloor b≤(v).operandStart b:=by
  have left:=((v).control_address_bounds b).2.2.1
  have setup:(v).operandFloor b≤(v).keepBase b:=by
    change _≤(v).setup.endAddress ((v).operandFloor b)
    rw [(v).setup.affine]
    exact Nat.le_add_right ..
  exact left.trans (setup.trans (Nat.le_add_right ..))

theorem DateInputs.rendered_to_final_area (x:Fin (A).blocks) (j:Fin (2*(A).capacity)) :
    ((FinalInputs.predecessor u).signed x.val j.val).base+((FinalInputs.predecessor u).signed x.val j.val).size≤(v).finalEnd b:=by
  rw [u.rendered_page x j]
  exact (DateInputs.rendered_page_room (a:=a) (floor:=floor) x j).trans ((render_le_start (a:=a) (floor:=floor)).trans
    (((v).operand_order b).1.trans (((v).operand_order b).2.trans ((v).final_ge b))))

theorem DateInputs.sheets_render_frame (ok:u.Ready) (actors:Memory w) (i:ℕ) (before:i<(v).controlFloor b) :
    u.sheetsResult ok actors i=(rendered ok actors) i:=by
  let dest:=u.operandEntry ok actors
  let old:=(v).operandDictionaryEnd b
  let last:=(v).operandMemory u.operand r₀ b dest
  have scalar:=(v).operand_any u.operand r₀ b dest ok.fields (((v).final_ge b).trans_lt ok.full)
  have slots:(A).fields=(v).nodeNames*(v).nodes:=by
    simpa only [ok.nodes,ok.slots,ResetOutput.nodeNames] using u.operand.channels
  have room:old+((v).nodeNames*(v).nodes)*DescentResetNodeBooks.rows (A).hosts (A).groups (A).lanes≤(v).scalarEnd b:=by
    change old+_≤old+(A).fields*_
    rw [slots]
    rfl
  have output:=DescentResetNodeBooks.any ((v).scalarEnd b) old (v).nodeNames (v).nodes
    (A).hosts (A).groups (v).nodeBits (A).lanes last room ok.full
  have atStart:=before.trans_le (render_le_start (a:=a) (floor:=floor))
  have atEnd:=atStart.trans_le (((v).operand_order b).1.trans ((v).operand_order b).2)
  exact (output.2 i (.inl atEnd)).trans ((scalar.2.1 i (.inl atStart)).trans (u.operand_render_frame ok actors i before))

/-- This is the signed-input hypothesis of the recorded successor at the real sheets return. -/
theorem DateInputs.signed_at_sheets (ok:u.Ready) (actors:Memory w) (x:Fin (A).blocks) (j:Fin (2*(A).capacity))
    {s:ℕ} (values:Fin (A).hosts→Fin (A).groups→Cell s)
    (read:Reads (page x j) values (A).lanes (rendered ok actors)) :
    Reads ((FinalInputs.predecessor u).signed x.val j.val) values (A).lanes (u.sheetsResult ok actors):=by
  rw [u.rendered_page x j]
  intro lane
  have limit:(row (A).hosts (A).groups (A).lanes lane).val<(page x j).size:=
    (row _ _ _ lane).isLt.trans_le (DescentDyadicSpan.span_ge _)
  exact (u.sheets_render_frame ok actors _ ((Nat.add_lt_add_left limit _).trans_le (DateInputs.rendered_page_room (a:=a) (floor:=floor) x j))).trans (read lane)

variable {u} (z:u.FinalInputs)
theorem signed_at_date (ok:u.Ready) (room:z.Room) (actors:Memory w) {m out:Memory w}
    (mid:u.throughOperandDate.Runs m (u.sheetsResult ok actors)) (full:(date z).Runs m out)
    (x:Fin (A).blocks) (j:Fin (2*(A).capacity)) {s:ℕ} (values:Fin (A).hosts→Fin (A).groups→Cell s)
    (read:Reads (page x j) values (A).lanes (rendered ok actors)) :
    Reads ((FinalInputs.predecessor u).signed x.val j.val) values (A).lanes out:=by
  have seen:=u.signed_at_sheets ok actors x j values read
  rw [date_image z room full mid]
  intro lane
  have limit:(row (A).hosts (A).groups (A).lanes lane).val<((FinalInputs.predecessor u).signed x.val j.val).size:=by
    rw [u.rendered_page]
    exact (row _ _ _ lane).isLt.trans_le (DescentDyadicSpan.span_ge _)
  exact ((z.tail_result room _).2.2.1 _ (.inl ((Nat.add_lt_add_left limit _).trans_le
    (u.rendered_to_final_area x j)))).trans (seen lane)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
