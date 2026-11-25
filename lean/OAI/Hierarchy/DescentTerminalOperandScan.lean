import OAI.Hierarchy.DescentTerminalBundleRows
import OAI.Hierarchy.DescentTerminalHeaderPrefixRAM

namespace OAI
/-! # Physical live-operand numbering in terminal birth order -/
namespace Hierarchy.DescentTerminalOperandScan
open DescentKernelHistory DescentTerminalBundleRows
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {Tag B : Type} (r : Recipe Tag B) (birth : r.Node ↪ ℕ)

abbrev Rows := ∑u,r.arity u
def allPositions := ProtocolRAMPortRanks.enumerate r.arity birth birth.injective
def live (i : Fin (Rows r)) : Bool :=
  let a:=(allPositions r birth).symm i
  (r.operand a.1 a.2).isLeft

def cursor (i : ℕ) := (Finset.univ.filter fun a : Public r=>raw r birth a < i).card

theorem cursor_zero : cursor r birth 0=0 := by simp [cursor]

theorem cursor_slot (a : Public r) : cursor r birth (raw r birth a)=(publicOrdinal r birth a).val := by
  rw [publicOrdinal_val]
  simp [cursor,raw_before]

theorem cursor_next (i : Fin (Rows r)) :
    cursor r birth (i.val+1)=cursor r birth i.val+(if live r birth i then 1 else 0) := by
  let z:=(allPositions r birth).symm i
  have index (a : Public r) : raw r birth a=i.val ↔ a.val=z := by
    change ((allPositions r birth) a.val).val=i.val ↔ _
    rw [←Fin.ext_iff,Equiv.eq_symm_apply]
  by_cases h : (r.operand z.1 z.2).isLeft=true
  · let a : Public r:=⟨z,h⟩
    have hit:= (index a).mpr rfl
    have seteq : (Finset.univ.filter fun b : Public r=>raw r birth b < i.val+1)=
        insert a (Finset.univ.filter fun b : Public r=>raw r birth b < i.val) := by
      ext b
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
      constructor
      · intro lt
        by_cases same : raw r birth b=i.val
        · exact Or.inl (Subtype.ext ((index b).mp same))
        · exact Or.inr (by omega)
      · rintro (rfl|prior) <;> omega
    have outside : a ∉ Finset.univ.filter (fun b : Public r=>raw r birth b < i.val) := by simp [hit]
    change _=_+(if (r.operand z.1 z.2).isLeft then 1 else 0)
    simp only [cursor,seteq,Finset.card_insert_of_notMem outside,ite_eq_left h]
  · have seteq : (Finset.univ.filter fun b : Public r=>raw r birth b < i.val+1)=
        Finset.univ.filter fun b : Public r=>raw r birth b < i.val := by
      ext b
      have absent : raw r birth b≠i.val := by
        intro eqn
        have eqz := (index b).mp eqn
        exact h (eqz ▸ b.property)
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      omega
    change _=_+(if (r.operand z.1 z.2).isLeft then 1 else 0)
    simp only [cursor,seteq,ite_eq_right h,Nat.add_zero]

theorem raw_live (a : Public r) : live r birth (allPositions r birth a.val)=true := by
  unfold live
  rw [(allPositions r birth).symm_apply_apply a.val]
  exact a.property

def select (bank : Bank) : Expr := .lookup bank .row
def program (bits out : ℕ) (bank : Bank) :=
  DescentTerminalHeaderPrefixRAM.program bits out (Rows r) .add (select bank)

theorem cheap (bits out : ℕ) (b : Bank) : CheapCode (program r bits out b) :=
  @DescentTerminalHeaderPrefixRAM.cheap bits out (Rows r) .add (select b)

def state (bits : ℕ) (i : ℕ) : Computability.VPVNP.BurstRAM.Word bits := (cursor r birth i : ℕ)

abbrev finish {bits : ℕ} (out : ℕ) (m : Memory bits) :=
  fillSegment out (Rows r) (DescentTerminalHeaderPrefixRAM.file out (state r birth bits)) m

/-- The old resident flag bank is indexed by actual chronological operand,
and the only new cells are the inclusive prefix words. -/
theorem run {bits out : ℕ} (b : Bank) (m : Memory bits) (fit : (select b).Fits bits out)
    (room : out+Rows r<2^bits)
    (mounted : ∀i : Fin (Rows r),b.read m (i.val:Computability.VPVNP.BurstRAM.Word bits)=((if live r birth i then 1 else 0 : ℕ):Computability.VPVNP.BurstRAM.Word bits)) :
    (program r bits out b).Exec m (finish r birth out m)
      (4+Rows r*32) := by
  change (program r bits out b).Exec m (finish r birth out m)
    (4+Rows r*(2*DescentTerminalHeaderPrefixRAM.work .add (select b)+4))
  apply DescentTerminalHeaderPrefixRAM.spec
  · trivial
  · exact fit
  · exact room
  · simp [state,cursor_zero]
  · intro i
    change ((cursor r birth i.val:ℕ):Computability.VPVNP.BurstRAM.Word bits)+b.read m (i.val:Computability.VPVNP.BurstRAM.Word bits)=((cursor r birth (i.val+1):ℕ):Computability.VPVNP.BurstRAM.Word bits)
    rw [mounted,cursor_next,Nat.cast_add]

/-- A live physical row publishes the exclusive public operand number after
one decrement. Hidden-only rows only advance the input cursor. -/
theorem published {bits out : ℕ} (m : Memory bits) (a : Public r) :
    finish r birth out m (out+raw r birth a)-1=((publicOrdinal r birth a).val:Computability.VPVNP.BurstRAM.Word bits) := by
  let i:=allPositions r birth a.val
  have step:=cursor_next r birth i
  rw [raw_live r birth a] at step
  have row:=DescentTerminalHeaderPrefixRAM.at_row out (state r birth bits) m i
  change finish r birth out m (out+i.val)-1=((publicOrdinal r birth a).val:Computability.VPVNP.BurstRAM.Word bits)
  unfold finish
  rw [row]
  change ((cursor r birth (i.val+1):ℕ):Computability.VPVNP.BurstRAM.Word bits)-1=_
  rw [step,ite_eq_left rfl,Nat.cast_add]
  change ((cursor r birth (raw r birth a):ℕ):Computability.VPVNP.BurstRAM.Word bits)+1-1=_
  rw [cursor_slot]
  abel

end
end Hierarchy.DescentTerminalOperandScan

end OAI
