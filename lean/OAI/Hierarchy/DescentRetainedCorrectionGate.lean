import OAI.Hierarchy.DescentRetainedAssignedDigits
import OAI.Hierarchy.DescentPhysicalRetainedCableRows
import OAI.Hierarchy.DescentResetRetainedCableValue

namespace OAI
/-! A chronological cable adjustment and a retained literal never pay for the same numeric field. -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup DescentResetRetainedSetup DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (C : DescentResetOperandSetup.Chart)
local notation "r" => C.retained
variable (hostEq : C.placement.oldHosts=C.retained.hosts) (groupEq : C.placement.groups*C.placement.blocks=C.retained.grouped)
    (which : C.seven.control.Targets) (packet : C.seven.Packets) (strips : C.retained.Strips)

variable {u : ℕ} (keep : Fin C.placement.shapes→Bool) (name : Fin u→Fin C.placement.sparse)
variable (x : Fin C.placement.blocks) (arg : Fin C.retained.args) (n : Fin C.retained.nodes)
variable (h : Fin C.placement.newHosts) (g : Fin C.placement.groups)
local notation "Y" => C.assignedDigits hostEq groupEq which packet strips
local notation "carriedWord[" t "," f "]" => DescentRetainedTargetPlacement.Chart.compact C.placement C.seven.batch keep name
  (Y) ((r).outputID t f arg n) x h g

/-- Filtering chooses the same old strip in the tag and each of its scalar fields. -/
theorem assigned_cable_zero (field : Fin 7) (small : field.val<4)
    (bits : 2<2^C.fieldBits) (tag : (((carriedWord[0,0]).val:Cell C.fieldBits)).val=1) :
    ((carriedWord[1,field]).val:Cell C.fieldBits)=0 :=by
  by_cases hv:h.val<u
  · let who:=name ⟨h.val,hv⟩
    by_cases live:keep (C.placement.shape who)=true
    · let j:=C.placement.shape who
      let row:=(r).site (C.seven.stripes which packet strips j)
        ((C.placement.previous who).cast hostEq) ((finProdFinEquiv (g,x)).cast groupEq)
      have atWord (t : Fin 2) (f : Fin 7) : carriedWord[t,f]=(r).decodeDigit row t f arg n:=by
        let out := (r).outputID t f arg n
        have read : carriedWord[t,f] = (Y) (finProdFinEquiv (out,j))
            (C.placement.previous who) (finProdFinEquiv (g,x)) := by
          simp [DescentRetainedTargetPlacement.Chart.compact,DescentResetDenseOperand.dense,hv,
            DescentRetainedTargetPlacement.Chart.selected,who,j,out,
            show keep (C.placement.shape (name ⟨h.val,hv⟩))=true from live]
          rfl
        rw [read]
        unfold assignedDigits
        rw [Equiv.symm_apply_apply]
        change C.seven.decoded which packet strips ((r).outputID t f arg n) j
          ((C.placement.previous who).cast hostEq) ((finProdFinEquiv (g,x)).cast groupEq) = _
        simp only [DescentRetainedSeven.Chart.decoded, Layout.outputID, Layout.function]
        repeat' (erw [Equiv.symm_apply_apply]; dsimp only)
        rfl
      rw [atWord,show (r).decodeDigit row 0 0 arg n=(r).rawField row n.val arg.val 0 by simp [Layout.decodeDigit]] at tag
      have zero_:((r).rawField row n.val arg.val 0).val≠0:=by
        intro q;rw [q] at tag;simp at tag
      have two:((r).rawField row n.val arg.val 0).val≠2:=by
        intro q
        simp only [Fin.val_natCast,q,Nat.mod_eq_of_lt bits] at tag
        omega
      rw [atWord]
      simp [Layout.decodeDigit,show ¬4≤field.val by omega,zero_,two]
    · have off:keep (C.placement.shape who)=false:=by cases a:keep (C.placement.shape who) <;>simp_all
      simp [DescentRetainedTargetPlacement.Chart.compact,DescentResetDenseOperand.dense,hv,
        DescentRetainedTargetPlacement.Chart.selected,show keep (C.placement.shape (name ⟨h.val,hv⟩))=false from off]
  · simp [DescentRetainedTargetPlacement.Chart.compact,DescentResetDenseOperand.dense,hv]

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
