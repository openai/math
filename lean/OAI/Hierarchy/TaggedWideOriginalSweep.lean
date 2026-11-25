import OAI.Hierarchy.TaggedWidePageSweep

namespace OAI
/-! # Original physical role snapshots, width masks and both final socket pages -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
variable {T W : ℕ} (g : Dated T) (rom work : ℕ)
local notation "two" => Fin.cases (motive := fun _ : Fin 2 => Scatter) (g.widthPage rom work) (fun _ : Fin 1 => g.slotPage work false)
variable (R : ∀t f,PageResult W (g.rolePage rom work t f))
    (widths : PageResult W (g.widthPage rom work)) (slots : ∀b,PageResult W (g.slotPage work b))

def Dated.originalReports : ∀i,PageResult W (g.sheets rom work i) :=
  PageResult.pair (PageResult.pair
    (PageResult.pair (fun i=>let jf : Fin (T+1)×Fin 3:=finProdFinEquiv.symm i;R jf.1 jf.2)
      (PageResult.pair (fun j=>PageResult.skip (g.ballotPage rom work j)) (fun j=>PageResult.skip (g.controlPage rom work j))))
    (Fin.cases (motive := fun i : Fin 2 => PageResult W (two i)) widths (fun _ => slots false)))
    (fun _ : Fin 1=>slots true)

/-- The first physical batch preserves all role fields, both slot memories
and the zeroed positive width slice. The later correction program supplies
the signed ballot/gather fields used in the retained tensor. -/
theorem Dated.original_run (m : Memory W)
    (rolesDone : ∀t f,(R t f).Issued work m)
    (ballot : ∀j,(PageResult.skip (g.ballotPage rom work j)).Issued work m)
    (control : ∀j,(PageResult.skip (g.controlPage rom work j)).Issued work m)
    (widthDone : widths.Issued work m) (slotDone : ∀b,(slots b).Issued work m) :
    ∃out,(ProcedureBank.program (Dated.last T) (fun i=>(g.sheets rom work i).code W)).Exec m out
      (∑i,(g.sheets rom work i).ticks) ∧ (∀t f,(R t f).holds out) ∧ widths.holds out ∧
      (∀b,(slots b).holds out) ∧ ∀a,a<work→ out a=m a := by
  let get:=g.originalReports rom work R widths slots
  have issued : ∀i,(get i).Issued work m := by
    refine PageResult.pair_issued _ _ (PageResult.pair_issued _ _ (PageResult.pair_issued _ _ ?_ ?_) ?_) ?_
    · intro i;exact rolesDone _ _
    · exact PageResult.pair_issued _ _ ballot control
    · intro i;induction i using Fin.cases with
      | zero=>exact widthDone
      | succ i=>exact slotDone false
    · intro _;exact slotDone true
  obtain ⟨out,exec,state,frame⟩:=PageResult.exec (g.ordered rom work) get issued
  have parts {a b} {p : Fin a→Scatter} {q : Fin b→Scatter}
      (l : ∀i,PageResult W (p i)) (r : ∀j,PageResult W (q j))
      (all : ∀k,(PageResult.pair l r k).holds out) :
      (∀i,(l i).holds out) ∧ ∀j,(r j).holds out := by
    exact ⟨fun i=>by simpa [PageResult.pair] using all (Fin.castAdd b i),
      fun j=>by simpa [PageResult.pair] using all (Fin.natAdd a j)⟩
  have split:=parts _ _ state
  have mid:=parts _ _ split.1
  have role:= (parts _ _ mid.1).1
  refine ⟨out,exec,?_,mid.2 0,?_,frame⟩
  · intro t f
    let i : Fin ((T+1)*3) := finProdFinEquiv (t,f)
    have pair : finProdFinEquiv.symm i = (t,f) := finProdFinEquiv.symm_apply_apply (t,f)
    have held := role i
    change (R (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).holds out at held
    rw [pair] at held
    exact held
  · intro b;cases b with
    | false => exact mid.2 1
    | true => exact split.2 0

end Hierarchy.ProtocolRAM.Calendar.WideCPU
end

end OAI
