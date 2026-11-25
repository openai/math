import OAI.Hierarchy.CheapISAMachine
import OAI.Hierarchy.CheapISAHostClock

namespace OAI
/-! # Native entry and bounded simulation on the actual 72-label instruction machine -/
namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ThreeFlat.RAM
open scoped Fin.CommRing
open DescentTerminalSimulatedClock
noncomputable section
variable {w p r k : ℕ} (M : Machine w p r k)
set_option quotPrecheck false
local notation "U" => machine w p r M.entry

theorem boot_run (st : Word w) (m : Memory w) (n : Memory (width w))
    (mounted : Banks (ROM M) (fun _ : Fin r=>0) m n) :
    ∃d,advance (U).program 1 ((U).program.start (wide st)) n=some (d,n) ∧
      Rel M (M.program.start st) m d n := by
  let d:=((U).program.start (wide st)).put 1 0 (M.entry.val:Word (width w))
  refine ⟨d,?_,?_,?_,?_,?_⟩
  · rfl
  · rfl
  · simp [d,Config.put,Machine.program]
  · rfl
  · exact mounted

theorem clock_of_steps {A : Type*} {S sourceFuel : ℕ} (st : Word w)
    (header : A→ℕ→ Word w) (out : A→ Memory w)
    (micro : Steps M.program (U).program (Rel M) 0 64)
    (ret : ∀c m d n,Rel M c m d n→∀ans,M.program.step c=.finish ans→
      ∃u last,u ≤ 64 ∧ advance (U).program u d n=some (last,n) ∧ (U).program.step last=.finish (ans.map wide))
    (source : ∀a,∃t cfg ans,t < sourceFuel ∧ advance M.program t (M.program.start st)
      (initialMemory S (header a))=some (cfg,out a) ∧ M.program.step cfg=.finish ans) :
    ∃image : A→ Memory (width w),
      (∀a,∃t cfg ans,t < hostFuel sourceFuel ∧ advance (U).program t ((U).program.start (wide st))
        (initialMemory (dataBase p r+S) (bankHeader r (ROM M) (header a)))=some (cfg,image a) ∧ (U).program.step cfg=.finish ans) ∧
      ∀a (i : Word w),image a (dataAddr p r i)=wide (out a i.val) :=
  host_clock M U (Rel M) (ROM M) st header out (fun _ mounted=>boot_run M st _ _ mounted)
    micro (fun _ _ _ _ h=>h.banks) ret source

end
end Hierarchy.CheapISA

end OAI
