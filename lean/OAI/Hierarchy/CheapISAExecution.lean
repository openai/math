import OAI.Hierarchy.CheapISATranslatedClock
import OAI.Hierarchy.CheapISAStep

namespace OAI
/-! # The fixed instruction interpreter reaches the shifted outputs for every original header -/
namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
variable {w p r k : ℕ} (M : Machine w p r k)
set_option quotPrecheck false
local notation "U" => machine w p r M.entry

theorem translated_clock {A : Type*} {S sourceFuel : ℕ} (st : Word w)
    (header : A→ℕ→ Word w) (out : A→ Memory w)
    (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1)) (cheap : ∀i,TaggedShorterCheapCPU.Cheap (M.code i))
    (source : ∀a,∃t cfg ans,t < sourceFuel ∧ advance M.program t (M.program.start st)
      (initialMemory S (header a))=some (cfg,out a) ∧ M.program.step cfg=.finish ans) :
    ∃image : A→ Memory (width w),
      (∀a,∃t cfg ans,t < hostFuel sourceFuel ∧ advance (U).program t ((U).program.start (wide st))
        (initialMemory (dataBase p r+S) (bankHeader r (ROM M) (header a)))=some (cfg,image a) ∧ (U).program.step cfg=.finish ans) ∧
      ∀a (i : Word w),image a (dataAddr p r i)=wide (out a i.val) :=
  clock_of_steps M st header out (step M hp hr cheap) (halt M hp hr) source

end
end Hierarchy.CheapISA

end OAI
