import OAI.Hierarchy.FactorCompiledOwners
import OAI.Hierarchy.FactorCompilerBudget

namespace OAI
/-! # Native assignment contract used by the receiver and the verifier -/

namespace Hierarchy.FactorBucketRAM
open Computability.VPVNP.BurstRAM ThreeFlat.RAM.PhysicalProcedure
open FactorAllocation
open scoped Fin.CommRing

/-- Starting with the published resource rows and the width-only public threshold
table, the installed fixed program computes both factor banks. Every address outside
its four mutable tables, including the original admitted archive, is preserved. -/
theorem assignment_compiler {w width N d T : ℕ} (ht : 0<T) (hd : 0<d)
    (b : Banks) (bounds : BankBounds b w width N d) (cost : Fin N → Fin d → ℕ)
    (smallS : 20*(w+1)+1<2^width) (smallD : d<2^width) (smallT : T<2^width)
    (smallScan : N*d*(20*(w+1)+1)<2^width) (smallRows : N*d<2^width)
    (smallClasses : (20*(w+1)+2)^d<2^width) (smallN : N<2^width) :
    (compiler width w N d T b).Spec
      (fun m => (∀ (i : Fin N) (j : Fin d), (m (b.resources+(i.val*d+j.val))).val=cost i j) ∧
        ∀ j≤20*(w+1), (m (b.thresholds+j)).val=FactorBucket.threshold j)
      (fun m out => (∀ a, untouched b w N d a → out a=m a) ∧
        ∀ i : Fin N, out (b.keys+i.val) = (classIndex (key w cost i):Word width) ∧
          out (b.output+i.val) = ((owner ht w cost i).val:Word width))
      (ticks w N d) := by
  intro P R K M pc reg pub exit installed data c m entry pre
  obtain ⟨n,hn,out,mem,run,atExit,eq⟩ :=
    compiler_computes width w N d T b smallScan smallRows smallClasses smallN
      M pc reg pub exit installed data c m entry trivial
  subst mem
  exact ⟨n,hn,out,_,run,atExit,compiled_state ht hd b bounds m cost smallS smallD smallT
    smallScan smallRows pre.1 pre.2⟩

end Hierarchy.FactorBucketRAM

end OAI
