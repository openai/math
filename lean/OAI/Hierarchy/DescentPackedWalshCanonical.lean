import OAI.Hierarchy.DescentPackedWalshWeightedSeed
import OAI.Hierarchy.DescentPackedWalshTotalColumn
import OAI.Hierarchy.DescentMeasuredRectangle
import OAI.Hierarchy.DescentCanonicalTrajectory

namespace OAI
/-! # The physical reset uses the canonical matrix of the actual two families of counts -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentGL DescentIntegerScale DescentMeasuredWeights DescentWeightColumnRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {A C : Type} [Fintype A] [Fintype C] {u l N g w base B q : ℕ}
local notation "k" => u+l

theorem original_weights (levels : A→ℕ) (loc : Item levels C↪Fin N)
    (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ) (x : A→Bits k→ℕ) (y : C→Bits k→ℕ)
    (f full K : ℕ) (gainBits : ∀i,padded loc (gain levels f full K) 0 i<2^g)
    (v : Fin (k+1)) (d : Fin (2^k)) :
    (∑i,bill v.val (padded loc (level levels j cj) 0)
      (fun z=>(⟨_,gainBits z⟩:Cell g)) (padded loc (load levels x y) (fun _=>0)) i (centralOrder u l d))=
      mixingWeightNumerator levels j cj x y f full K v (DescentGLScoreRAM.vec d) := by
  simp only [bill,centralOrder,Equiv.symm_apply_apply]
  exact padded_money levels loc j cj x y f full K v (DescentGLScoreRAM.vec d)

/-- The published scalar banks are precisely the final outputs of the packed per-depth sums.
The matrix here is the same continuous-paper estimator's public first minimizer. -/
theorem issue_canonical (levels : A→ℕ) (loc : Item levels C↪Fin N)
    (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ) (x : A→Bits k→ℕ) (y : C→Bits k→ℕ)
    (f full K : ℕ) (gainBits : ∀i,padded loc (gain levels f full K) 0 i<2^g)
    (bank : ℕ→ℕ) (mem : Memory w) (room : PhysicalTrajectory.Room w k base bank)
    (positive : 0<q) (precision : 3*k+B+2≤w)
    (bound : ∀v d,mixingWeightNumerator levels j cj x y f full K v d≤2^B)
    (printed : ∀(v : Fin (k+1)) (d : Fin (2^k)),mem (bank v.val+d.val)=
      ((∑i,bill v.val (padded loc (level levels j cj) 0)
        (fun z=>(⟨_,gainBits z⟩:Cell g)) (padded loc (load levels x y) (fun _=>0)) i (centralOrder u l d)):Word w)) :
    let W:=mixingWeightNumerator levels j cj x y f full K
    let μ:=PhysicalTrajectory.canonicalTrajectory W q k
    let dst:=PhysicalTrajectory.finalMemory k base bank mem
    (PhysicalTrajectory.program w k base bank).Exec mem dst
        (PhysicalTrajectory.time k base bank k+DescentGLPermutationRAM.clock k) ∧
    (∀i : Fin k,dst (PhysicalTrajectory.pointer k base i.val)=((rowIndex k (rowFunctional μ i)).val:Word w)) ∧
    (∀i : Fin (2^k),dst (PhysicalTrajectory.outputBase k base+i.val)=
      ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm i))).val:Word w)) ∧ ∀z<base,dst z=mem z := by
  let W:=mixingWeightNumerator levels j cj x y f full K
  have weights (v : Fin (k+1)) (d : Fin (2^k)) : mem (bank v.val+d.val)=(W v (DescentGLScoreRAM.vec d):Word w) := by
    exact (printed v d).trans (by
      simpa only [Nat.cast_sum] using congrArg (fun total : ℕ => (total : Word w))
        (original_weights levels loc j cj x y f full K gainBits v d))
  refine ⟨?_,PhysicalTrajectory.receipt bank W (PhysicalTrajectory.canonicalTrajectory W q)
    (PhysicalTrajectory.canonicalTrajectory_chooses W q) mem room positive precision bound weights⟩
  intro pc regs ports machine
  exact PhysicalTrajectory.exec bank mem room machine

end
end Hierarchy.DescentPackedWalsh

end OAI
