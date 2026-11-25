import OAI.Optimization.LinearProgramming.Recovery.WitnessProgramBodyCode
import OAI.Optimization.LinearProgramming.Recovery.WitnessProgramInput
import OAI.Optimization.LinearProgramming.Recovery.MaskedProgram
import OAI.Optimization.LinearProgramming.Recovery.WitnessSolve
import OAI.Optimization.LinearProgramming.Recovery.WitnessTable

/-! Read the support packet, form the marked equations, run the normal rectangular
solver, and publish the vector into the ordinary scalar prefix. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessProgram

open RAM RAM.Callable
open OAI.Optimization.LinearProgramming.Geometry

private def blank : Memory ℚ := (start [] ([] : List ℚ)).memory

private theorem blankFoot : Footprint 0 (blank.atPC 0) :=
  ⟨fun _ => le_rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem body_run {h n : ℕ} (E : Matrix (Fin h) (Fin n) ℚ) (S : Finset (Fin n))
    (hn : 0<n) (e : ℕ) (three : 3≤e) (entries : ∀ i j, ratBits (E i j) ≤ e)
    (w : Fin n → ℚ) (answer : Elimination.fixedSolve (system E S hn) (rhs h n) = some w) :
    ∃ out, body.Run (fun q => ratBits q ≤ WitnessSolve.heightPolynomial.eval (h+n+e))
        (Odd.memory (start [] ([] : List ℚ)).memory (start [h,n] (MaskedInput.bundle E S)).memory)
        (bodyTime h n) out ∧ ∀ j : Fin n, out.data j.val = w j := by
  let C := maskedEquations E S
  let M := WitnessSolve.heightPolynomial.eval (h+n+e)
  let P := fun q : ℚ => ratBits q ≤ M
  let dst := WitnessTable.destination h n
  let cap := WitnessTable.capacity h n
  have low : e ≤ M := WitnessSolve.old_height_le h n e
  have threeM : 3 ≤ M := three.trans low
  have blankSafe : blank.AllData P := fun _ => threeM
  have inputSafe (i : ℕ) : P ((MaskedInput.bundle E S)[i]?.getD 0) :=
    (MaskedInput.bundle_height E S e three entries i).trans low
  obtain ⟨v,cv,hcv,prepared,regs,read⟩ := MaskedInput.program_run E S P threeM threeM inputSafe
  obtain ⟨t,ct,hct,written,raw,dstAt,lenAt⟩ := WitnessTable.program_run C hn P
    v prepared.safe_end threeM threeM regs read
  have fit : 0 < cap := by unfold cap WitnessTable.capacity; omega
  have size : (n+1)*(h+n+1) ≤ cap := by unfold cap WitnessTable.capacity WitnessTable.words; omega
  have dims : 2 ≤ cap := by unfold cap WitnessTable.capacity; omega
  have dstHigh : 5 ≤ dst := by unfold dst WitnessTable.destination WitnessTable.tableBase; omega
  have dstRoom : n ≤ Odd.slot dst := by unfold dst WitnessTable.destination WitnessTable.tableBase Odd.slot; omega
  obtain ⟨native,caller,solved,ns,cs,coords,indices,_,_⟩ := WitnessSolve.program_run
    (system E S hn) (rhs h n) blank t (WitnessTable.tableBase h n) 208 cap 0 dst M
    raw blankFoot fit size dims blankSafe written.safe_end threeM
    (solver_height E S hn e three entries) dstAt lenAt dstHigh w answer
  obtain ⟨out,published,values,_,_⟩ := Publish.fromOdd_spec 0 n dst native caller w P ns cs
    hn dstRoom ((indices 210 (by decide)).trans dstAt) ((indices 211 (by decide)).trans lenAt) coords
  have begin := Odd.leaf_run P blank blankSafe prepared
  have tabulate := Odd.leaf_run P blank blankSafe written
  refine ⟨out,(begin.seq (tabulate.seq (solved.seq (Fragment.Run.ofBlock published)))).mono ?_,values⟩
  unfold bodyTime
  dsimp only [cap]
  omega

end WitnessProgram
end Recovery
end LinearProgramming
end Optimization
end OAI
