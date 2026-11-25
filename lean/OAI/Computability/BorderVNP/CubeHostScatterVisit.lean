import OAI.Computability.BorderVNP.CubeHostScatterEnd

/-! # Visiting both physical endpoints of one crossing cable in public row order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Both physical endpoint visits, followed by advancing the public cable cursor. -/
def rowStep : Code := .seq (visit false) (.seq (visit true) (.binary .add 13 13 1))

/-- Fixed metadata budget of a two-sided row visit. -/
def rowOverhead := visitOverhead false + visitOverhead true + 1

/-- Upper clock for a single cable, charging a bit copy only at its owned live endpoints. -/
def rowTicks (l : Layout) (m : ℕ → ℕ) (i : ℕ) :=
  rowOverhead + (l.bits m i false + l.bits m i true)*(scatterStep.slots+1)

/-- Execute both ends of one real cable. All setup registers and future input words survive;
only the cable's actual external intervals on this team receive their decoded source bits. -/
theorem run_rowStep {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) {i : ℕ} (hi : i < l.count)
    (s : Bank w) (m : Memory w) (ready : l.Ready (.ofWords s m)) (idx : (s 13).val = i)
    (frozen : l.Frozen before (readings m)) :
    BoundedRun pub macros rowStep s m (rowTicks l before i) (fun z => l.Ready z ∧ z.reg 13 = i+1 ∧
      z.mem = l.copyEnd before (l.copyEnd before (readings m) i false) i true) := by
  let result := l.copyEnd before (l.copyEnd before (readings m) i false) i true
  have end1 := run_visit pub macros l before fit hi false s m ready idx frozen
  have both := end1.seq (b := .seq (visit true) (.binary .add 13 13 1))
    (t := visitOverhead true+l.bits before i true*(scatterStep.slots+1)+1)
    (Q := fun z => l.Ready z ∧ z.reg 13 = i+1 ∧ z.mem = result) (fun u mu h1 => by
      have hm : readings mu = l.copyEnd before (readings m) i false := h1.2.2
      have fr := frozen.copyEnd fit hi false
      apply (run_visit pub macros l before fit hi true u mu h1.1 h1.2.1 (hm.symm ▸ fr)).seq
      intro v mv h2
      have r1 : (v 1).val = 1 := h2.1 1 (by decide)
      have r13 : (v 13).val = i := h2.2.1
      have inc : i+1 < 2^w := by have := fit.countFit; omega
      have c := (Code.binary .add 13 13 1).runFixed pub macros v mv (by
        simpa only [Code.fixedSafe,Code.safeReadOnly,NatState.ofWords,readings,r1,r13,addressOpFits] using inc)
      apply c.mono le_rfl
      rintro _ rfl
      refine ⟨?_,?_,?_⟩
      · intro j hj
        have hj' : j ≠ 13 := by intro he; subst j; norm_num at hj
        simpa only [Code.fixedEval,Code.evalNat,Function.update_of_ne hj'] using h2.1 j hj
      · simp (config := {decide := true}) [Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,readings,r13,r1]
      · exact h2.2.2.trans (congrArg (fun mem => l.copyEnd before mem i true) hm))
  apply both.mono _ fun _ => id
  dsimp [rowTicks,rowOverhead]
  rw [Nat.add_mul]
  omega

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
