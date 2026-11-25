import OAI.Optimization.LinearProgramming.BitRAM.FragmentControl
import OAI.Optimization.LinearProgramming.BitRAM.DispatchFrame

/-! Reentrant bit control with the numerical callback cache in the high even address bank. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch
open RAM RAM.Tape RAM.Callable OracleSpec

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The same fixed controller retains the scalar bank, native headers and high even address
registers between calls. This permits a numerical service to cache its grid and symbolic flags. -/
theorem fragWithCallback_run_frame {p : BitProgram} {bo : WordOracle} {P : K → Prop}
    {ctx : Transcript → Memory K → Prop} {allowed : p.Config → Fin p.states → Prop}
    {callback : Fragment} {factor : Nat} (oracle : FragCallbackCorrect p bo P ctx allowed callback factor)
    (keeps : ∀ (h : Transcript) (m t : Memory K), t.data = m.data → StableHeaders m t → StableEven m t →
      ctx h m → ctx h t)
    {c d : p.Config} {cost : Nat} (source : p.Run bo c cost d) (halted : d.pc = none)
    (permit : PermittedAsksFrom p bo allowed c) {m : Memory K}
    (rep : Rep p c m) (safe : Good P m) (env : ctx c.transcript m) :
    ∃ t, (fragController p callback).Run P m ((2*p.states+32+factor)*cost+2) t ∧
      Rep p d t ∧ ctx d.transcript t := by
  apply fragWithCallback_run_ctx oracle _ _ source halted permit rep safe env
  · intro s q a pc r ok cache
    obtain ⟨t,j,hj,run,issue,data,headers,even⟩ := issuedTable_complete_frame pc r ok
    exact ⟨t,j,hj,run,issue,keeps s.transcript a t data headers even cache⟩
  · intro h a cache
    apply keeps h a (a.putIndex limitReg p.states) rfl _ _ cache
    · intro i low _
      exact Memory.putIndex_ne _ (by unfold limitReg; omega) _
    · intro i low _
      exact Memory.putIndex_ne _ (by unfold limitReg; omega) _

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI
