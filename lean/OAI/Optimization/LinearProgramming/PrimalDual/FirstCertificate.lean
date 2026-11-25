import OAI.Optimization.LinearProgramming.PrimalDual.BridgeLayout
import OAI.Optimization.LinearProgramming.PrimalDual.Gather
import OAI.Optimization.LinearProgramming.PrimalDual.CompactDecoder

/-! Return directly from an infeasible first call using its actual even-register
certificate. No joint system is constructed along this path. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace Bridge

open RAM RAM.Block RAM.Tape Polynomial

noncomputable def returnBudget : Polynomial Nat := termBudget returnTerms + 300*(X+1)

private def certLow : List CursorBind := [.reg 0 41,.reg 1 44]

def firstCertificate : Block :=
  .seq (returnHeader 9 11) (.seq (gather 2 40 44 41) (.seq (CursorBind.script certLow) compactInfeasible))

theorem firstCertificate_correct {m d H : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c : Fin d → ℚ) (first : State ℚ) (cert : Certificate A b (readVector first 0 m))
    (s : Memory ℚ) (safe : Good (fun q => ratBits q ≤ H) s)
    (hm : s.index 9=m) (hd : s.index 11=d) (even : ∀ i, s.data (2*i)=first.data i) :
    ∃ t k, Eval (Good (fun q => ratBits q ≤ H)) firstCertificate s k t ∧
      k ≤ returnBudget.eval (m+d) ∧ OptimizationOutput A b c {t.atPC 0 with output := some 0} := by
  obtain ⟨u,j,e1,hj,ud,r⟩ := returnHeader_correct s safe 9 11 m d (by decide) (by decide) hm hd
  let R := returnBase m d
  have high : 2*m+4 ≤ R := by dsimp [R,returnBase]; omega
  obtain ⟨v,e2,words,_,ids⟩ := gather_correct 2 40 44 41 0 R m u e1.safe_end (by decide)
    (by decide) (by decide) r.even r.buffer r.mreg (by decide) (by omega) (by omega) (by omega)
  let w := CursorBind.install certLow v
  have init := CursorBind.run certLow v e2.safe_end
  have vm := (ids 41 (by decide)).trans r.mreg
  have vr := (ids 44 (by decide)).trans r.buffer
  have w0 : w.index 0=m := by simp [w,certLow,CursorBind.install,CursorBind.apply,vm]
  have w1 : w.index 1=R := by simp [w,certLow,CursorBind.install,CursorBind.apply,vr,R]
  have atW : Holds w R (readVector first 0 m) := by
    intro i
    have eq := (words i.val i.isLt).trans ((congrFun ud _).trans (by simpa using even i.val))
    change v.data (R+i.val) = first.data (0+i.val)
    simpa only [Nat.zero_add] using eq
  obtain ⟨t,k,e3,hk,hout⟩ := compactInfeasible_correct A b c w R init.safe_end
    w0 w1 (by omega) (by omega) first cert atW
  refine ⟨t,_,e1.seq (e2.seq (init.seq e3)),?_,hout⟩
  change j+(m*(2+6)+5+(2+k)) ≤ _
  have hR (n : Nat) : returnBudget.eval n=(termBudget returnTerms).eval n+300*(n+1) := by
    simp [returnBudget]
  rw [hR]
  omega

end Bridge
end PrimalDual
end LinearProgramming
end Optimization
end OAI
