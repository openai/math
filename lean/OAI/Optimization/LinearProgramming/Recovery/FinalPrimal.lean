import OAI.Optimization.LinearProgramming.Recovery.FinalPrimalCode
import OAI.Optimization.LinearProgramming.Recovery.PrimalTable
import OAI.Optimization.LinearProgramming.Recovery.WitnessSolve
import OAI.Optimization.LinearProgramming.Recovery.WitnessProgramInput
import OAI.Optimization.LinearProgramming.Recovery.PublishOdd

/-! The actual primal output branch assembles and solves the original inhomogeneous
system and publishes the result in the public registers starting at zero. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PrimalOutput
open RAM RAM.Callable Geometry Matrix PrimalDual
open scoped Matrix

def outputWidth (m d seed : ℕ) := seed+differenceWidth seed+WitnessSolve.solverHeight ((d+1)*m*differenceWidth seed)

theorem program_run {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ) (w : Fin (m+1)→ℚ)
    (native caller : Memory ℚ) (raw atW cap B limit : ℕ) (hp : 0 < m) (hd : 0 < d) (three : 3 ≤ B)
    (old : native.AllData (fun q=>ratBits q ≤ B)) (inside : caller.AllData (fun q=>ratBits q ≤ B))
    (foot : Footprint (cap-1) (native.atPC 0)) (two : 2 ≤ cap) (space : (d+1)*m ≤ cap)
    (stored : SlackRAM.InputAt caller raw A b) (values : ∀j : Fin (m+1),caller.data (atW+j.val)=w j)
    (high : 7 ≤ raw) (sep : raw+(m*d+m) ≤ atW) (bound : ∀j,caller.index j ≤ limit)
    (a : caller.index 24=raw) (r : caller.index 28=m) (c : caller.index 29=d) (hcap : caller.index 60=cap) (v : caller.index 212=atW)
    (x : Fin d→ℚ) (answer : Elimination.fixedSolve A (b-Fin.tail w)=some x) :
    ∃ z,program.Run (fun q=>ratBits q ≤ outputWidth m d B) (Odd.memory native caller) (programTime m d cap limit) z ∧
      (∀j : Fin d,z.data j.val=x j) ∧ z.index 16=0 ∧ z.index 17=0 := by
  let M:=outputWidth m d B
  have first : B ≤ M:=by dsimp [M,outputWidth];omega
  have diff : differenceWidth B ≤ M:=by dsimp [M,outputWidth];omega
  have nativeSafe : native.AllData (fun q=>ratBits q ≤ M):=fun j=>(old j).trans first
  have callerSafe : caller.AllData (fun q=>ratBits q ≤ M):=fun j=>(inside j).trans first
  have ha (i : Fin m) (j : Fin d) : ratBits (A i j) ≤ B:=by rw [←stored.1 i j];exact inside _
  have hb (i : Fin m) : ratBits (b i) ≤ B:=by rw [←stored.2 i];exact inside _
  have hw (i : Fin (m+1)) : ratBits (w i) ≤ B:=by rw [←values i];exact inside _
  have rhs (i : Fin m) : ratBits ((b-Fin.tail w) i) ≤ differenceWidth B := by
    change ratBits (b i-w i.succ) ≤ _
    have hbnd:=hb i
    have wbnd:=hw i.succ
    exact (ratBits_sub_le _ _).trans (by unfold differenceWidth;omega)
  have seedDiff : B ≤ differenceWidth B:=by unfold differenceWidth;omega
  have bitBound:=WitnessSolve.inputBits_le (Elimination.augmentedRows A (b-Fin.tail w)) (differenceWidth B)
    (WitnessSolve.augmented_entries _ _ _ (fun i j=>(ha i j).trans seedDiff) rhs)
  have solveWidth : WitnessSolve.solverHeight (totalBits (encodedGramInput (Elimination.augmentedRows A (b-Fin.tail w)))) ≤ M := by
    calc _ ≤ WitnessSolve.solverHeight ((d+1)*m*differenceWidth B) := by unfold WitnessSolve.solverHeight;gcongr
         _ ≤ M := by dsimp [M,outputWidth];omega
  obtain ⟨s,ks,ksb,start,head,data⟩:=header_run (fun q=>ratBits q ≤ M) caller m d raw atW cap limit callerSafe a r c v hcap bound
  have read : SlackRAM.InputAt s raw A b:=by simpa only [SlackRAM.InputAt,data] using stored
  obtain ⟨t,kt,ktb,table,tapes,whereX,lenX⟩:=assemble_run A b w s raw atW cap B M head read
    (fun j=>by rw [data];exact values j) high sep start.safe_end hb hw diff (three.trans first)
  let dst:=pointBase atW m d
  have room : 5 ≤ dst:=by dsimp [dst,pointBase,tableauBase];omega
  obtain ⟨u,t',solve,nu,ct,out,fields,_,_⟩:=WitnessSolve.program_run A (b-Fin.tail w) native t
    (tableauBase atW m) 208 cap (cap-1) dst M tapes foot (by omega) space two
    nativeSafe table.safe_end (three.trans first) solveWidth whereX lenX room x answer
  have boundDst : d ≤ Odd.slot dst:=by
    have mult:=Nat.mul_le_mul_left (d+1) hp
    simp only [Nat.mul_one] at mult
    dsimp [dst,pointBase,tableauBase,Odd.slot];omega
  obtain ⟨z,publish,actual,tag,nil⟩:=Publish.fromOdd_spec 0 d dst u t' x (fun q=>ratBits q ≤ M) nu ct hd
    boundDst ((fields 210 (by decide)).trans whereX) ((fields 211 (by decide)).trans lenX) out
  have staged := (Odd.leaf_run (fun q=>ratBits q ≤ M) native nativeSafe (start.seq table)).mono
    (Nat.mul_le_mul_left 4 (Nat.add_le_add ksb ktb))
  exact ⟨z,staged.seq (solve.seq (Fragment.Run.ofBlock publish)),actual,tag,nil⟩

end PrimalOutput
end Recovery
end LinearProgramming
end Optimization
end OAI
