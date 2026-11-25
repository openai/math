import OAI.Hierarchy.DescentPackedWalshCalendarInput

namespace OAI
/-! # Measured packed reset columns execute the canonical basis estimator in the same memory -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentGL DescentIntegerScale DescentMeasuredWeights DescentWeightColumnRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {A C : Type} [Fintype A] [Fintype C] {N u l b c g w base gainBound q : ℕ}
local notation "k" => u+l

theorem measured_basis (calendar : Calendar k) (h : ℕ) (hc : 0<c) (mem rom : Memory w)
    (levels : A→ℕ) (loc : Item levels C↪Fin N)
    (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ) (x : A→Bits k→ℕ) (y : C→Bits k→ℕ)
    (f full K : ℕ) (gainBits : ∀i,padded loc (gain levels f full K) 0 i<2^g)
    (B : ℕ) (bound : ∀v a,padded loc (load levels x y) (fun _=>0) v a≤B)
    (numSize : 2^(3*k)*B^2<2^b) (lanes : laneBits k h c=l)
    (lv : ∀v,padded loc (level levels j cj) 0 v<2^w) (stages : k+1≤2^w)
    (enough : calendar.limit<2^w) (width : h≤w) (prec : c+Nat.clog 2 N≤w)
    (billSize : ∀s<k+1,∀v d,bill s (padded loc (level levels j cj) 0)
      (fun z=>(⟨_,gainBits z⟩:Cell g)) (padded loc (load levels x y) (fun _=>0)) v d<2^c)
    (inputs : ∀s<k+1,DepthInput (calendar.atDepth s) calendar.limit h b c g hc
      (padded loc (level levels j cj) 0) (fun z=>(⟨_,gainBits z⟩:Cell g))
      (padded loc (load levels x y) (fun _=>0)) mem rom)
    (bankRoom : PhysicalTrajectory.Room w k base (fun s=>(calendar.atDepth s).out))
    (before : calendar.limit≤base)
    (positive : 0<q) (estimatorBound : 3*k+gainBound+2≤w)
    (scoreBound : ∀v d,mixingWeightNumerator levels j cj x y f full K v d≤2^gainBound) :
    let P:=reduction N u l c h hc
    let bank:=fun s=>(calendar.atDepth s).out
    let measured:=calendar.state P N mem (k+1)
    let W:=mixingWeightNumerator levels j cj x y f full K
    let μ:=PhysicalTrajectory.canonicalTrajectory W q k
    let dst:=PhysicalTrajectory.finalMemory k base bank measured
    ((calendar.code P w N (k+1)).seq (PhysicalTrajectory.program w k base bank)).Exec mem dst
      (calendar.ticks P N (k+1)+(PhysicalTrajectory.time k base bank k+DescentGLPermutationRAM.clock k)) ∧
    (∀i : Fin k,dst (PhysicalTrajectory.pointer k base i.val)=((rowIndex k (rowFunctional μ i)).val:Word w)) ∧
    (∀i : Fin (2^k),dst (PhysicalTrajectory.outputBase k base+i.val)=
      ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm i))).val:Word w)) ∧
    ∀z<calendar.limit,dst z=mem z := by
  dsimp only
  obtain ⟨evaluate,columns,frame⟩:=measured_calendar calendar h hc mem rom _ _ _ B bound numSize lanes lv
    stages enough width prec billSize inputs
  obtain ⟨select,rows,cube,kept⟩:=issue_canonical levels loc j cj x y f full K gainBits _ _ bankRoom
    positive estimatorBound scoreBound (fun v=>columns v.val v.isLt)
  refine ⟨?_,rows,cube,fun z hz=>(kept z (hz.trans_le before)).trans (frame z hz)⟩
  intro labels regs slots machine
  exact Procedure.Exec.then evaluate select machine

end
end Hierarchy.DescentPackedWalsh

end OAI
