import OAI.Hierarchy.DescentPackedWalshPassAny
import OAI.Hierarchy.DescentEstimatorAnyDepth
import OAI.Hierarchy.DescentEstimatorLiteralIssue
import OAI.Hierarchy.DescentPackedWalshPhysicalBasis

namespace OAI
/-! # Total execution of the reset estimator at its physical calendar price -/

namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w : ℕ}

namespace EstimatorArena
open DescentGL
variable (E : EstimatorArena)

theorem numerator_any (m : Memory w) (fit : E.Fits w) :
    (numeratorCode E.transformAt E.start E.squareAt E.hosts E.high E.low E.precision w).Exec m
      (E.spectrumMem m) (numeratorTicks E.hosts E.high E.low) := by
  let top:=sqOffset E.start E.hosts E.high E.low
  let z:=axesList E.high E.low
  let B : Bank:=⟨location E.start E.hosts E.high E.dim,rowBits E.hosts E.high⟩
  let D : Bank:=⟨E.squareAt,smallKey E.low E.precision⟩
  let one:=after E.transformAt E.start E.hosts E.high E.low E.precision 0 z m
  let two:=ProtocolRAM.image top (E.hosts*2^E.high) (squareExpr B D) one
  have inputEnd : top+(E.dim+1)*page E.hosts E.high=E.inputEnd := by
    unfold inputEnd numeratorAt location
    rw [Nat.add_mul,Nat.one_mul,Nat.add_assoc]
  have bounded : E.inputEnd<2^w:=(E.calendar.pre (E.dim+1)).trans_lt fit.bounded
  have topEq : top=E.start+(E.dim+1)*page E.hosts E.high:=rfl
  have first : E.start≤top:=by omega
  have T : E.transformAt+E.dim*span E.hosts E.high E.low E.precision≤E.start :=
    E.areas.2.2.2.2.1
  have last : top+(E.dim+1)*page E.hosts E.high<2^w:=inputEnd.symm ▸ bounded
  have fst : top<2^w:=by omega
  have h₁ : (code w E.transformAt E.start E.hosts E.high E.low E.precision 0 z).Exec m one
      (duration E.hosts E.high E.dim) :=
    @after_any w E.transformAt E.start E.hosts E.high E.low E.precision m T fst
  have q : 0<page E.hosts E.high:=Nat.two_pow_pos _
  have before : location E.start E.hosts E.high E.dim+page E.hosts E.high=top := by
    simp [location,topEq,Nat.succ_mul,Nat.add_assoc]
  have static : E.squareAt+2^(smallKey E.low E.precision)≤E.start:=Nat.le_add_right E.staticEnd E.dataGap
  have bf : B.Fits w top:=⟨q,by change page E.hosts E.high<2^w;omega,before.le⟩
  have df : D.Fits w top:=⟨Nat.two_pow_pos _,by change 2^(smallKey E.low E.precision)<2^w;omega,static.trans first⟩
  have full : top+E.hosts*2^E.high<2^w := by
    have hw:=rows_le E.hosts E.high
    have hv:=Nat.mul_le_mul_right (page E.hosts E.high) (show 1≤E.dim+1 by omega)
    simp only [Nat.one_mul] at hv
    omega
  have legal : (squareExpr B D).Fits w top:=⟨df,bf,trivial⟩
  have sq : (scan w top (E.hosts*2^E.high) (squareExpr B D)).Exec one two (4+28*(E.hosts*2^E.high)) := by
    have price : 2*(squareExpr B D).work+4=28:=rfl
    rw [show 4+28*(E.hosts*2^E.high)=4+(E.hosts*2^E.high)*(2*(squareExpr B D).work+4) by
      rw [price,Nat.mul_comm 28]]
    exact @scan_exec w top (E.hosts*2^E.high) (squareExpr B D) one legal full
  have h₂ : (code w E.transformAt top E.hosts E.high E.low E.precision 0 z).Exec two
      (E.spectrumMem m) (duration E.hosts E.high E.dim) :=
    @after_any w E.transformAt top E.hosts E.high E.low E.precision two (T.trans first) last
  have firstAndSquare :
      ((code w E.transformAt E.start E.hosts E.high E.low E.precision 0 z).seq
        (scan w top (E.hosts*2^E.high) (squareExpr B D))).Exec m two
        (duration E.hosts E.high E.dim+(4+28*(E.hosts*2^E.high))) := by
    intro labels registers slots machine
    exact Procedure.Exec.then h₁ sq machine
  intro P R K M
  exact Procedure.Exec.then firstAndSquare h₂ M

/-- Issuing the fixed header and solving at the chosen reset date is total
on every input tape and has the same clock as on a measured branch. -/
theorem any (m : Memory w) (fit : E.Fits w) (endRoom : E.staticEnd<2^w)
    (central : PhysicalTrajectory.Room w E.dim E.solveAt E.bank)
    (payload : E.payload≤w) (stages : E.dim+1≤2^w) :
    ((E.header (w:=w)).program.seq (E.cpu w)).Exec m (E.image (E.literal m))
      ((4+10*(E.staticEnd-E.origin))+E.clock) := by
  let mounted:=E.literal m
  have header : (E.header (w:=w)).program.Exec m mounted (4+10*(E.staticEnd-E.origin)) :=
    (E.header_eq m endRoom).1
  let spectrum:=E.spectrumMem mounted
  let summed:=E.calendar.state E.plan E.hosts spectrum (E.dim+1)
  have num : (numeratorCode E.transformAt E.start E.squareAt E.hosts E.high E.low E.precision w).Exec
      mounted spectrum (numeratorTicks E.hosts E.high E.low) := @numerator_any w E mounted fit
  have all : (E.calendar.code E.plan w E.hosts (E.dim+1)).Exec spectrum summed
      (E.calendar.ticks E.plan E.hosts (E.dim+1)) := E.calendar_any fit payload stages spectrum
  have solve : (PhysicalTrajectory.program w E.dim E.solveAt E.bank).Exec summed (E.image mounted)
      (PhysicalTrajectory.time E.dim E.solveAt E.bank E.dim+DescentGLPermutationRAM.clock E.dim) :=
    PhysicalTrajectory.exec E.bank summed central
  have measured :
      ((numeratorCode E.transformAt E.start E.squareAt E.hosts E.high E.low E.precision w).seq
        (E.calendar.code E.plan w E.hosts (E.dim+1))).Exec mounted summed
        (numeratorTicks E.hosts E.high E.low+E.calendar.ticks E.plan E.hosts (E.dim+1)) := by
    intro labels registers slots machine
    exact Procedure.Exec.then num all machine
  have compute : (E.cpu w).Exec mounted (E.image mounted) E.clock := by
    intro P R K M
    exact Procedure.Exec.then measured solve M
  intro P R K M
  exact Procedure.Exec.then header compute M

end EstimatorArena
end
end Hierarchy.DescentPackedWalsh

end OAI
