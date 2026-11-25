import OAI.Hierarchy.GridRegisteredRoom
import OAI.Hierarchy.GridRegisteredWork

namespace OAI
/-! # The actual archive tariff supplies the selected registered grid setting -/

namespace Hierarchy.GridRegisteredSetting

open ThreeFlat Diagonal Diagonal.PhysicalStage
open GridScale Filter TraceDistribution Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing

/-- The same real selected archive supplies per-tick pin and directional room
as well as the total work used for the evaluator clock. All header operands,
initial input bits, and terminal sites refer to that particular run. -/
theorem eventual_issued_room {F : Type} [Field F] [Fintype F] (blk : Block F)
    {Q : ℕ→ℕ} {loss : ℕ→ℝ} (env : Envelopes Q loss) (m A c coeff degree : ℕ)
    (q : ℕ→ℕ) (range : ∀ᶠ w : ℕ in atTop, 0<q w ∧ q w≤Q w)
    (nodeDegree stageRate rootRate : ℕ) :
    ∃ workCoeff : ℕ, ∀ᶠ w : ℕ in atTop, let k := m+1
      let a := overhead Q loss w
      let n := side a-1
      let B := pairs A w (q w)
      let E := external k a B
      let ell := selector k w a
      let passes := traceBlocks k a
      let u := evalDepth w k A c a (q w)
      ∀ (paramsN : ℕ) (_ : paramsN≤ coeff*(w+1)^degree) (text : ℕ) (textFit : text≤w^2),
        let S := GridSelfHeader.rawSize w E B paramsN
        ∀ (axes pc regs words base fuel : ℕ) (_dim : axes+1=u+1-w/2) (hk : 2≤axes+1)
          (_ : pc≤64*w) (_ : regs≤64*w) (_ : words≤64*w)
          (M : Machine (64*w) pc regs words)
          (fit : NativeTrace.Fits M S base ((axes+1)+w/2) fuel)
          (hf : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (valid : blk.blockCharge*passes≤axes+1),
          let D : RunData F (64*w) pc regs words S base fuel axes (w/2) := ⟨M,fit,hf,st,blk,hk,passes,valid⟩
          ∀ (h : D.run.plan.History) (raw : Fin (w^2)→Bool)
            (params : Fin paramsN→Word (64*w)) (sel : Fin ell→Bool),
            let header := fun t : GridThrough.Cell k n × Fin (q w) =>
              GridReceiverHeader.header text textFit raw ((GridTicks.index t).val : Word (64*w)) params sel
            let C := D.issuedCharges
            let unit := D.issuedUnit w nodeDegree stageRate rootRate
            ∃ R : D.Room h C unit w m n B (q w) (pins w a) header,
              R.cap=2^(3*w/5) ∧ (∑ i, D.work h C unit i)≤2^u*workCoeff*(w+1)^51 := by
  have scale := trace_scale env (m+1) A c q range
  obtain ⟨workCoeff,work⟩ := RunData.eventual_ranked_work_of_bounds blk scale nodeDegree stageRate rootRate
  refine ⟨workCoeff,?_⟩
  filter_upwards [eventual_room blk env m A c coeff degree q range,work] with w build ranked
  dsimp only
  intro paramsN num text textFit axes pc regs words base fuel dim hk pcFit regFit wordFit M fit hf st valid
  let D : RunData F (64*w) pc regs words _ base fuel axes (w/2) := ⟨M,fit,hf,st,blk,hk,_,valid⟩
  intro h raw params sel
  have priced := ranked D rfl rfl dim rfl pcFit regFit wordFit h
  obtain ⟨R,cut⟩ := build paramsN num text textFit axes pc regs words base fuel dim hk M fit hf st valid
    h D.issuedCharges (D.issuedUnit w nodeDegree stageRate rootRate) priced.2 raw params sel
  exact ⟨R,cut,priced.1⟩

/-- Version for an existing installed machine with a dependent input size
and a selector whose actual length is known by an equality. -/
theorem eventual_issued_on {F : Type} [Field F] [Fintype F] (blk : Block F)
    {Q : ℕ→ℕ} {loss : ℕ→ℝ} (env : Envelopes Q loss) (m A c coeff degree : ℕ)
    (q : ℕ→ℕ) (range : ∀ᶠ w : ℕ in atTop, 0<q w ∧ q w≤Q w)
    (nodeDegree stageRate rootRate : ℕ) :
    ∃ C₁ : ℕ, ∀ᶠ w : ℕ in atTop, let k:=m+1
      let a:=overhead Q loss w
      let u:=evalDepth w k A c a (q w)
      let B:=pairs A w (q w)
      ∀ (paramsN text ell : ℕ) (_pn : paramsN≤ coeff*(w+1)^degree) (textFit : text≤w^2)
        (_se : ell=selector k w a) {pc regs words S base fuel axes : ℕ}
        (D : RunData F (64*w) pc regs words S base fuel axes (w/2))
        (_size : S=GridSelfHeader.rawSize w (external k a B) B paramsN)
        (_b : D.block=blk) (_stages : D.passes=traceBlocks k a) (_dim : axes+1=u+1-w/2)
        (_pfit : pc≤64*w) (_rfit : regs≤64*w) (_wfit : words≤64*w)
        (h : D.run.plan.History) (raw : Fin (w^2)→Bool) (params : Fin paramsN→Word (64*w)) (sel : Fin ell→Bool),
        let header := fun t : GridThrough.Cell k (side a-1) × Fin (q w) =>
          GridReceiverHeader.header text textFit raw ((GridTicks.index t).val : Word (64*w)) params sel
        let C := D.issuedCharges
        let unit := D.issuedUnit w nodeDegree stageRate rootRate
        ∃ R : D.Room h C unit w m (side a-1) B (q w) (pins w a) header,
          R.cap=2^(3*w/5) ∧ (∑ i,D.work h C unit i)≤2^u*C₁*(w+1)^51 := by
  obtain ⟨C₁,known⟩ := eventual_issued_room blk env m A c coeff degree q range nodeDegree stageRate rootRate
  refine ⟨C₁,?_⟩
  filter_upwards [known] with w available
  dsimp only
  intro paramsN text ell pn textFit se pc regs words S base fuel axes D size
  subst S ell
  obtain ⟨machine,fit,hf,state,block,hk,passes,passed⟩ := D
  intro b stages dim pfit rfit wfit
  change block=blk at b
  change passes=traceBlocks _ _ at stages
  subst block passes
  exact available paramsN pn text textFit axes pc regs words base fuel dim hk pfit rfit wfit
    machine fit hf state passed

/-- The per-tick work bound from the same ranked sum, with any fixed
polynomial charge for replaying an occurrence on the evaluator. -/
theorem eventual_tick_work {F : Type} [Field F] [Fintype F] {Q : ℕ→ℕ} {loss : ℕ→ℝ}
    (env : Envelopes Q loss) (m A c workCoeff J r : ℕ)
    (saving : UniversalTick.saving+c+(r+51)<A) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → let k := m+1
      let a := overhead Q loss w
      let n := side a-1
      let B := pairs A w q
      let p := pins w a
      let u := evalDepth w k A c a q
      ∀ {W pc regs words S base fuel axes low : ℕ} (D : RunData F W pc regs words S base fuel axes low)
        (template : TraceAdmission.Resources.Parameters ℕ) (h : D.run.plan.History)
        (C : D.run.Charges) (unit : ℕ) (header : GridThrough.Cell k n × Fin q → List Bool)
        (R : D.Room h C unit w m n B q p header) (_ : R.cap=2^(3*w/5))
        (_ : (∑ i,D.work h C unit i)≤2^u*workCoeff*(w+1)^51) (t : GridThrough.Cell k n × Fin q),
        J*(w+1)^r*((FactorAllocation.factors w (D.costs template h m n B C unit)
          (List.finRange (D.roots h)) (GridTicks.index t)).map fun i => D.work h C unit i).sum ≤
          UniversalTick.clock w UniversalTick.saving := by
  let k := m+1
  filter_upwards [average_work env k A c (r+51) (4*J*workCoeff*2^(r+51)) saving,
    rounding_room env k A J r UniversalTick.saving,eventually_ge_atTop 1]
      with w averages rounding age
  intro q pos top
  dsimp only
  intro W pc regs words S base fuel axes low D template h C unit header R cut total t
  let a := overhead Q loss w
  let n := side a-1
  let u := evalDepth w k A c a q
  have gn : n+1=side a := by dsimp only [n]; have := Nat.two_pow_pos (10*a); change 0 < side a at this; omega
  apply RunData.tick_work D template h C unit header R (J*(w+1)^r) (UniversalTick.clock w UniversalTick.saving) _ _ t
  · have counted : (∑ i,D.work h C unit i) =
        unit*D.run.rootTotal h C (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit) := by
      exact ((D.ordinal h).symm.sum_comp (Physical.publishedWork D.run h C _ unit)).trans
        (Physical.publishedWork_sum D.run h C _ unit)
    rw [←counted]
    have power : (w+1)^(r+51)≤2^(r+51)*w^(r+51) := by
      rw [←mul_pow]
      exact Nat.pow_le_pow_left (by omega) _
    calc
      _ ≤ 4*(J*(w+1)^r)*(2^u*workCoeff*(w+1)^51) := Nat.mul_le_mul_left _ total
      _ = 4*J*workCoeff*2^u*(w+1)^(r+51) := by rw [pow_add];ring
      _ ≤ 4*J*workCoeff*2^u*(2^(r+51)*w^(r+51)) := Nat.mul_le_mul_left _ power
      _ = (4*J*workCoeff*2^(r+51))*2^u*w^(r+51) := by ring
      _ ≤ UniversalTick.clock w UniversalTick.saving*ticks k a q := averages q pos top
      _ = _ := by
        change UniversalTick.clock w UniversalTick.saving*((side a)^k*q) = (n+1)^(m+1)*q*_
        rw [gn]
        exact Nat.mul_comm ..
  · rw [cut]
    exact (rounding q pos top _ (cutoff_real w)).2


end Hierarchy.GridRegisteredSetting

end OAI
