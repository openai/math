import OAI.Hierarchy.GridRegisteredSetting
import OAI.Hierarchy.GridPhysicalFactorBudget
import OAI.Hierarchy.GridSelfHeader
import OAI.Hierarchy.GridTickCapacity

namespace OAI
/-! # Room for the chosen native registered setting and its real input tape -/

namespace Hierarchy.GridRegisteredSetting

open ThreeFlat Diagonal Diagonal.PhysicalStage
open GridScale Filter TraceDistribution Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing

/-- The natural cutoff used for reader work and prefix demand lies under the
real cutoff in the directional allocation estimate. -/
theorem cutoff_real (w : ℕ) : ((2^(3*w/5) : ℕ) : ℝ) ≤ ((2:ℝ)^w)^(3/5:ℝ) := by
  have integer := Nat.div_mul_le_self (3*w) 5
  have real : ((3*w/5 : ℕ):ℝ)*5 ≤ 3*(w:ℝ) := by exact_mod_cast integer
  rw [dyad_nat, ←Real.rpow_natCast (2:ℝ) w]
  change dyad _ ≤ (dyad w)^(3/5:ℝ)
  rw [dyad_rpow]
  apply dyad_mono
  linarith

private theorem raw_inventory {w E B n coeff deg : ℕ} (age : 1≤w) (nonempty : 1≤B)
    (num : n≤coeff*(w+1)^deg) :
    GridSelfHeader.rawSize w E B n ≤ (1503+64*coeff)*(w+1)^(deg+2)*(E+B*w^2) := by
  let p := (w+1)^(deg+2)
  let M := E+B*w^2
  have poly : 1≤p := Nat.pow_pos (Nat.succ_pos _)
  have fixed := GridReceiverHeader.structural_words w coeff deg n num
  have one : 1≤M := by
    dsimp [M]
    have h := Nat.mul_le_mul nonempty (Nat.one_le_pow 2 w age)
    omega
  have tail : w^2+(n+GridReceiverHeader.count w)*(64*w) ≤ (1500+64*coeff)*p := by
    dsimp only [p]
    nlinarith only [fixed,Nat.zero_le w,Nat.zero_le (w^2)]
  have main : 2*E+B*w^2≤2*M := by dsimp [M]; omega
  have paid : (1500+64*coeff)*p≤(1500+64*coeff)*p*M := Nat.le_mul_of_pos_right _ one
  have lots : M≤p*M := Nat.le_mul_of_pos_left _ poly
  change E*2+w^2+B*w^2+(n+GridReceiverHeader.count w)*(64*w)≤(1503+64*coeff)*p*M
  nlinarith only [tail,main,paid,lots,Nat.zero_le (p*M)]

/-- The real native run, with its installed executable already in the allotted
text field. The local work bound is the output of the selected native
`archiveTariff` estimate. Original bit fibers, header lengths, averages,
rounding error, and directional passage room are derived here. -/
theorem eventual_room {F : Type} [Field F] [Fintype F] (blk : Block F)
    {Q : ℕ→ℕ} {loss : ℕ→ℝ} (env : Envelopes Q loss) (m A c coeff degree : ℕ)
    (q : ℕ→ℕ) (range : ∀ᶠ w : ℕ in atTop, 0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop, let k := m+1
      let a := overhead Q loss w
      let n := side a-1
      let B := pairs A w (q w)
      let E := external k a B
      let ell := selector k w a
      let passes := traceBlocks k a
      let u := evalDepth w k A c a (q w)
      ∀ (paramsN : ℕ) (_ : paramsN≤coeff*(w+1)^degree) (text : ℕ) (textFit : text≤w^2),
        let S := GridSelfHeader.rawSize w E B paramsN
        ∀ (axes pc regs words base fuel : ℕ) (_dim : axes+1=u+1-w/2) (hk : 2≤axes+1)
          (M : Machine (64*w) pc regs words)
          (fit : NativeTrace.Fits M S base ((axes+1)+w/2) fuel)
          (hf : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (valid : blk.blockCharge*passes≤axes+1),
          let D : RunData F (64*w) pc regs words S base fuel axes (w/2) := ⟨M,fit,hf,st,blk,hk,passes,valid⟩
          ∀ (h : D.run.plan.History) (C : D.run.Charges) (unit : ℕ)
            (_ : ∀ i,D.work h C unit i≤2^(3*w/5))
            (raw : Fin (w^2)→Bool) (params : Fin paramsN→Word (64*w)) (sel : Fin ell→Bool),
            let header := fun t : GridThrough.Cell k n × Fin (q w) =>
              GridReceiverHeader.header text textFit raw ((GridTicks.index t).val : Word (64*w)) params sel
            ∃ R : D.Room h C unit w m n B (q w) (pins w a) header, R.cap=2^(3*w/5) := by
  let k := m+1
  let C0 := 1503+64*coeff
  have scale := trace_scale env k A c q range
  filter_upwards [range,GridReceiverHeader.eventual_room_of_poly env k A coeff degree,
    controller_room env k A (8*C0) (degree+2) (Nat.succ_pos m),rounding_room env k A 2 0 0,
    allocation env k A,GridPhysicalSelector.physical_factor_budget blk scale,
    header_room env k A (Nat.succ_pos m),(grows env).eventually_ge_atTop 1,eventually_ge_atTop 1]
      with w good hdr volume round passage fibers geometry grown age
  let a := overhead Q loss w
  let n := side a-1
  let B := pairs A w (q w)
  let E := external k a B
  let P := pins w a
  let T := ticks k a (q w)
  let cap := 2^(3*w/5)
  dsimp only
  intro paramsN num text textFit
  let S := GridSelfHeader.rawSize w E B paramsN
  intro axes pc regs words base fuel dim hk M fit hf st valid
  let D : RunData F (64*w) pc regs words S base fuel axes (w/2) := ⟨M,fit,hf,st,blk,hk,_,valid⟩
  intro h C unit work raw params sel
  let headerLen := text+((paramsN+1)*(64*w)+(GridReceiverHeader.count w*(64*w)+selector k w a))
  have headerFit : 4*headerLen≤P := hdr (q w) good.1 good.2 paramsN num text textFit
  have BP : 0<B := (geometry (q w) good.1 good.2 B (by simp [B])).1
  have g4 : 4 ≤ side a := by
    change 2^2≤2^(10*a)
    exact Nat.pow_le_pow_right (by decide) (show 2≤10*a by change 1≤a at grown; omega)
  have gn : n+1=side a := by dsimp only [n]; omega
  have tally : S ≤ C0*(w+1)^(degree+2)*(E+B*w^2) := raw_inventory age BP num
  have transmission := (volume (q w) good.1 good.2).2
  change (8*C0*(w+1)^(degree+2))*(E+B*w^2)≤T*P at transmission
  have load : 8*S≤T*P := by
    exact (Nat.mul_le_mul_left 8 tally).trans (by simpa only [Nat.mul_assoc] using transmission)
  have saved : P≤2*(P-headerLen) := by omega
  have avg : 4*S≤T*(P-headerLen) := by
    have scaled := Nat.mul_le_mul_left T saved
    rw [show T*(2*(P-headerLen))=2*(T*(P-headerLen)) by ring] at scaled
    omega
  have capR := cutoff_real w
  have small := (round (q w) good.1 good.2 cap capR).1
  change 4*(2*(w+1)^0)*classes k w*cap ≤ P at small
  have rounded : 4*classes k w*cap≤P-headerLen := by
    simp only [pow_zero,Nat.mul_one] at small
    rw [show 4*2*classes k w*cap=2*(4*classes k w*cap) by ring] at small
    omega
  have exterior : E=(m+1)*GridIdleLayout.each m n B := by
    change (m+1)*(2*(side a)^(m+1-1)*B)=(m+1)*(2*(n+1)^m*B)
    rw [gn,Nat.add_sub_cancel]
  have room := fibers hk dim M fit hf st valid h
  refine ⟨⟨cap,P-headerLen,headerLen,good.1,by change 4 ≤ n+1; rw [gn]; exact g4,BP,?_,?_,work,?_,?_,
    rounded,?_,?_,?_⟩,rfl⟩
  · change 2*((m+1)*GridIdleLayout.each m n B) ≤ GridSelfHeader.rawSize w E B paramsN
    rw [←exterior]
    unfold GridSelfHeader.rawSize
    omega
  · exact Nat.pow_le_pow_right (by decide) (show 3*w/5≤w by omega)
  · intro v
    simpa only using room.2 S le_rfl v
  · change 4*S≤(n+1)^(m+1)*q w*(P-headerLen)
    rw [gn]
    exact avg
  · change headerLen+(P-headerLen) ≤ P
    omega
  · intro t
    exact (GridReceiverHeader.length text textFit raw _ params sel).le
  · have p := passage (q w) good.1 good.2
    have ge := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left capR
      (show (0:ℝ)≤(classes k w:ℝ) by positivity))
      (show (0:ℝ)≤(side a*q w:ℕ) by positivity)
    rw [gn]
    simpa only [k,cap,classes,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      using ge.trans p


end Hierarchy.GridRegisteredSetting

end OAI
