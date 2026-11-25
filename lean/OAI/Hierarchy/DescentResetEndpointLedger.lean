import OAI.Hierarchy.DescentResetEndpointTariff
import OAI.Hierarchy.DescentStageLedger

namespace OAI
/-! # Summing the measured endpoint procedures on the reset dates of the private calendar -/
namespace Hierarchy.DescentSixParty
open Filter DescentCompiler DescentCompiler.TerminalScale DescentPlainTerminal.Suffix
open PackedFlow.Padded DescentPackedWalsh DescentSIMDLookup ProtocolRAM
noncomputable section

/-- The addresses and the fixed grouping proofs in the re-packing instruction. -/
structure EndpointSite (P : StencilBook) (h e : ℕ) where
  inputs : StencilBook.Sources
  countWord : inputs.count.work≤6
  chip : Bank
  first : ℕ
  base : ℕ
  out : ℕ
  full : ℕ
  grouped : 2^P.c=2^P.high*(2^(laneBits P.m h P.b-P.r-e)*P.M)
  live : 0<P.M

def EndpointSite.fee {P : StencilBook} {h e : ℕ} (R : EndpointSite P h e) (t f g n w : ℕ) :=
  endpointInvoice P R.inputs R.chip R.first R.base R.out f R.full (quota t) g (2^n) w
    (2^(laneBits P.m h P.b-P.r-e)) R.grouped (Nat.two_pow_pos _) R.live

variable {F : Type} [Field F] (G : PoweredGadget F)

private theorem endpoint_shared (fee x y M u : ℕ) (price : fee ≤ x*u+y*u+M) (fit : M≤x) :
    fee ≤ x*(u+1)+y*(u+1) := by
  simpa only [Nat.mul_add, Nat.mul_one] using price.trans (by omega : x*u+y*u+M ≤ (x*u+x)+(y*u+y))

/-- The degrees in both applications of the stage ledger depend only on the original gadget. -/
theorem endpoint_dates (t f g reset τ B D n ratio qDegree : ℕ) (den : 0<B)
    (width : 2*(3*stencilRate G t f g reset+1)≤B)
    (tailFit : 6*stencilRate G t f g reset+0+3+(qDegree+5)≤τ)
    (timeFit : 2*((2+hostRate t reset*(t+1)+6*stencilRate G t f g reset+(0+1)+1)+5+qDegree)≤B) :
    ∀ᶠ h : ℕ in atTop,∀M q p w : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀dates : (i : Fin (S.length+1)) → Option (EndpointSite (S.endpointBook k (tail τ J) i.val p f D h n)
        h (S.endpointExponent k (tail τ J) i.val p f D h n)),
      0<q→q≤ scale J qDegree→h≤32*(q*p)→p≤h→2^h≤M→w≤ratio*h→
      (∑i,(dates i).elim 0 (fun z=>z.fee t f g n w))*2^J≤2*(M*(S.copies*p)) := by
  let d:=6*stencilRate G t f g reset
  let C:=endpointFactor ratio
  filter_upwards [endpoint_date_tariff G t f g reset τ B D n ratio 0 den width,
    calibration_at G t f g reset d d qDegree (C+1) 0 τ tailFit B den timeFit,
    eventually_ge_atTop 1] with h tariff ledger hpos
  intro M q p w J S k dates qpos qa spent pFit ambient machine
  let u:=C*scale J d
  have positive:1≤ scale J d:=Nat.two_pow_pos _
  have short:u+1≤ scale J d*((C+1)*(tail τ J+1)^0):=by
    simp only [pow_zero,Nat.mul_one]
    dsimp [u];rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm C];omega
  apply ledger M q p (u+1) (u+1) qpos qa spent short short
  intro i
  cases pick : dates i with
  | none=>simp
  | some job=>
    obtain ⟨_,_,price⟩:=tariff M i.val p w job.inputs job.chip job.first job.base job.out job.full
      (Nat.le_of_lt_succ i.isLt) pFit ambient machine job.countWord
    have rad:0<S.radix:=Nat.two_pow_pos _
    have pop:M≤S.hostSize i.val:=by
      change M≤M*(2^S.hostGain*S.radix)^i.val
      exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos _) rad))
    have target:=pop.trans (Nat.le_mul_of_pos_right _ hpos)
    simp only [pow_zero,Nat.div_one] at price
    simp only [Option.elim_some]
    change job.fee t f g n w≤S.hostSize i.val*h*u+S.hostSize i.val*(S.groupCount i.val*S.radix)*u+M at price
    exact endpoint_shared _ _ _ _ u price target

end
end Hierarchy.DescentSixParty

end OAI
