import OAI.Hierarchy.DescentResetPrimitiveReceivedVolume
import OAI.Hierarchy.DescentResetClippedDatePrice

namespace OAI
/-! # Uniform bit price for the registered reset primitive checkpoint -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentPlacedInvoiceVolume TerminalScale Filter
noncomputable section
variable (v : ResetOutput)

structure PrimitiveLimits (L increase work : ℕ) : Prop where
  nodes : v.birth.nodes≤L
  args : v.birth.arguments≤L
  roots : v.birth.roots≤L
  residual : v.birth.residual≤L
  shapes : v.birth.placement.shapes≤L
  blocks : v.birth.placement.blocks≤L
  finalNodes : v.primitive.chart.nodes≤L
  finalBlocks : v.primitive.chart.blocks≤L
  gain : increase≤L
  source : work≤L

def primitiveWork (baseWork : ℕ) :=v.birth.argumentBudget baseWork
def uniformPrimitiveFactor (L : ℕ) :=
  let root:=1+(L+1)*20
  let U:=1+(1+L*(2*L+11+19))+((2*L+11)+(1+L*(2*L+12))+11)
  (printed L+stemFactor (L*L) L root+suffixFactor L (L*L) L+
    printed (L+L+L+2)+finalFactor L L U)*(L+1)

theorem bounded_primitive_factor (L gain work : ℕ) (r : PrimitiveLimits v L gain work) :
    v.primitiveFactor gain (v.primitiveWork work)≤uniformPrimitiveFactor L:=by
  rcases r with ⟨hn,ha,hr,hk,hs,hx,hf,hb,hg,hw⟩
  simp only [primitiveFactor,uniformPrimitiveFactor,birthFactor,primitiveWork,DescentPrimitiveBirth.Layout.rootBudget,
    DescentPrimitiveBirth.Layout.batch,DescentPrimitiveBirth.Layout.gates,
    DescentPrimitiveBirth.Layout.argumentBudget,printed,stemFactor,suffixFactor,volumeFactor,finalFactor]
  gcongr

private theorem scale_primitive (j rate : ℕ) :
    uniformPrimitiveFactor (scale j rate)≤(2^48)*scale j (8*rate):=by
  let L:=scale j rate
  have algebra:uniformPrimitiveFactor L≤(2^40)*(L+1)^8:=by
    unfold uniformPrimitiveFactor printed stemFactor volumeFactor suffixFactor finalFactor
    ring_nf;omega
  have pos:1≤L:=Nat.two_pow_pos _
  have bound:L+1≤2*L:=by omega
  have power: L^8=scale j (8*rate):=by
    change (2^(rate*(j+1)))^8=2^((8*rate)*(j+1))
    rw [←pow_mul];congr 1;ring
  calc
    uniformPrimitiveFactor L≤2^40*(L+1)^8:=algebra
    _≤2^40*(2*L)^8:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bound _)
    _=2^48*scale j (8*rate):=by rw [mul_pow,power];ring

theorem primitive_date_price (rate receiver ratio saving : ℕ) :
    ∃lead exponent : ℕ,∀ᶠ h : ℕ in atTop,∀ j (z : ResetOutput) gain work H groups δ copies N b width rows w fee,
      j≤Nat.log 2 h→2^h≤copies→PrimitiveLimits z (scale j rate) gain work→
      N≤ scale j rate→b≤ scale j rate→width≤ scale j receiver→w≤ratio*h→
      rows*h≤(2+N)*h+groups*(32*N*b+16*width)→
      fee≤z.primitiveFactor gain (z.primitiveWork work)*receiptArea h H rows→1≤δ→
      fee*w≤H*h*(lead*scale j exponent)+H*(groups*δ)*(lead*scale j exponent)+copies/(2^j)^saving:=by
  obtain ⟨C,E,late⟩:=clipped_date_price (2^48) (8*rate) 3 rate receiver ratio saving
  refine ⟨C,E,?_⟩
  filter_upwards [late] with h all
  intro j z gain work H groups δ copies N b width rows w fee height lot r small bits broad word packed tariff rad
  exact all j H groups δ copies _ N b width rows w fee height lot
    ((bounded_primitive_factor z _ _ _ r).trans (scale_primitive j rate)) small bits broad word packed tariff rad

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
