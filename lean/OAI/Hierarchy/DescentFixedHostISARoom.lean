import OAI.Hierarchy.DescentTerminalHostISARoom
import OAI.Hierarchy.DescentChosenExteriorHeadWidths
import OAI.Hierarchy.DescentChosenGrainRoom

namespace OAI
/-! # The purchased finite host fits the ISA at its chosen dyadic height -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Catalyst Filter
open ThreeFlat.Routing
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- One invoice for the candidate's actual compiled program implies its four ISA bounds. -/
def ISAFromInvoice (t f g reset τ β W price h M : ℕ) {cp pins : ℕ} (X : Approximation F cp pins) : Prop :=
  let J:=Nat.log 2 h/(2*β)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let s:=S.firstWidth G.b (headGrain G S k h)
  let w:=W*h
  let E:=Fintype.card (Port pins X.width)
  ∀pcs regs firstFree fuel obs extra rate : ℕ,
    (extra+
        (257*(1000*(2*(7*(rate+6))+2)*(2*4^7+1))+256*fixedISAPrice*(rate+6))*
          (pcs+regs+firstFree+fuel+obs+2^h+1)*(h+1))*2^J≤price*(S.copies*s)*(M+2^J*E) →
      pcs≤2^(w+1) ∧ regs≤2^(w+1) ∧ CheapISA.hostFuel fuel+obs≤2^(CheapISA.width w+1) ∧
        (CheapISA.dataBase pcs regs+firstFree)+(CheapISA.hostFuel fuel+obs)≤2^(3*h)

/-- The price is fixed before the height at which the program and its memory are examined. -/
theorem cofinal_isa_from_invoice (t f g reset τ β W price : ℕ) (wide : 3≤W) :
    ∀ᶠ h : ℕ in atTop, ∀M : ℕ, M≤(2^h)^2 → ∀{cp n : ℕ} (X : Approximation F cp n),
      10*(X.size+1)≤M → ISAFromInvoice G t f g reset τ β W price h M X :=by
  filter_upwards [wide_host_isa_room G t f g reset τ price] with h bounds
  intro M upper cp n X opened
  let J:=Nat.log 2 h/(2*β)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let s:=S.firstWidth G.b (headGrain G S k h)
  have fits : s≤h := S.split_first_width G.b h (NativeBranch.binLimit (k:=k) S)
    (2^headChunk G S) (Nat.two_pow_pos _)
  dsimp only [ISAFromInvoice]
  intro pcs regs firstFree fuel obs extra rate spent
  exact bounds J M s (W*h) pcs regs firstFree fuel obs extra rate X (Nat.div_le_self ..)
    upper opened fits (Nat.mul_le_mul_right h wide) spent

end
end Hierarchy.DescentSixParty

end OAI
