import OAI.Hierarchy.DescentSixPartyGadget

namespace OAI
/-! # Recovering the original eight supply multiplicities of the six-party gadget -/
namespace Hierarchy.DescentOrdinaryPaletteBirth
open DescentSixParty
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

def recover (supply : Fin 8→ℕ) : Option (Profile G.C) :=
  let v:=fun e=>supply e-G.k
  if h : ∀e,G.k≤ supply e ∧ v e<G.C+2 then
    if total : (∑e,v e)≤G.C+8 then some ⟨fun e=>⟨v e,(h e).2⟩,total⟩ else none
  else none

theorem recover_saved (p : Profile G.C) (supply : Fin 8→ℕ) (observed : ∀e,supply e=(p.1 e).val+G.k) :
    recover G supply=some p :=by
  have digits (e : Fin 8) : supply e-G.k=(p.1 e).val:=by rw [observed];omega
  have valid (e : Fin 8) : G.k≤ supply e ∧ supply e-G.k<G.C+2:=
    ⟨by rw [observed];omega,by rw [digits];exact (p.1 e).isLt⟩
  have total : (∑ e, (supply e-G.k))≤G.C+8:=by
    calc
      _ = ∑ e, (p.1 e).val := Finset.sum_congr rfl (fun e _=>digits e)
      _ ≤ _ := p.2
  simp only [recover,dite_eq_left valid,dite_eq_left total,Option.some.injEq]
  apply Subtype.ext
  funext e
  exact Fin.ext (digits e)

theorem recover_iff (p : Profile G.C) (supply : Fin 8→ℕ) :
    recover G supply=some p ↔ ∀e,supply e=(p.1 e).val+G.k :=by
  refine ⟨?_,recover_saved G p supply⟩
  intro seen
  unfold recover at seen
  dsimp only at seen
  split at seen
  next good =>
    split at seen
    next total =>
      have same:=Option.some.inj seen
      intro e
      have digit:=congrArg (fun v : Profile G.C=>(v.1 e).val) same
      change supply e-G.k=(p.1 e).val at digit
      have lo:=(good e).1
      omega
    next => contradiction
  next => contradiction

end
end Hierarchy.DescentOrdinaryPaletteBirth

end OAI
