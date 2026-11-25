import OAI.Hierarchy.DescentExteriorTokenLedger
import OAI.Hierarchy.DescentSeedWorld

namespace OAI
/-! # The hub equality in each real seed stack has exactly one original external word -/

namespace Hierarchy.DescentInitialHost
open DescentCompiler DescentSixParty MarkedWorld DescentResetTrunks Computability.BorderVNP.Crossing Catalyst CatalystSubstitution CorrectionBatch
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
variable {R s : ℕ} (c : (initialGroup X R s).Choice)
local notation "Pin" => Fin (Fintype.card (Port p X.width))
local notation "N" => X.network.copyGraph

theorem seed_exterior_count (j : Fin R) (pin : Pin) :
    ((initialGroup X R s).state c).exteriorTokens ⟨j,.inr pin⟩=1 := by
  unfold exteriorTokens bin
  rw [Finset.sum_eq_single (⟨j,pin⟩ : Σ_ : Fin R,Pin)]
  · exact ite_eq_left rfl
  · rintro ⟨i,b⟩ _ ne
    apply ite_eq_right
    intro attached
    have same : (⟨i,Sum.inr b⟩ : Σ _ : Fin R,Site N) = ⟨j,Sum.inr pin⟩ := attached
    have ij : i=j := congrArg Sigma.fst same
    subst j
    have h : b=pin := Sum.inr.inj (congrArg (fun a : Σ_ : Fin R,Site N => a.2) same)
    exact ne (by subst b;rfl)
  · simp

theorem seed_exterior_owners (pin : Σ _ : Fin R, Pin) : seedHub X c (((initialGroup X R s).state c).graph.attach pin)=true := rfl

theorem seed_hub_balance : ((initialGroup X R s).state c).HubExterior (seedHub X c) := by
  rintro ⟨j,u|pin⟩ live
  · change false=true at live
    contradiction
  · have read := measure_seed X c 1 0 ⟨j,.inr pin⟩
    have same : ((initialGroup X R s).state c).siteUnits (seedHub X c) (fun _=>([] : List Unit)) 1 256 0 ⟨j,.inr pin⟩=
        ((initialGroup X R s).state c).siteUnits (seedHub X c) (seedRecords X c) 1 256 0 ⟨j,.inr pin⟩ := by simp [siteUnits]
    let v : ((initialGroup X R s).state c).graph.Site := ⟨j,.inr pin⟩
    have width := ((initialGroup X R s).state c).exterior_width_eq (s:=s) (fun _=>Nat.mul_one s) v
    have single := seed_exterior_count X c j pin
    have external : ((initialGroup X R s).state c).exteriorWidth v = s :=
      width.trans ((congrArg (s*·) single).trans (Nat.mul_one s))
    refine ((same.trans read).trans ?_).trans (congrArg (256*·) external.symm)
    rw [hub_load]
    simp [hubFlag,Nat.mul_comm]

end
end Hierarchy.DescentInitialHost

end OAI
