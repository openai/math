import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankNative
import OAI.Computability.NearSquareRoot.InterchangePackedRequest

/-! # Identifying padded physical rows with the outer cubic bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.InterchangeROMTable NearSquareRoot.InterchangeROMRepair NearSquareRoot.InterchangeROMRepair.Physical

open private stripe_render from OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocalLift

/-- The label-major, lane-minor packet is exactly the padded bank's single
natural ordinal. Any transformation of keys acts inside every such lane. -/
theorem bank_wires {K D : Type} {p l n : ℕ} (rows : Series K) (pay : Series D)
    (v : Fin (l*n) → K → Tree)
    (good : ∀ u i, ∃ digits : D → ZMod (p+1), v u i = stripe pay (fun j => numeral (digits j).val)) :
    ∃ x : Bank (ZMod (p+1)) (Fin l) (K × D) (Fin n), ∀ σ : K → K,
      Task.forest id (LocalTable.Lift.bank rows (fun _ => pay) (fun i j => (i,j))
        (fun m z k => x m (σ z.1,z.2) k)) =
      stripe (Series.natural (l*n)) (fun u => stripe rows (fun i => v u (σ i))) := by
  choose digits enc using good
  let x (i : Fin l) (z : K × D) (k : Fin n) := digits (finProdFinEquiv (i,k)) z.1 z.2
  refine ⟨x,fun σ => ?_⟩
  rw [LocalTable.Lift.bank,stripe_render]
  apply congrArg (stripe _)
  funext u
  apply congrArg (stripe _)
  funext i
  change stripe pay (fun j => numeral (digits (finProdFinEquiv
    ((finProdFinEquiv.symm u).1,(finProdFinEquiv.symm u).2)) (σ i) j).val) = _
  rw [Prod.mk.eta,Equiv.apply_symm_apply,← enc]

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
