import OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedStage

namespace OAI
/-! # The selected physical refresh witness has the native stage type -/

namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F] {m lanes hbits rem h pad : ℕ} {c : Fin m→Fin m→ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State m lanes)
  (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
  (hm : 2 ≤ m) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Bound (transition c h) ℝ γ)
  (L : A.Words Pins) (idx : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count)

set_option quotPrecheck false
local notation "physMove" => refreshMove T A u port hm hh sym rows zero conn
open private selectedWitness from OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedStage

/- Read the binder type directly from the checked existential without retaining
its predicate and its physical assembly calculation in the type expression. -/
open Lean Elab Term in
local elab "issuedCarrier% " witness:term:max : term => do
  let proof ← elabTerm witness none
  let type ← Meta.whnf (← Meta.inferType proof)
  unless type.isAppOfArity ``Exists 2 do throwError "expected the selected physical stage witness"
  return type.getAppArgs[0]!

/-- The existential's result type is the declared native stage of the selected move. -/
theorem RefreshIssued.type_eq :
    issuedCarrier% (selectedWitness T A u port hm hh sym rows zero conn L idx) =
      StageFor (physMove) idx L (refreshWords T A u port hm hh sym rows zero conn L idx) := rfl


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
