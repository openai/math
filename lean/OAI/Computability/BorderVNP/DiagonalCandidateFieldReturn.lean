import OAI.Computability.BorderVNP.DiagonalSignedCandidateSiteSelection

/-! # Retaining a candidate's actual return at its physical processor fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM TeamContraction JointHeader Packing BorderVNP.Cube Physical LocalRow
open PackedHistoryCircuit Crossing

variable {w R X : ℕ} {ar : CubeArena.Layout} {D : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {word : Broadcast ar.n ar.header.d ar.header.cap} {owner : ℕ → Fin (R+1)}
    {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)}
    {frame base : ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {mem : Memory w}
    {I : Type*} [Fintype I] {host : I → Fin ar.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {d : ℕ} {P A : Type*} {bits : P → ℕ} {N : Network d P bits} {cell : N.Site → Fin ar.cells}
    {recv : A → Fin ar.cells} {amount : A → ℕ}

local notation3 (prettyPrint := false) "Site₀" => CandidateSite (X:=X) ar D pp lp word owner decl group
  frame base pins fields f guess pub mac reg mem host key sizes N cell recv amount

/-- The pin return's equality of layouts and heterogeneous equality of
processor fields put the candidate on the physical wiring. The witness carries
the registers, memory and observation of the original return. -/
theorem CandidateSite.reindex_fields_return
    {actualPins : Pins.Layout} (actualFields : Pins.ProcessorFields actualPins)
    (shape : pins=actualPins) (same : HEq fields actualFields)
    {T : Type*} {old : Fin 81 → Word w} {fresh gates outputs width off ell controls : ℕ}
    {profile : List Bool} {claims : List (List Bool)} {pad used : ℕ}
    {preRegs : T → Bank w} {preMem : T → Memory w} {charged : T → ℕ} {physical : T → Prop}
    (received : ∃ (t : T) (s : Site₀), s.OnReturn old fresh gates outputs width off ell controls profile claims
      pad (preRegs t) (preMem t) used (charged t) ∧ physical t) :
    ∃ (t : T) (s : CandidateSite (X:=X) ar D pp lp word owner decl group frame base actualPins actualFields
      f guess pub mac reg mem host key sizes N cell recv amount), s.OnReturn old fresh gates outputs width off ell
        controls profile claims pad (preRegs t) (preMem t) used (charged t) ∧ physical t := by
  cases shape
  obtain rfl := eq_of_heq same
  exact received

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
