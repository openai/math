import OAI.Computability.BorderVNP.DiagonalSignedCandidateSiteSelection

/-! # The same signed candidate under its observed public registers -/

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

/-- Express the returned candidate under the public words and macro table
recorded in the physical team's history. -/
noncomputable def CandidateSite.rebankPublic (s : CandidateSite (X:=X) ar D pp lp word owner decl group frame base pins fields f guess
      pub mac reg mem host key sizes N cell recv amount) {front : Arg → Word w} {routines : TeamOpcode.Macros w 8}
    (hpub : front=pub) (hmac : routines=mac) : CandidateSite (X:=X) ar D pp lp word owner decl group frame base pins fields f guess
      front routines reg mem host key sizes N cell recv amount := by
  cases hpub
  cases hmac
  exact s

variable (s : CandidateSite (X:=X) ar D pp lp word owner decl group frame base pins fields f guess
      pub mac reg mem host key sizes N cell recv amount) {front : Arg → Word w} {routines : TeamOpcode.Macros w 8}
    (hpub : front=pub) (hmac : routines=mac)

/-- Reindexing a processor leaves all original and shared memory observations
available at their attained addresses. -/
theorem CandidateSite.rebankPublic_fields :
    let a := s.rebankPublic hpub hmac
    a.geometry=s.geometry ∧ a.middle=s.middle ∧ a.old=s.old ∧ a.control=s.control ∧
    a.receipt.history.dataInput=s.receipt.history.dataInput ∧
    a.receipt.history.sharedInput=s.receipt.history.sharedInput := by
  cases hpub
  cases hmac
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The original cost, geometry return, and all copied header fields still
belong to this processor after identifying its public registers. -/
theorem CandidateSite.rebankPublic_onReturn {old : Fin 81 → Word w} {fresh gates outputs width off ell controls : ℕ}
    {profile : List Bool} {claims : List (List Bool)} {pad : ℕ} {preRegs : Bank w} {preMem : Memory w}
    {used charged : ℕ} (attained : s.OnReturn old fresh gates outputs width off ell controls profile claims pad
      preRegs preMem used charged) :
    (s.rebankPublic hpub hmac).OnReturn old fresh gates outputs width off ell controls profile claims pad
      preRegs preMem used charged := by
  cases hpub
  cases hmac
  exact attained

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
