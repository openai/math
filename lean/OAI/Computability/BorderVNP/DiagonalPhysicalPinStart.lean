import OAI.Computability.BorderVNP.DiagonalExteriorPrefixBanks

/-! # Physical post-boot pin states on every positive exterior -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM TeamContraction CompactMachine CellMacro.Generator BorderVNP.Cube

/-- The booted hardware and its actual pin substitution. These data precede
authentication of other teams' messages and therefore exist even on shared
exteriors that cannot complete their joint route. -/
structure PinStart (gen : Fragment IO) (n w : ℕ) where
  /-- Public argument words from the team’s processor header. -/
  pub : Arg → Word w
  /-- The routine table in which `install` places the cell generator. -/
  routines : TeamOpcode.Macros w 8
  /-- Post-boot register bank at entry to pin preparation. -/
  bank : Bank w
  /-- Post-boot memory at entry to pin preparation. -/
  memory : Memory w
  /-- Number of independent bits substituted at the team’s pins. -/
  guessWidth : ℕ
  /-- Bijection between pin bit vectors and native pin-preparation returns from this state. -/
  pins : (Fin guessWidth → Bool) ≃ Pins.Return pub (install gen n routines) bank memory

variable {R n w axes b h K s : ℕ} {id : TableEntry axes b h K s → ℕ} {gen : Fragment IO}

/-- Forget the post-route certificates while retaining the genuine pin
banks and every preparation opcode. -/
def PositiveTeam.start (T : PositiveTeam id gen n w) : PinStart gen n w :=
  ⟨T.pub,T.routines,T.bank,T.memory,T.guessWidth,T.pins⟩

/-- An initially unchecked returning pre-call path. -/
abbrev PinStart.Prefix (T : PinStart gen n w) (id : TableEntry axes b h K s → ℕ) :=
  Σ x : Fin T.guessWidth → Bool, SignedPreps id T.pub T.routines gen n T.bank T.memory T.pins x

/-- Every team can reach its private call boundary on the same exterior.
This asks nothing about its eventual private checks or its residue value. -/
def PinStart.jointSupport (id : TableEntry axes b h K s → ℕ) (T : Fin (R+1) → PinStart gen n w) : Prop :=
  ∀ u, Nonempty ((T u).Prefix id)

/-- The full tuple of returning preparations already certifies joint support.
Thus restricting the stronger local post-route certificates to supported exteriors
retains every genuine pre-call path. -/
noncomputable def PinStart.supportedPrefixes {X : Type} (U : X → Fin (R+1) → PinStart gen n w)
    (S : {x : X // jointSupport id (U x)} → Fin (R+1) → PositiveTeam id gen n w)
    (same : ∀ x u, (S x u).start=U x.val u) :
    JointBeforeCells S ≃ ((x : X) × ((u : Fin (R+1)) → (U x u).Prefix id)) := by
  let transfer (x : {x : X // jointSupport id (U x)}) :=
    Equiv.piCongrRight (fun u => Equiv.cast (congrArg (fun z : PinStart gen n w => z.Prefix id) (same x u)))
  let forget : ((x : {x : X // jointSupport id (U x)}) × ((u : Fin (R+1)) → (U x.val u).Prefix id)) ≃
      ((x : X) × ((u : Fin (R+1)) → (U x u).Prefix id)) :=
    ⟨fun a => ⟨a.1.val,a.2⟩,fun a => ⟨⟨a.1,fun u => ⟨a.2 u⟩⟩,a.2⟩,fun _ => rfl,fun _ => rfl⟩
  exact (Equiv.sigmaCongrRight transfer).trans forget

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
