import OAI.Computability.BorderVNP.DiagonalPositiveExteriorPrepare
import OAI.Computability.BorderVNP.DiagonalPositiveExteriorHeader
import OAI.Computability.BorderVNP.DiagonalTeamPinChoices

/-! # Moving the single native substituted-index guess outside the exterior route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator CompactMachine
open CellMacro.Generator _root_.OAI.Computability.BorderVNP.Cube

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (ib hb sb : Fin (R+1) → ℕ)
variable {axes b h K sym : ℕ} {id : TableEntry axes b h K sym → ℕ} {gen : Fragment IO}

/-- Interpret the same bits on a real positive team whose startup measured the
specified physical pin bank. The cast changes only the dependent index proof. -/
def teamGuessEquiv (u : Fin (R+1)) (T : PositiveTeam id gen n w)
    (width : T.guessWidth = (G.pinLayout u (ib u) (hb u) (sb u)).guessWidth) :
    TeamGuess G ib hb sb u ≃ (Fin T.guessWidth → Bool) :=
  Equiv.arrowCongr (finCongr width.symm) (Equiv.refl Bool)

/-- Native positive team preparations on all real pin guesses. The only free
guess among the teams is the one true raw substituted-index word at team zero. -/
noncomputable def positiveJointPrefixes (T : Fin (R+1) → PositiveTeam id gen n w)
    (width : ∀ u, (T u).guessWidth = (G.pinLayout u (ib u) (hb u) (sb u)).guessWidth) :
    let pin := fun (bits : Fin d → Bool) u => teamGuessEquiv G ib hb sb u (T u) (width u) ((G.jointGuess ib hb sb).symm bits u)
    (∀ u : Fin (R+1), (T u).Prefix) ≃
      Σ bits : Fin d → Bool, ∀ u, SignedPreps id (T u).pub (T u).routines gen n (T u).bank (T u).memory (T u).pins (pin bits u) := by
  intro pin
  let prep (u : Fin (R+1)) := SignedPreps id (T u).pub (T u).routines gen n (T u).bank (T u).memory (T u).pins
  let cast (u : Fin (R+1)) := teamGuessEquiv G ib hb sb u (T u) (width u)
  let adapted := Equiv.piCongrRight fun u => (Equiv.sigmaCongrLeft (β:=prep u) (cast u)).symm
  exact adapted.trans (G.jointPrefixes ib hb sb (fun u bits => prep u (cast u bits)))

variable {X : Type} (T : X → Fin (R+1) → PositiveTeam id gen n w)
    (width : ∀ x u, (T x u).guessWidth = (G.pinLayout u (ib u) (hb u) (sb u)).guessWidth)

/-- An exterior may alter every team's actual boot bank, pin return and
prepared memory. Its physical index width is fixed, so the independent raw pin
can nevertheless be chosen before that exterior, with no loss of paths. -/
noncomputable def exteriorPinPrefixes :
    let pin := fun (x : X) (bits : Fin d → Bool) u => teamGuessEquiv G ib hb sb u (T x u) (width x u)
      ((G.jointGuess ib hb sb).symm bits u)
    (Σ x : X, ∀ u, (T x u).Prefix) ≃
      Σ bits : Fin d → Bool, (x : X) × ∀ u, SignedPreps id (T x u).pub (T x u).routines gen n
        (T x u).bank (T x u).memory (T x u).pins (pin x bits u) := by
  intro pin
  let prepare x bits := ∀ u, SignedPreps id (T x u).pub (T x u).routines gen n
    (T x u).bank (T x u).memory (T x u).pins (pin x bits u)
  let swap : (Σ x : X, Σ bits : Fin d → Bool, prepare x bits) ≃ (Σ bits : Fin d → Bool, Σ x : X, prepare x bits) :=
    { toFun := fun ⟨x,bits,q⟩ => ⟨bits,x,q⟩
      invFun := fun ⟨bits,x,q⟩ => ⟨x,bits,q⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Equiv.sigmaCongrRight fun x => positiveJointPrefixes G ib hb sb (T x) (width x)).trans swap

/-- The original accepting cell, tally and private-bit fibers may be carried
unchanged through the pin/exterior reindexing by evaluating them on the recovered
original preparations. -/
noncomputable def exteriorPinAssignments (fiber : (x : X) → ((u : Fin (R+1)) → (T x u).Prefix) → Type*) :
    let E := exteriorPinPrefixes G ib hb sb T width
    (Σ x : X, (p : (u : Fin (R+1)) → (T x u).Prefix) × fiber x p) ≃
      Σ z, fiber (E.symm z).1 (E.symm z).2 := by
  intro E
  exact (Equiv.sigmaAssoc fiber).symm.trans (Equiv.sigmaCongrLeft' E)

/-- The literal passing private-cell and subtotal witnesses are retained under
the actual pin/exterior permutation. The codomain's first coordinate is the one
raw substituted pin and its exterior is the original complete shared assignment. -/
noncomputable def acceptedExteriorPinEquiv (joined : ∀ x (p : (u : Fin (R+1)) → (T x u).Prefix),
    JoinedCells (fun u => (T x u).pub) (fun u => (T x u).postMemory) (fun u => (T x u).generated) p) :
    let E := exteriorPinPrefixes G ib hb sb T width
    ProcessorSlots.AcceptedExterior T joined ≃ Σ z, let original := E.symm z
      {a : (joined original.1 original.2).Private // positivePass (T original.1) (joined original.1) ⟨original.2,a⟩} := by
  intro E
  let fiber (x : X) (p : (u : Fin (R+1)) → (T x u).Prefix) :=
    {a : (joined x p).Private // positivePass (T x) (joined x) ⟨p,a⟩}
  let grouped : ProcessorSlots.AcceptedExterior T joined ≃ Σ x : X, (p : (u : Fin (R+1)) → (T x u).Prefix) × fiber x p :=
    { toFun := fun z => ⟨z.1,z.2.val.1,⟨z.2.val.2,z.2.property⟩⟩
      invFun := fun z => ⟨z.1,⟨⟨z.2.1,z.2.2.val⟩,z.2.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact grouped.trans (exteriorPinAssignments G ib hb sb T width fiber)

end TeamContraction

end BorderVNP
end Computability
end OAI
