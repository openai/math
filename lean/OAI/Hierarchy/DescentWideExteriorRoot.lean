import OAI.Hierarchy.DescentSeedExteriorVote
import OAI.Hierarchy.DescentExteriorRootImage
import OAI.Hierarchy.DescentPackedEpochPins

namespace OAI
/-! The original packed seed, selector tape and both exterior proposals at independent physical width. -/
namespace Hierarchy.DescentExteriorShelf.Root
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentExterior DescentGL Computability.VPVNP.BurstRAM ThreeFlat.Diagonal Catalyst Computability.BorderVNP.Crossing
open ProtocolRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F A : Type} [Field F] {k n e j r t : ℕ} (X : Approximation F k n) (R s payload bw : ℕ)
variable (seed : Select X R s → A) (lo C grain : ℕ) (ss : List (Source A))
set_option quotPrecheck false
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "H" => span j r t e
local notation "flag" => DescentWideSeedFlags.initial X R s payload bw seed

def widePackedPin (i : Fin lowEnd × Fin (bw+1)) : A ⊕ Bool :=
  let «prefix»:=fun a b=>if live : b < bw+1 then DescentWideSeedFlags.pin X R s payload bw seed a ⟨b,live⟩ else Sum.inr false
  headerPin bw lo C grain ss «prefix» i.1.val i.2.val

variable (origin : ℕ) (x : Fin e → Plane j r → Fin t → Bool) (z : A ⊕ Hidden e j r t → Bool)

theorem widePacked_read (sep : lowEnd ≤ origin) (arch : payload ≤ bw) (room : 2^j*t ≤ bw)
    (pos : 0 < grain) (fits : ∀a∈ss,DescentTerminalEpochBits.width a.C*grain ≤ bw)
    (ij : Fin (origin+17*H)×Fin (bw+1)) :
    (pin lowEnd origin (widePackedPin X R s payload bw seed lo C grain ss) ij).elim (assign x z) id =
      TraceWords.bits (TraceBanks.wide (widePackedImage X R s payload bw seed lo C grain ss origin x z ij.1.val)) ij.2 := by
  apply pin_read _ _ _ _ x z sep room _ ij
  intro i
  dsimp only [widePackedPin, wideOriginal, TraceWords.bits, TraceBanks.wide]
  apply header_pin lo C grain ss (z ∘ Sum.inl) (flag (z ∘ Sum.inl)) _ _ pos fits i.1.isLt i.2.val
  intro addr _ bit
  by_cases live : bit < bw+1
  · rw [dite_eq_left live]
    exact DescentWideSeedFlags.pin_at X R s payload bw seed (z ∘ Sum.inl) arch addr ⟨bit,live⟩
  · have upper:=((flag (z ∘ Sum.inl) addr).isLt).trans_le (Nat.pow_le_pow_right (by decide) (by omega : bw ≤ bit))
    simp [live,Nat.testBit_lt_two_pow upper]


end
end Hierarchy.DescentExteriorShelf.Root

end OAI
