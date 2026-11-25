import OAI.Hierarchy.DescentExteriorRootImage
import OAI.Hierarchy.DescentPackedEpochSeedImage

namespace OAI
/-! # The true compact count and chronological selector pins in the joint exterior input -/
namespace Hierarchy.DescentExteriorShelf.Root
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentExterior DescentGL Computability.VPVNP.BurstRAM ThreeFlat.Diagonal Catalyst Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F A : Type} [Field F] {k n e j r t : ℕ} (X : Approximation F k n) (R s w : ℕ)
variable (seed : Select X R s→ A) (lo C grain : ℕ) (ss : List (Source A))
set_option quotPrecheck false
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "H" => span j r t e

def packedPin (i : Fin lowEnd×Fin (w+1)) : A⊕Bool :=
  let earlier:=fun a v=>if h : v < w+1 then
    DescentTerminalPackedSeedFlags.pin X R s w ([]:List (Source A)) seed a ⟨v,h⟩ else Sum.inr false
  headerPin w lo C grain ss earlier i.1.val i.2.val

def packedImage (origin : ℕ) (x : Fin e→ Plane j r→ Fin t→ Bool) (z : A⊕Hidden e j r t→ Bool) :=
  image lowEnd origin (original X R s w seed (z∘Sum.inl) lo C grain ss) x (z∘Sum.inr)

theorem packed_read (origin : ℕ) (x : Fin e→ Plane j r→ Fin t→ Bool) (z : A⊕Hidden e j r t→ Bool)
    (sep : lowEnd ≤ origin) (room : 2^j*t ≤ w) (positive : 0 < grain)
    (fits : ∀a∈ss,DescentTerminalEpochBits.width a.C*grain ≤ w) (ij : Fin (origin+17*H)×Fin (w+1)) :
    (pin lowEnd origin (packedPin X R s w seed lo C grain ss) ij).elim (assign x z) id=
      TraceWords.bits (TraceBanks.wide (packedImage X R s w seed lo C grain ss origin x z ij.1.val)) ij.2 := by
  apply pin_read _ _ _ _ x z sep room _ ij
  intro i
  exact installed_bits X R s w seed (z∘Sum.inl) lo C grain ss positive fits i.1.val i.1.isLt i.2

theorem packed_original (origin : ℕ) (x : Fin e→ Plane j r→ Fin t→ Bool) (z : A⊕Hidden e j r t→ Bool)
    (sep : lowEnd ≤ origin) {a : ℕ} (small : a < lowEnd) :
    packedImage X R s w seed lo C grain ss origin x z a=original X R s w seed (z∘Sum.inl) lo C grain ss a :=
  low _ _ _ _ _ sep small

end
end Hierarchy.DescentExteriorShelf.Root

end OAI
