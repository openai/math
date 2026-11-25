import OAI.Hierarchy.DescentWideSeedFlags
import OAI.Hierarchy.DescentEpochVoteHeader
import OAI.Hierarchy.DescentExteriorVoteImage

namespace OAI
/-! # Counting the original stamped ballot with both exterior proposals in memory -/
namespace Hierarchy.DescentExteriorShelf.Root
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentExterior DescentGL Computability.VPVNP.BurstRAM Catalyst Computability.BorderVNP.Crossing
open ProtocolRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F A : Type} [Field F] {k n e j r t : ℕ} (X : Approximation F k n) (R s payload bw : ℕ)
variable (seed : Select X R s → A) (lo C grain : ℕ) (ss : List (Source A))
set_option quotPrecheck false
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "H" => span j r t e
local notation "flag" => DescentWideSeedFlags.initial X R s payload bw seed
local notation "base_" => DescentWideSeedFlags.endInput X R s payload
local notation "cnt" => DescentPackedSeed.rows X R s payload

def wideOriginal (z : A → Bool) := header lo C grain ss z (flag z)

variable (origin : ℕ) (x : Fin e → Plane j r → Fin t → Bool) (z : A ⊕ Hidden e j r t → Bool)

def widePackedImage :=
  image lowEnd origin (wideOriginal X R s payload bw seed lo C grain ss (z∘Sum.inl)) x (z∘Sum.inr)

theorem widePacked_original (sep : lowEnd ≤ origin) {a : ℕ} (small : a < lowEnd) :
    widePackedImage X R s payload bw seed lo C grain ss origin x z a =
      wideOriginal X R s payload bw seed lo C grain ss (z ∘ Sum.inl) a :=
  low _ _ _ _ _ sep small

theorem wideCounted_on (raw : Memory bw)
    (fixed : ∀a < origin+17*H,raw a=widePackedImage X R s payload bw seed lo C grain ss origin x z a)
    (wide : 2*digitsNeeded s ≤ payload) (room : base_+(cnt+1)<2^bw)
    (next : base_+(cnt+1) ≤ lo) (sep : lowEnd ≤ origin) :
    let o:=DescentWideSeedFlags.countedAt X R s payload seed (z ∘ Sum.inl) raw
    let check:=DescentWideSeedFlags.check X R s payload bw
    check.Exec raw o (4+(cnt+1)*66) ∧ CheapCode check ∧ (o (base_+cnt)=0 ↔ valid X ((z ∘ Sum.inl) ∘ seed)) ∧
      Loaded origin (fun _=>LinearEquiv.refl _ _) x (z ∘ Sum.inr) o ∧
      ∀a,a < base_ ∨ base_+(cnt+1) ≤ a → o a=raw a := by
  have ext : lo ≤ lowEnd:=by dsimp only [end_,dict];omega
  have executed:=DescentWideSeedFlags.run X R s payload bw seed (z∘Sum.inl) raw (fun a ha=>
    (fixed _ (by omega)).trans ((widePacked_original X R s payload bw seed lo C grain ss origin x z sep (by omega)).trans
      (frame lo C grain ss _ _ (by omega)))) wide room
  refine ⟨executed.1,executed.2.1,executed.2.2.1,?_,executed.2.2.2⟩
  intro col idx hi
  have bound:=Nat.mul_le_mul_right (span j r t e) (show col.val+1≤17 by have := col.isLt;omega)
  rw [Nat.succ_mul] at bound
  have reach : origin+col.val*span j r t e+idx < origin+17*H:=by omega
  exact (executed.2.2.2 _ (.inr (by change base_+(cnt+1) ≤ origin+col.val*span j r t e+idx;omega))).trans
    ((fixed _ reach).trans (loaded lowEnd origin _ x (z∘Sum.inr) col idx hi))

end
end Hierarchy.DescentExteriorShelf.Root

end OAI
