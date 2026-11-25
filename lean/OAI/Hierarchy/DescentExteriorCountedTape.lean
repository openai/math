import OAI.Hierarchy.DescentExteriorAppendedWords
import OAI.Hierarchy.DescentExteriorPackedRoot

namespace OAI
/-! # Consecutive original input words after both exterior proposals -/
namespace Hierarchy.DescentExteriorShelf.Root
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentExterior Computability.VPVNP.BurstRAM ThreeFlat.Diagonal Catalyst Computability.BorderVNP.Crossing
open ProtocolRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.RAMMemory (initialMemory)
open scoped Fin.CommRing
noncomputable section
variable {w : ℕ}

variable {F A : Type} [Field F] {k n e j r t : ℕ} (X : Approximation F k n) (R s w : ℕ)
variable (seed : Select X R s→A) (lo C grain : ℕ) (ss : List (Source A))
set_option quotPrecheck false
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "base_" => DescentTerminalPackedSeedFlags.endInput X R s w ([] : List (Source A))
local notation "N" => DescentPackedSeed.rows X R s w
local notation "check" => DescentTerminalPackedSeedFlags.check X R s w ([] : List (Source A))
variable (origin : ℕ) (x : Fin e→Plane j r→Fin t→Bool) (z : A⊕Hidden e j r t→Bool)
local notation "front" => packedImage X R s w seed lo C grain ss origin x z
local notation "extent_" => origin+17*span j r t e

def countedAt (raw : Memory w) : Memory w :=
  DescentPackedRejection.after (M:=DescentPackedSeed.multiplicity w s) base_ (DescentTerminalPackedSeedFlags.predicate s)
    (DescentPackedSeed.cells X ((z∘Sum.inl)∘seed)) raw

theorem counted_on (raw : Memory w) (fixed : ∀a<extent_,raw a=front a)
    (wide : 2*digitsNeeded s ≤ w) (seedFits : base_+(N+1)<2^w)
    (next : base_+(N+1) ≤ lo) (sep : lowEnd ≤ origin) :
    let o:=countedAt X R s w seed z raw
    (check).Exec raw o (4+(N+1)*66) ∧ CheapCode check ∧
    (o (base_+N)=0 ↔ DescentSeedRoot.valid X ((z∘Sum.inl)∘seed)) ∧
    Loaded origin (fun _=>LinearEquiv.refl _ _) x (z∘Sum.inr) o ∧ ∀a,a< base_ ∨ base_+(N+1) ≤ a→ o a=raw a := by
  have ext : lo ≤ lowEnd:=by dsimp only [end_,dict];omega
  have basis:=seed_exact_on X R s w seed (z∘Sum.inl) lo C grain ss raw wide seedFits next
    (fun a ha=>(fixed a (by omega)).trans (packed_original X R s w seed lo C grain ss origin x z sep (by omega)))
  refine ⟨basis.1,basis.2.1,basis.2.2.1,?_,basis.2.2.2⟩
  intro col idx hi
  have h:=col.isLt
  have before:=Nat.mul_le_mul_right (span j r t e) (show col.val+1≤17 by omega)
  rw [Nat.succ_mul] at before
  have endpoint : origin+col.val*span j r t e+idx<extent_:=by omega
  exact (basis.2.2.2 _ (.inr (by change base_+(N+1)≤ origin+col.val*span j r t e+idx;omega))).trans
    ((fixed _ endpoint).trans (loaded lowEnd origin _ x (z∘Sum.inr) col idx hi))

end
end Hierarchy.DescentExteriorShelf.Root

end OAI
