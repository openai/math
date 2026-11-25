import OAI.Hierarchy.DescentExteriorPackedRoot
import OAI.Hierarchy.DescentExteriorPublished

namespace OAI
/-! # The paid packed seed validator preserves the public and both guessed exterior flights -/
namespace Hierarchy.DescentExteriorShelf.Root
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentExterior DescentGL Computability.VPVNP.BurstRAM ThreeFlat.Diagonal Catalyst Computability.BorderVNP.Crossing
open ProtocolRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
variable {F A : Type} [Field F] {k n e j r t : ℕ} (X : Approximation F k n) (R s w : ℕ)
variable (seed : Select X R s→ A) (lo C grain : ℕ) (ss : List (Source A))
set_option quotPrecheck false
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "base_" => DescentTerminalPackedSeedFlags.endInput X R s w ([] : List (Source A))
local notation "N" => DescentPackedSeed.rows X R s w
variable (origin : ℕ) (x : Fin e→Plane j r→Fin t→Bool) (z : A⊕Hidden e j r t→Bool)
local notation "prior" => packedImage X R s w seed lo C grain ss origin x z
local notation "check" => DescentTerminalPackedSeedFlags.check X R s w ([] : List (Source A))

def counted : Memory w :=
  DescentPackedRejection.after (M:=DescentPackedSeed.multiplicity w s) base_ (DescentTerminalPackedSeedFlags.predicate s)
    (DescentPackedSeed.cells X ((z∘Sum.inl)∘seed)) prior

theorem counted_run (wide : 2*digitsNeeded s ≤ w) (seedFits : base_+(N+1) < 2^w)
    (next : base_+(N+1) ≤ lo) (sep : lowEnd ≤ origin) :
    let o:=counted X R s w seed lo C grain ss origin x z
    (check).Exec prior o (4+(N+1)*66) ∧ CheapCode check ∧
    (o (base_+N)=0 ↔ DescentSeedRoot.valid X ((z∘Sum.inl)∘seed)) ∧
    Loaded origin (fun _=>LinearEquiv.refl _ _) x (z∘Sum.inr) o ∧
    ∀a,a < base_ ∨ base_+(N+1) ≤ a → o a=prior a := by
  have extent_ : lo ≤ lowEnd:=by dsimp only [end_,dict];omega
  have run:=seed_exact_on X R s w seed (z∘Sum.inl) lo C grain ss prior wide seedFits next
    (fun a small=>packed_original X R s w seed lo C grain ss origin x z sep (by omega))
  refine ⟨run.1,run.2.1,run.2.2.1,?_,run.2.2.2⟩
  intro col idx live
  rw [show counted X R s w seed lo C grain ss origin x z ((bank j r t e origin col.val).base+idx)=_ from
    run.2.2.2 _ (.inr (by change base_+(N+1) ≤ origin+col.val*span j r t e+idx;omega))]
  exact loaded lowEnd origin _ x (z∘Sum.inr) col idx live

end
end Hierarchy.DescentExteriorShelf.Root

end OAI
