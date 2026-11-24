import OAI.Computability.VPVNP.CursorBranchCommunication
import OAI.Computability.VPVNP.PairShrinkRoleChild
import OAI.Computability.VPVNP.PairSimulationAssembly

/-! # Bounds on the selected shrinking child arguments

The shrinking reader enumerates the placement fiber at its output site.
The pass's record bound limits the length of that enumeration, and each
old site's two sets of half-wires contribute at most twice the old degree
times the maximum wire width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.ChildArguments

open Compression LocalHistory NodeArguments

theorem demand_le {a g : ℕ} (X : State a g) (sites : List X.network.Site) :
    demand X sites ≤ sites.length * (2 * 2 ^ a * X.maxWireWidth) := by
  induction sites with
  | nil => simp [demand]
  | cons u us ih =>
    have first : width X u ≤ 2 * 2 ^ a * X.maxWireWidth := by
      rw [width, ChildSlots.length_all]
      exact CursorNetwork.incidentBits_le X u
    change width X u + demand X us ≤ (us.length + 1) * _
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (us.length * _)]
    exact Nat.add_le_add first ih

variable {K R : Type*} [Field K] [CommRing R] {S : BlockSchedule K}

/-- The descriptor of the actual scheduled term fits the fixed record limit.
Its input bit demand grows linearly with the current state's maximum wire width. -/
theorem selected_budget (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)
    (i : Fin S.steps) {g w : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (sel : X.ShrinkSelection B.shrink)
    (v : (X.Base × BitWord (packingTagBits (2 ^ S.degreeExponent i.castSucc))) × BitWord g)
    (desc : Descriptor w X)
    (order : desc.sites = List.ofFn fun j =>
      ((((shrinkPassReaders B f hf i rfl X).order sel).children v).entries j).val) :
    desc.sites.length ≤ B.recordLimit ∧
      demand X desc.sites ≤
        (2 * 2 ^ S.degreeExponent i.castSucc * B.recordLimit) * X.maxWireWidth := by
  classical
  have card := Fintype.card_congr
    (((shrinkPassReaders B f hf i rfl X).order sel).children v).entries
  rw [Fintype.card_fin] at card
  have records := (X.shrinkStatePass_bounded B.shrink (f ∘ Sum.inl)
    ((B.solution_iff f).mp hf).1 (S.shrink i) sel).1 v
  have factor := Finset.le_sup (f := fun j : Fin S.steps =>
    State.shrinkHistoryFactor B.shrink (S.degreeExponent j.castSucc) (S.degreeExponent j.succ))
    (Finset.mem_univ i)
  have count : desc.sites.length ≤ B.recordLimit := by
    rw [order, List.length_ofFn, card]
    exact (Nat.le_add_left _ _).trans (records.trans (factor.trans
      ((le_max_left ..).trans (le_max_right ..))))
  refine ⟨count, (demand_le X desc.sites).trans ?_⟩
  calc
    _ ≤ B.recordLimit * (2 * 2 ^ S.degreeExponent i.castSucc * X.maxWireWidth) :=
      Nat.mul_le_mul_right _ count
    _ = _ := by ac_rfl

end PairSimulation.ShrinkRole.ChildArguments

end VPVNP
end Computability
end OAI
