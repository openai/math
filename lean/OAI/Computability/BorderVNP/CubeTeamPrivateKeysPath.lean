import OAI.Computability.BorderVNP.CubeTeamPrivateKeysNative

/-! # Recovering the distributed cube assignment from all native team tapes

For fixed selectors, an arbitrary strict crossing suffix and arbitrary private
team tapes of their exact lengths have one joint physical realization. Repeating
this fiber equivalence over selectors yields a bijection on entire cube paths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Crossing Physical
open scoped Classical

variable {n d blocks b h K s : ℕ} {Team : Type*} [DecidableEq Team]
variable {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)} {owner : Fin d → Team}

/-- The common half of the complete native encoding uses exactly the actual
shared crossing streams of every strict unordered row. -/
theorem nativeWordsEquiv_shared (f : Assignment.Choices b s select i owner) (pair : Symbols d) :
    (((nativeWordsEquiv b s select i owner) f).1 pair).val =
      commonCrossings b i pair select (Assignment.supplies f) (fun z => Assignment.lookup f (.inl z)) :=
  choiceWordsEquiv_shared b s select i owner f pair

/-- Every choice of shared row words and chronological native team tapes of
the proper lengths has exactly one physical assignment on the routing fibers. -/
theorem existsUnique_dispatch_assignment (code : Team ↪ ℕ) (layouts : Team → TeamRowPrepare.Layout)
    (dimensions : ∀ t, (layouts t).d = d) (ids : ∀ t, (layouts t).teamID = code t)
    (packetBase singleBase : Team → ℕ) (common : StrictCrossWords b s select i)
    (localWords : TeamPrivateWords b s select i owner) :
    ∃! f : Assignment.Choices b s select i owner,
      (∀ pair, commonCrossings b i pair select (Assignment.supplies f) (fun z => Assignment.lookup f (.inl z)) =
        (common pair).val) ∧ ∀ t, TeamRows.choices (layouts t) (TeamRows.wordOwner (code ∘ owner))
          ((Assignment.bankData f (packetBase t) (singleBase t)).privateTapeAt (layouts t)) = (localWords t).val := by
  let e := nativeWordsEquiv b s select i owner
  have equiv (f : Assignment.Choices b s select i owner) :
      ((∀ pair, commonCrossings b i pair select (Assignment.supplies f) (fun z => Assignment.lookup f (.inl z)) =
        (common pair).val) ∧ ∀ t, TeamRows.choices (layouts t) (TeamRows.wordOwner (code ∘ owner))
        ((Assignment.bankData f (packetBase t) (singleBase t)).privateTapeAt (layouts t)) = (localWords t).val) ↔
      e f = (common,localWords) := by
    constructor
    · rintro ⟨shared,localEq⟩
      apply Prod.ext
      · funext pair
        exact Subtype.ext ((nativeWordsEquiv_shared f pair).trans (shared pair))
      · funext t
        exact Subtype.ext ((nativeWordsEquiv_teamRows code f t (layouts t) (dimensions t) (ids t)
          (packetBase t) (singleBase t)).trans (localEq t))
    · intro eq
      constructor
      · intro pair
        exact (nativeWordsEquiv_shared f pair).symm.trans (congrArg (fun x => (x.1 pair).val) eq)
      · intro t
        exact (nativeWordsEquiv_teamRows code f t (layouts t) (dimensions t) (ids t)
          (packetBase t) (singleBase t)).symm.trans (congrArg (fun x => (x.2 t).val) eq)
  exact ⟨e.symm (common,localWords),(equiv _).mpr (e.apply_symm_apply _),
    fun f hf => e.injective (((equiv f).mp hf).trans (e.apply_symm_apply _).symm)⟩

/-- Reindex the entire path: carry private host bits and selectors, then use the
actual common-row suffixes and arbitrary chronological words of the greedy
team owners for that selector tuple. -/
noncomputable def pathWordsEquiv {D : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
    (N : Network D P bits) (cell : N.Site → Cell) (n d blocks b h K s : ℕ)
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team) :
    Path N cell n d blocks b h K s ≃
      (∀ c, N.InsideAssignment cell c) ×
        ((u : Packet n d blocks → Selector n K h) ×
          StrictCrossWords b s u (chosen b s u) × TeamPrivateWords b s u (chosen b s u) (owners u)) :=
  (Assignment.adaptivePathEquiv N cell n d blocks b h K s owners).trans
    ((Equiv.refl _).prodCongr (Equiv.sigmaCongrRight fun u => nativeWordsEquiv b s u (chosen b s u) (owners u)))

end Cube.Scatter

end BorderVNP
end Computability
end OAI
