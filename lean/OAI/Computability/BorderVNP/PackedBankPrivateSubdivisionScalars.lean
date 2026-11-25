import OAI.Computability.BorderVNP.PackedBankInheritedScalarBounds
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites

/-! # Scalar words in the installed subdivision programs

The new endpoint fields address intervals in the extended site bank.
A relay stores the two intrinsic hop addresses and their common width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Crossing CellSparse
open scoped Classical

variable {D m n np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (routes : N.WireRoutes) (oldID : N.Edge ↪ Fin m)
    (newID : (N.subdivide routes).Edge ↪ Fin n) (portID : P ↪ Fin np)
local notation "G" => N.subdivide routes

private theorem relay_scalarBound (j : (e : N.Edge) × Fin (routes.interior e)) :
    (relaySite N routes newID portID j).ScalarBound (max 1 (relaySite N routes newID portID j).size) := by
  intro a ha
  obtain ⟨r,hr,ha⟩ := List.mem_flatMap.mp ha
  have eqn : r = relayRecord N routes newID portID j := by simpa [relaySite,Site.rows] using hr
  subst r
  let left := wireStart G newID portID (.inr j) (leftHop N routes j)
  let right := wireStart G newID portID (.inr j) (rightHop N routes j)
  let inc := incoming G (.inr j)
  have hl : left + N.width j.1 ≤ inc := wireEnd_le G newID portID (.inr j) (leftHop N routes j)
  have hr : right + N.width j.1 ≤ inc := wireEnd_le G newID portID (.inr j) (rightHop N routes j)
  change a ∈ [(Kind.plain,1),(.plain,1),(.plain,N.width j.1),(.bitAddress,left),
    (.plain,0),(.plain,1),(.bitAddress,right),(.plain,0),(.plain,1)] at ha
  change a.2 ≤ max 1 (0+inc)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- Retention bounds each new scalar by the extended size. At a relay the width and both
hop bases fit in its current incidence bank, also for zero-width words. -/
theorem subdividePrivatePrograms_scalarBound (old : Site.Programs N) (U : ℕ)
    (bound : ∀ v, (old v).program.ScalarBound (max U (max 1 (old v).program.size))) (z : (G).Site) :
    let s := (subdividePrivatePrograms N routes oldID newID portID old z).program
    s.ScalarBound (max U (max 1 s.size)) := by
  dsimp only
  cases z with
  | inl v =>
    let s := (old v).program
    let inc := incoming G (.inl v)
    let fits := covers N routes v oldID newID portID
    have h := s.scalarBound_retain (n := inc) (bound v)
      (fun p hp => (fits.oldFit p hp).trans (old v).size.symm.le) fits.newFit
    intro a ha
    have val := h a ha
    change a.2 ≤ max (max U (max 1 s.size)) (max 1 (s.size+inc)) at val
    change a.2 ≤ max U (max 1 (s.size+inc))
    omega
  | inr j =>
    intro a ha
    exact (relay_scalarBound N routes newID portID j a ha).trans (le_max_right ..)

end Packing.Inherited.Subdivision

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

open Cover Crossing BorderVNP.Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
open Subdivision Diagonal.ExternalSew PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

private theorem same_scalarBound {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N M : Network D P bits}
    (eqn : N = M) (old : Site.Programs N) (U : ℕ)
    (bound : ∀ v, (old v).program.ScalarBound (max U (max 1 (old v).program.size))) (v : M.Site) :
    let s := (samePrivatePrograms eqn old v).program
    s.ScalarBound (max U (max 1 s.size)) := by
  subst M
  exact bound v

universe u
variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} {t : ℕ} {ht : t<T}
    {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (rows : E.F.SiteRows)
    (c : Fin (fan S) → Admissible good t) (old : ∀ i, Site.Programs (c i).val.pack.layout)

set_option maxHeartbeats 1600000 in
/-- The scalar invariant follows the actual child rows, subdivision and saved network of
this enriched epoch, with the full current site extent at each installed leaf program. -/
theorem installedPrivatePrograms_scalarBound (U : ℕ)
    (bound : ∀ i v, (old i v).program.ScalarBound (max U (max 1 (old i v).program.size)))
    (i : Fin (fan S)) (v : (E.view 0 ((E.run c).flat i)).pack.layout.Site) :
    let s := (E.installedPrivatePrograms rows c old i v).program
    s.ScalarBound (max U (max 1 s.size)) := by
  let run := E.run c
  let a := run.initialSites i
  let orig := congrArg Pack.layout (run.originalPack i).symm
  let saved := congrArg (fun p => p.pack.layout) a.realizes.symm
  let raw := RowTrace.sameRows orig (c i).val.rows
  let new := raw.siteRoutes a.routes S.radius
  let prior := samePrivatePrograms orig (old i)
  let changed := changePrivateInstance (fin' := portFintype (P := Port (fan S) P t) (k := S.fanIn) (b := 0))
    a.pack.layout prior
  have cap (u) : (changed u).program.ScalarBound (max U (max 1 (changed u).program.size)) :=
    same_scalarBound orig (old i) U (bound i) u
  let installed := subdividePrivatePrograms a.pack.layout (a.routes.routes S.radius)
    raw.edge new.edge (rows.ports 0) changed
  exact same_scalarBound saved installed U
    (subdividePrivatePrograms_scalarBound a.pack.layout (a.routes.routes S.radius)
      raw.edge new.edge (rows.ports 0) changed U cap) v

end PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

end BorderVNP
end Computability
end OAI
