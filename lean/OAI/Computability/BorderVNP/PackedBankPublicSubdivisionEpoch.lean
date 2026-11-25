import OAI.Computability.BorderVNP.PackedBankPublicSubdivision
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites
import OAI.Computability.BorderVNP.PackedSiteRecords
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseExecutionRecords

/-! # Public record cap at the actual inputs of an enriched epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

open Cover Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited
open Subdivision PhysicalEpochs Diagonal.ExternalSew PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

private theorem subdivision_within {D d a m n np : ℕ} {P I K : Type} [fin : Fintype P] (outFin : Fintype P) [Fintype I] [Field K]
    {bits : P → ℕ} {L δ : ℝ} {hδ : 0 < δ} {leaf : PlacedPack D P bits K I d} (s : InitialSites leaf L hδ)
    {input : Pack D P bits K} (route : SiteRoutes input I a L)
    (hd : d = a) (hp : s.pack = input) (hr : HEq s.routes route)
    (old : @Site.Programs D P fin bits input.layout) (oldID : s.pack.layout.Edge ↪ Fin m)
    (newID : (s.pack.layout.subdivide (s.routes.routes δ)).Edge ↪ Fin n) (portID : P ↪ Fin np)
    (ex : Bool) (B : ℕ) (hc : @SiteCap D K P I fin _ bits a L input route (@publicProgramData D P fin bits _ old) ex B) :
    let prior := @samePrivatePrograms D P fin bits _ _ (congrArg Pack.layout hp.symm) old
    let next := @subdividePrivatePrograms D m n np P outFin bits s.pack.layout (s.routes.routes δ) oldID newID portID
      (changePrivateInstance s.pack.layout (fin := fin) (fin' := outFin) prior)
    let actual := @samePrivatePrograms D P outFin bits _ _ (congrArg (fun q => q.pack.layout) s.realizes.symm) next
    @RecordsWithin D d P I outFin _ bits K leaf (@publicProgramData D P outFin bits _ actual) ex
      (1040*(1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L δ)))*B) := by
  obtain rfl : outFin = fin := Subsingleton.elim _ _
  subst a
  subst input
  obtain rfl := eq_of_heq hr
  rcases s with ⟨input,r,rfl⟩
  let init : InitialSites (r.initialPlacedPack hδ) L hδ := ⟨input,r,rfl⟩
  have pos := hc 1
  have shift : 1+(B-1) = B := by omega
  have bound := init.installedBankPrograms_within oldID newID portID old (publicProgramData old)
    (fun _ => le_rfl) ex (fun _ _ => le_rfl) (B-1) (fun t => Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using hc t))
  rw [shift,←Nat.mul_assoc] at bound
  exact bound

universe u

variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} {t : ℕ} {ht : t<T}
    {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (rows : E.F.SiteRows)
    (c : Fin (fan S) → Admissible good t) (old : ∀ i, Site.Programs (c i).val.pack.layout)

set_option maxHeartbeats 1400000 in
/-- Record cap in either mode of the native subdivision on this child, using its own physical cable
numbering, its routed insertion sites, and the saved layout of the epoch's actual leaf. -/
theorem installedPrivatePrograms_bank_within (ex : Bool) (B : ℕ)
    (cap : ∀ i, SiteCap (c i).val.route (publicProgramData (old i)) ex B) (i : Fin (fan S)) :
    RecordsWithin (E.view 0 ((E.run c).flat i)) (publicProgramData (E.installedPrivatePrograms rows c old i)) ex
      (1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius)))*B) := by
  let run := E.run c
  let s := run.initialSites i
  let raw := RowTrace.sameRows (congrArg Pack.layout (run.originalPack i).symm) (c i).val.rows
  let new := raw.siteRoutes s.routes S.radius
  have hd := (S.start_level (offset S start t)).trans (levels S deep ht).2.2
  have hr := (run.originalRoutes i).trans (reindexRoutes_heq (levels S deep ht).2.2.symm (c i).val.route)
  exact subdivision_within (P := Port (fan S) P t) (fin := portFintype (P := P) (k := fan S) (b := t))
    (portFintype (P := Port (fan S) P t) (k := S.fanIn) (b := 0)) s (c i).val.route hd (run.originalPack i) hr (old i)
    raw.edge new.edge (rows.ports 0) ex B (cap i)

/-- Public tile cap of the native subdivision on this child, using its own physical cable
numbering, its routed insertion sites, and the saved layout of the epoch's actual leaf. -/
theorem installedPrivatePrograms_public_within (B : ℕ)
    (cap : ∀ i, SiteCap (c i).val.route (publicProgramData (old i)) false B) (i : Fin (fan S)) :
    RecordsWithin (E.view 0 ((E.run c).flat i)) (publicProgramData (E.installedPrivatePrograms rows c old i)) false
      (1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius)))*B) :=
  E.installedPrivatePrograms_bank_within rows c old false B cap i

end PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

end BorderVNP
end Computability
end OAI
