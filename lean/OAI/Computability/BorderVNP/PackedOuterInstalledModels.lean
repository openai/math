import OAI.Computability.BorderVNP.PackedOuterSiteFieldRows
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites

/-! # Field factors on each actual routed subdivision

Both ends of an original cable are staged in the true physical incidence
order. New intermediate sites impose their equality guard. The prior field
models are transported through the original pack and saved placement equalities.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Programs

open Crossing Shortening

variable {D ne np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {K : Type*} [Field K]
    (p : Pack D P bits K) (edge : p.layout.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (s : Site.Programs p.layout) (values : ℕ → K)

/-- Equal capacities and occupied ordinals preserve every field model in the new naming. -/
theorem FieldModels.renumber {nf nq : ℕ} (model : FieldModels p edge port s values)
    (next : p.layout.Edge ↪ Fin nf) (ports : P ↪ Fin nq) (cap : nf = ne) (pcap : nq = np)
    (hc : ∀ z, (next z).val = (edge z).val) (hp : ∀ z, (ports z).val = (port z).val) :
    FieldModels p next ports s values := by
  subst nf; subst nq
  obtain rfl : next = edge := DFunLike.ext _ _ fun z => Fin.ext (hc z)
  obtain rfl : ports = port := DFunLike.ext _ _ fun z => Fin.ext (hp z)
  exact model

/-- Reconcile the finite enumeration of nested ports with the enumeration at the outer boundary. -/
theorem FieldModels.changePrivate {D ne np : ℕ} {P : Type} {bits : P → ℕ} {K : Type} [Field K]
    (f g : Fintype P) (p : Pack D P bits K) (edge : p.layout.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (programs : @Site.Programs D P f bits p.layout) (values : ℕ → K)
    (model : @FieldModels D ne np K _ P f bits p edge port programs values) :
    @FieldModels D ne np K _ P g bits p edge port
      (BorderVNP.PackedHistoryCircuit.Normalized.EnrichedOuter.changePrivateInstance p.layout programs) values := by
  obtain rfl : g = f := Subsingleton.elim _ _
  exact model

/-- The genuine subdivision field model follows from the current programs' locality,
even if their initial private fibers have many successful guesses. -/
theorem FieldModels.subdivide {nf : ℕ} (route : p.layout.WireRoutes) (next : (p.layout.subdivide route).Edge ↪ Fin nf)
    (model : FieldModels p edge port s values) :
    let out : Pack D P bits K := ⟨p.layout.subdivide route,p.layout.subdivideTables route p.table⟩
    FieldModels out next port (Subdivision.subdividePrivatePrograms p.layout route edge next port s) values := by
  intro out v
  rcases v with v | j
  · exact ⟨(s v).program.local_retain (model v).1 _ _ ((Subdivision.covers p.layout route v edge next port).castOld (s v).size),
      Subdivision.original_models p.layout route v edge next port p.table (s v).program (s v).size (model v).1
        (fieldWeight values) (model v).2⟩
  · exact ⟨Subdivision.relay_local p.layout route next port j,Subdivision.relay_models p.layout route next port j
      (fieldWeight values) (by simp [fieldWeight]) p.table⟩

end Packing.Inherited.Site.Programs

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

open Diagonal.ExternalSew Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

private theorem model_same {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {K : Type} [Field K]
    {sh : Shape} {np : ℕ} {p q : Pack D P bits K} (h : p = q) (old : Rows sh p.layout) (port : P ↪ Fin np)
    (s : Site.Programs p.layout) (values : ℕ → K) (model : Site.Programs.FieldModels p old.edge port s values) :
    Site.Programs.FieldModels q (RowTrace.sameRows (congrArg Pack.layout h) old).edge port
      (samePrivatePrograms (congrArg Pack.layout h) s) values := by
  subst q
  exact model

universe u
variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P]
    {bits : P → ℕ} {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (rows : E.F.SiteRows)
    {oldCap newCap : ℕ} (oldPort : Port (fan S) P t ↪ Fin oldCap)
    (nextPort : Port (fan S) P (t+1) ↪ Fin newCap) (fieldRows : E.FieldRows rows oldPort nextPort)
    (c : Fin (fan S) → Admissible good t) (old : ∀ j, Site.Programs (c j).val.pack.layout)
    (values : ℕ → K) (childModels : ∀ j, Site.Programs.FieldModels (c j).val.pack (c j).val.rows.edge oldPort (old j) values)

include childModels in
/-- The actual installed inner leaf programs realize the field-valued routed subdivision. -/
theorem installedPrivatePrograms_models (i : Fin (fan S)) :
    Site.Programs.FieldModels (E.view 0 ((E.run c).flat i)).pack (fieldRows.layout.edges 0 ((E.run c).flat i))
      (rows.ports 0) (E.installedPrivatePrograms rows c old i) values := by
  let run := E.run c
  let a := run.initialSites i
  let orig := congrArg Pack.layout (run.originalPack i).symm
  let raw := RowTrace.sameRows orig (c i).val.rows
  let new := raw.siteRoutes a.routes S.radius
  let prior := samePrivatePrograms orig (old i)
  let f₀ := portFintype (k := fan S) (P := P) (b := t)
  let f₁ := portFintype (k := S.fanIn) (P := Port (fan S) P t) (b := 0)
  let port₀ : Port (fan S) P t ↪ Fin (rows.nPort 0) := rows.ports 0
  let sub := Subdivision.subdividePrivatePrograms a.pack.layout (a.routes.routes S.radius) raw.edge new.edge (rows.ports 0)
    (changePrivateInstance _ prior)
  have base := Site.Programs.FieldModels.renumber (c i).val.pack (c i).val.rows.edge oldPort (old i) values
    (childModels i) (c i).val.rows.edge port₀ rfl fieldRows.inputPortCap (fun _ => rfl) fieldRows.inputPorts
  have ho := model_same (run.originalPack i).symm (c i).val.rows port₀ (old i) values base
  have changed := Site.Programs.FieldModels.changePrivate f₀ f₁ a.pack raw.edge port₀ prior values ho
  have hs := Site.Programs.FieldModels.subdivide a.pack raw.edge (rows.ports 0) (changePrivateInstance _ prior) values
    (a.routes.routes S.radius) new.edge changed
  have saved := model_same (congrArg PlacedPack.pack a.realizes.symm) new (rows.ports 0) sub values hs
  exact Site.Programs.FieldModels.renumber (E.view 0 (run.flat i)).pack (E.installedFieldRows c i).edge
    (rows.ports 0) (E.installedPrivatePrograms rows c old i) values saved _ _ (fieldRows.inputCap c) rfl
    (fieldRows.inputRows c i) (fun _ => rfl)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

end BorderVNP
end Computability
end OAI
