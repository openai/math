import OAI.Computability.BorderVNP.DiagonalNativeBirthInputs
import OAI.Computability.BorderVNP.DiagonalTrackedSubdivisionRead
import OAI.Computability.BorderVNP.DiagonalOuterPowerHosts
import OAI.Computability.BorderVNP.PackedOuterSiteFieldRows
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites

/-! # Physical birth words on the installed endpoint subdivision -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Lineage

open Crossing Shortening Diagonal.CellEntries Diagonal.ExternalSew PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity DirectoryCircuit Site.Programs
open private sameStorage from OAI.Computability.BorderVNP.DiagonalSiteExecution
open scoped Classical

variable {D ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (edges : N.Edge ↪ Fin ne) (ports : P ↪ Fin np)
    (progs : Site.Programs N)

/-- The zero-level and parent port enumerations sort the same incoming fields. -/
theorem birthInput_instance {D ne np : ℕ} {P : Type} {bits : P → ℕ} (f g : Fintype P)
    (N : Network D P bits) (edges : N.Edge ↪ Fin ne) (ports : P ↪ Fin np)
    (progs : @Site.Programs D P f bits N) (v : N.Site) (x : PowerInput N) :
    @birthInput D ne np P g bits N edges ports v (@changePrivateInstance D P bits N f g progs v) x =
      @birthInput D ne np P f bits N edges ports v (progs v) x := by
  obtain rfl : g = f := Subsingleton.elim _ _
  rfl

/-- A saved layout equality transports the numerical input together with its checker. -/
theorem birthInput_same {Q : Network D P bits} {sh : Shape} (h : N = Q)
    (rows : Rows sh N) (v : N.Site) (x : PowerInput Q) :
    birthInput Q (RowTrace.sameRows h rows).edge ports ((Retains.ofEq h).site v)
      (samePrivatePrograms h progs _) x =
      birthInput N rows.edge ports v (progs v) ((sameStorage h).powerInput x) := by
  subst Q
  rfl

/-- Changing the ambient port capacity preserves the word when its occupied numeric names agree. -/
theorem birthInput_portNumbered {np' : ℕ} (ports' : P ↪ Fin np') (cap : np' = np)
    (names : ∀ a, (ports' a).val = (ports a).val) (v : N.Site) (x : PowerInput N) :
    birthInput N edges ports' v (progs v) x = birthInput N edges ports v (progs v) x := by
  subst np'
  obtain rfl : ports' = ports := DFunLike.ext _ _ fun a => Fin.ext (names a)
  rfl

/-- The ordered subdivision cuts deliver the actual first or last hop selected at
the retained endpoint, also when a cable loops back to the same original site. -/
theorem birthInput_subdivide {nc : ℕ} (route : N.WireRoutes) (next : (N.subdivide route).Edge ↪ Fin nc)
    (v : N.Site) (x : PowerInput (N.subdivide route)) :
    birthInput (N.subdivide route) next ports (.inl v)
      (Subdivision.subdividePrivatePrograms N route edges next ports progs (.inl v)) x =
      birthInput N edges ports v (progs v) (x.beforeSubdivision route v) := by
  let wire := fun e : Incident (N.subdivide route) (.inl v) => x.edges e.val
  let port := fun p : Attached (N.subdivide route) (.inl v) => x.ports p.val
  have same : Subdivision.oldWires N route v wire = fun u : Incident N v => (x.beforeSubdivision route v).edges u.val := by
    funext e j
    by_cases h : N.src e.val = v <;> simp [Subdivision.oldWires,PowerInput.beforeSubdivision,h,wire]
  exact congrArg (fun a => extendWork ((progs v).retention.readInput (a ∘ Fin.cast (progs v).size)))
    ((Subdivision.read_inputs N route v edges next ports wire port).trans
      (congrArg (fun z => inputWords N edges ports v z (Subdivision.oldPorts N route v port)) same))

end Packing.Inherited.Site.Lineage

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

open Diagonal.ExternalSew Diagonal.CellEntries Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive
open Packing Packing.Inherited Site.Lineage PublicCapacity
open private sameHost from OAI.Computability.BorderVNP.DiagonalOuterPowerHosts
open private sameStorage from OAI.Computability.BorderVNP.DiagonalSiteExecution
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

universe u
variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P]
    {bits : P → ℕ} {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (rows : E.F.SiteRows) {oldCap newCap : ℕ}
    (oldPort : Port (fan S) P t ↪ Fin oldCap) (nextPort : Port (fan S) P (t+1) ↪ Fin newCap)
    (fieldRows : E.FieldRows rows oldPort nextPort)
    (c : Fin (fan S) → Admissible good t) (old : ∀ j, Site.Programs (c j).val.pack.layout)

/-- The attained child directory preserves every native birth lane on the endpoint
words reconstructed through its actual subdivision and sparse save. -/
theorem installedPrivatePrograms_birthInput (i : Fin (fan S)) (v : (c i).val.pack.layout.Site)
    (x : PowerInput (E.view 0 ((E.run c).flat i)).pack.layout) :
    let run := E.run c
    let host := (enrichedInstalledHosts run.flat run.initialSites run.originalPack i).site v
    birthInput (E.view 0 (run.flat i)).pack.layout (fieldRows.layout.edges 0 (run.flat i)) (rows.ports 0) host
      (E.installedPrivatePrograms rows c old i host) x =
      birthInput (c i).val.pack.layout (c i).val.rows.edge oldPort v (old i v)
        (EnrichedSiteReplay.installedPowerInput run i v x) := by
  intro run host
  let a := run.initialSites i
  let orig := congrArg Pack.layout (run.originalPack i).symm
  let saved := congrArg (fun p => p.pack.layout) a.realizes.symm
  let raw := RowTrace.sameRows orig (c i).val.rows
  let new := raw.siteRoutes a.routes S.radius
  let port₀ : Port (fan S) P t ↪ Fin (rows.nPort 0) := rows.ports 0
  let prior := samePrivatePrograms orig (old i)
  let r := a.routes.routes S.radius
  let f₀ := portFintype (k := fan S) (P := P) (b := t)
  let f₁ := portFintype (k := S.fanIn) (P := Port (fan S) P t) (b := 0)
  let prior' := @changePrivateInstance D _ _ a.pack.layout f₀ f₁ prior
  let v' := (Retains.ofEq orig).site v
  let sub := @Subdivision.subdividePrivatePrograms D _ _ _ _ f₁ _ a.pack.layout r raw.edge new.edge port₀ prior'
  let before := (sameStorage saved).powerInput x
  let original := before.beforeSubdivision r v'
  have agree : (sameStorage orig).powerInput original = EnrichedSiteReplay.installedPowerInput run i v x :=
    congrArg (fun u => (sameStorage orig).powerInput (before.beforeSubdivision r u)) (sameHost orig v).symm
  rw [←agree]
  exact (birthInput_numbered _ (E.installedFieldRows c i).edge port₀ host (E.installedPrivatePrograms rows c old i host)
    _ (fieldRows.inputCap c) (fieldRows.inputRows c i) x).trans
    ((@birthInput_same D _ _ f₁ _ _ port₀ sub _ _ saved new (.inl v') x).trans
    ((@birthInput_subdivide D _ _ _ f₁ _ _ raw.edge port₀ prior' _ r new.edge v' before).trans
    ((birthInput_instance f₀ f₁ _ raw.edge port₀ prior v' original).trans
    ((birthInput_same _ port₀ (old i) orig (c i).val.rows v original).trans
    (birthInput_portNumbered _ (c i).val.rows.edge oldPort (old i) port₀ fieldRows.inputPortCap fieldRows.inputPorts v _)))))

end PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

end BorderVNP
end Computability
end OAI
