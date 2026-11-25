import OAI.Computability.BorderVNP.DiagonalTagSubdivision
import OAI.Computability.BorderVNP.PackedOuterInstalledModels
import OAI.Computability.BorderVNP.DiagonalEnrichedDenseSiteReplay

/-! # Birth observations on the actual enriched epoch's installed child directories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Programs

open Crossing Diagonal.CellEntries
open PackedHistoryCircuit.Normalized.EnrichedOuter

variable {D ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {Param Gadget : Type*}
  (N : Network D P bits) (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np)
  (s : Site.Programs N) (tags : N.Tables (Entry Param Gadget))
  (num : Gadget ↪ ℕ) (pred : N.Site → (ℕ → Bool) → Prop)

/-- Only the occupied numeric addresses determine the private observation fiber. -/
theorem TagModels.renumber {nf nq : ℕ} (model : TagModels N edge port s tags num pred)
    (next : N.Edge ↪ Fin nf) (ports : P ↪ Fin nq) (cap : nf=ne) (pcap : nq=np)
    (hc : ∀ z, (next z).val = (edge z).val) (hp : ∀ z, (ports z).val = (port z).val) :
    TagModels N next ports s tags num pred := by
  subst nf; subst nq
  obtain rfl : next = edge := DFunLike.ext _ _ fun z => Fin.ext (hc z)
  obtain rfl : ports = port := DFunLike.ext _ _ fun z => Fin.ext (hp z)
  exact model

/-- The finite enumeration at the parent and the inner zero-level enumeration
give the same ordered input and private predicate on all birth words. -/
theorem TagModels.changePrivate {D ne np : ℕ} {P : Type} {bits : P → ℕ} {Param Gadget : Type*}
    (f g : Fintype P) (N : Network D P bits) (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (progs : @Site.Programs D P f bits N) (tags : N.Tables (Entry Param Gadget))
    (num : Gadget ↪ ℕ) (pred : N.Site → (ℕ → Bool) → Prop)
    (model : @TagModels D ne np P f bits Param Gadget N edge port progs tags num pred) :
    @TagModels D ne np P g bits Param Gadget N edge port (changePrivateInstance N progs) tags num pred := by
  obtain rfl : g = f := Subsingleton.elim _ _
  exact model

end Packing.Inherited.Site.Programs

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

open Diagonal.ExternalSew Diagonal.CellEntries Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive
open Packing Packing.Inherited Site.Programs PublicCapacity
open private sameStorage from OAI.Computability.BorderVNP.DiagonalSiteExecution
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

private theorem tags_same {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {Team Param Gadget : Type}
    [Fintype Team] [Fintype Param] {exp : ℕ} {sh : Shape} {np : ℕ} {N Q : Network D P bits}
    (h : N = Q) (rows : Rows sh N) (port : P ↪ Fin np) (s : Site.Programs N)
    (t : Tracked Team Param Gadget exp N) (num : Gadget ↪ ℕ) (p : N.Site → (ℕ → Bool) → Prop)
    (model : TagModels N rows.edge port s t.tags num p) :
    TagModels Q (RowTrace.sameRows h rows).edge port (samePrivatePrograms h s) ((sameStorage h).tracked t).tags
      num (carryPred (Retains.ofEq h).site p) := by
  subst Q
  have eqn : carryPred (Retains.ofEq (rfl : N=N)).site p = p := by
    funext v b
    exact propext (carryPred_old (Retains.ofEq (rfl : N=N)).site p v b)
  rw [eqn]
  intro v z x
  exact model v _ _

universe u
variable {D m start T exp : ℕ} [NeZero D] {K P Team Param Gadget : Type} [Field K] [Fintype P]
    [Fintype Team] [Fintype Param] {bits : P → ℕ} {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {good : ∀ t, State S start P bits shape W t → Prop} {deep : S.floor+1+S.drop*T ≤ start} {t : ℕ} {ht : t<T}
    {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch.{u} deep ht good V w) (rows : E.F.SiteRows) {oldCap newCap : ℕ}
    (oldPort : Port (fan S) P t ↪ Fin oldCap) (nextPort : Port (fan S) P (t+1) ↪ Fin newCap)
    (fieldRows : E.FieldRows rows oldPort nextPort)
    (c : Fin (fan S) → Admissible good t) (old : ∀ j, Site.Programs (c j).val.pack.layout)
    (num : Gadget ↪ ℕ) (tag : ∀ j, Tracked Team Param Gadget exp (c j).val.pack.layout)
    (pred : ∀ j, (c j).val.pack.layout.Site → (ℕ → Bool) → Prop)
    (prior : ∀ j, TagModels (c j).val.pack.layout (c j).val.rows.edge oldPort (old j) (tag j).tags num (pred j))

include prior in
/-- Each installed inner leaf has the same conditioned original private fiber at
its retained host, on the exact edge rows and sorted port pins of the attained run. -/
theorem installedPrivatePrograms_tagModels (i : Fin (fan S)) :
    let run := E.run c
    TagModels (E.view 0 (run.flat i)).pack.layout (fieldRows.layout.edges 0 (run.flat i)) (rows.ports 0)
      (E.installedPrivatePrograms rows c old i) (EnrichedSiteReplay.installed run i (tag i)).tags num
      (carryPred (enrichedInstalledHosts run.flat run.initialSites run.originalPack i).site (pred i)) := by
  intro run
  let a := run.initialSites i
  let orig := congrArg Pack.layout (run.originalPack i).symm
  let saved := congrArg (fun p => p.pack.layout) a.realizes.symm
  let raw := RowTrace.sameRows orig (c i).val.rows
  let new := raw.siteRoutes a.routes S.radius
  let progs := samePrivatePrograms orig (old i)
  let f₀ := portFintype (k:=fan S) (P:=P) (b:=t)
  let f₁ := portFintype (k:=S.fanIn) (P:=Port (fan S) P t) (b:=0)
  let port₀ : Port (fan S) P t ↪ Fin (rows.nPort 0) := rows.ports 0
  let moved := (sameStorage orig).tracked (tag i)
  let pr := carryPred (Retains.ofEq orig).site (pred i)
  let r := a.routes.routes S.radius
  let sub := Subdivision.subdividePrivatePrograms a.pack.layout r raw.edge new.edge (rows.ports 0)
    (changePrivateInstance _ progs)
  have base := TagModels.renumber (c i).val.pack.layout (c i).val.rows.edge oldPort (old i) (tag i).tags num (pred i)
    (prior i) (c i).val.rows.edge port₀ rfl fieldRows.inputPortCap (fun _ => rfl) fieldRows.inputPorts
  have ho := tags_same orig (c i).val.rows port₀ (old i) (tag i) num (pred i) base
  have changed := TagModels.changePrivate f₀ f₁ a.pack.layout raw.edge port₀ progs moved.tags num pr ho
  have hs := Subdivision.subdivide_tagModels a.pack.layout r raw.edge new.edge (rows.ports 0)
    (changePrivateInstance _ progs) moved.tags num pr changed
  have hsave := tags_same saved new (rows.ports 0) sub (moved.subdivide r) num
    (carryPred (Retains.subdivide a.pack.layout r).site pr) hs
  have names : carryPred (Retains.ofEq saved).site (carryPred (Retains.subdivide a.pack.layout r).site pr) =
      carryPred (enrichedInstalledHosts run.flat run.initialSites run.originalPack i).site (pred i) := by
    let f := (Retains.ofEq orig).site
    let g := (Retains.subdivide a.pack.layout r).site
    let h := (Retains.ofEq saved).site
    exact (carryPred_trans g h (carryPred f (pred i))).trans (carryPred_trans f (g.trans h) (pred i))
  rw [names] at hsave
  exact TagModels.renumber _ (E.installedFieldRows c i).edge (rows.ports 0) (E.installedPrivatePrograms rows c old i)
    (EnrichedSiteReplay.installed run i (tag i)).tags num _ hsave _ _ (fieldRows.inputCap c) rfl
    (fieldRows.inputRows c i) (fun _ => rfl)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

end BorderVNP
end Computability
end OAI
