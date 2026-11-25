import OAI.Computability.BorderVNP.DiagonalEmittedReportTransport

/-! # The charged window on the very same relabelled emitter return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Evaluator VPVNP.BurstRAM BorderVNP.Cube Physical

/-- The original public-directory return and assignment still certify the
window on the jointly relabelled emitter, seed, native launch and report data.
Both observations are retained on that report's emitted words. -/
theorem EmittedReport.reindex_issued_window
    {teams n w X budget offsets ctl live ports wp wd B J : ℕ}
    {a b : SignedTaskArena.Layout} {U : Fin (teams+1) → PinStart SparseExterior.driver n w}
    {u : Fin (teams+1)} {p : (U u).Prefix a.id} {q : (U u).Prefix b.id} {dir : Packing.Directory.Layout}
    {E I P A Z : Type} [Fintype P] [Fintype A] (d : EmittedReport a U u p dir offsets ctl live ports E I P A wp wd B J)
    (layout : a=b) (same : HEq p q) (profile : Z → ℕ → ℕ) (observed : Z → (ℕ → ℕ) → Prop)
    (source : ∃ z assigned, observed z assigned ∧ ∃ win : d.Window X budget,
      win.profile=profile z ∧ win.assigned=assigned) :
    ∃ z assigned, observed z assigned ∧ ∃ win : (d.reindex layout q same).Window X budget,
      win.profile=profile z ∧ win.assigned=assigned := by
  obtain ⟨z,assigned,ran,win,auth⟩ := source
  let next := d.reindexWith (fun _ _ report =>
    {payment : report.Window X budget // payment.profile=profile z ∧ payment.assigned=assigned})
    layout q same ⟨win,auth⟩
  exact ⟨z,assigned,ran,next.val,next.property⟩

/-- Attach a registered window at the construction of the real report. The
declaration and three native packet arrays are those used in its issued data,
and the relabelled window refers to its very same emitted RAM. -/
theorem EmittedReport.reindex_issued_packet
    {teams n w X budget offsets ctl live ports wp wd B J : ℕ}
    {a b : SignedTaskArena.Layout} {U : Fin (teams+1) → PinStart SparseExterior.driver n w}
    {u : Fin (teams+1)} {p : (U u).Prefix a.id} {q : (U u).Prefix b.id} {dir : Packing.Directory.Layout}
    {E I P A Z : Type} [Fintype P] [Fintype A] (d : EmittedReport a U u p dir offsets ctl live ports E I P A wp wd B J)
    (layout : a=b) (same : HEq p q) {decl : LengthDeclaration a.cube.n a.cube.header.d}
    {label : Fin a.cube.cells → Cube.Label (a.cube.n+1) a.cube.header.d} {recv : A → Fin a.cube.cells} {incoming : A → ℕ}
    (coordinates : (d.declaration,d.label,d.recv,d.incoming)=(decl,label,recv,incoming))
    (profile : Z → ℕ → ℕ) (observed : Z → (ℕ → ℕ) → Prop)
    (source : ∃ z assigned, observed z assigned ∧ ∃ win :
      PinStart.PublishedArgumentWindow a a.id U p decl label recv incoming X dir.description wp wd a.cube.teams a.p.parameters B
        (FragmentRows.Layout.fromFrame ((U u).pub 0).val (readings (PinStart.visits a.id U p).reports.val.2.2))
        (a.controlRows u.val ((U u).pub 0).val offsets ctl live ports) (readings d.emission.output) budget,
        win.profile=profile z ∧ win.assigned=assigned) :
    ∃ z assigned, observed z assigned ∧
      (∃ win : d.Window X budget, win.profile=profile z ∧ win.assigned=assigned) ∧
      ∃ win : (d.reindex layout q same).Window X budget, win.profile=profile z ∧ win.assigned=assigned := by
  obtain ⟨declAt,rest⟩ := Prod.mk.inj coordinates
  obtain ⟨labelAt,rest⟩ := Prod.mk.inj rest
  obtain ⟨recvAt,widthAt⟩ := Prod.mk.inj rest
  subst decl
  subst label
  subst recv
  subst incoming
  obtain ⟨z,assigned,runs,win,auth⟩ := source
  let next := d.reindexWith (fun _ _ report =>
    {payment : report.Window X budget // payment.profile=profile z ∧ payment.assigned=assigned})
    layout q same ⟨win,auth⟩
  exact ⟨z,assigned,runs,⟨win,auth⟩,next.val,next.property⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
