import OAI.Computability.BorderVNP.DiagonalIssuedWindowTransport

/-! # The original schedule and the window on its jointly deployed report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Evaluator VPVNP.BurstRAM BorderVNP.Cube Physical

variable {teams n w offsets ctl live ports wp wd B J os' ctl' live' ports' : ℕ}
    {a b : SignedTaskArena.Layout} {U : Fin (teams+1) → PinStart SparseExterior.driver n w}
    {u : Fin (teams+1)} {p : (U u).Prefix a.id} {q : (U u).Prefix b.id} {dir : Packing.Directory.Layout}
    {E I P A : Type} [Fintype P] [Fintype A]

local notation3 (prettyPrint := false) "old" => EmittedReport a U u p dir offsets ctl live ports E I P A wp wd B J
local notation3 (prettyPrint := false) "new" => EmittedReport b U u q dir os' ctl' live' ports' E I P A wp wd B J

/-- The emitter, patched bank, issued rows and the full native issue record
belong to the initial report, including their dependent indices. -/
structure EmittedReport.OriginalPackets (d : old) (placed : new) : Prop where
  emission : HEq placed.emission d.emission
  patch : HEq placed.patch d.patch
  rows : HEq placed.row d.row
  issued : HEq placed.issued d.issued

/-- Both allocations use the original report return and the same replayed
directory assignment. The executable operands remain those of the original
report through the change of layout and of the three public addresses. -/
def EmittedReport.WindowPair (d : old) (placed : new) (X budget : ℕ) {Z : Type}
    (profile : Z → ℕ → ℕ) (observed : Z → (ℕ → ℕ) → Prop) : Prop :=
  placed.emission.output=d.emission.output ∧ placed.emission.bank=d.emission.bank ∧
  HEq placed.seed d.seed ∧ HEq placed.launch d.launch ∧ HEq placed.issued.roster d.issued.roster ∧
  ∃ z assigned, observed z assigned ∧
    (∃ win : d.Window X budget, win.profile=profile z ∧ win.assigned=assigned) ∧
    ∃ win : placed.Window X budget, win.profile=profile z ∧ win.assigned=assigned ∧ d.OriginalPackets placed

/-- The original report's argument return fits the selected budget. -/
theorem EmittedReport.WindowPair.plannerWindow {d : old} {placed : new} {X budget : ℕ} {Z : Type}
    {profile : Z → ℕ → ℕ} {observed : Z → (ℕ → ℕ) → Prop}
    (pair : d.WindowPair placed X budget profile observed) : Nonempty (d.Window X budget) := by
  obtain ⟨_,_,_,⟨win,_⟩,_⟩ := pair.2.2.2.2.2
  exact ⟨win⟩

/-- The jointly deployed report has the same charged argument window. -/
theorem EmittedReport.WindowPair.deployedWindow {d : old} {placed : new} {X budget : ℕ} {Z : Type}
    {profile : Z → ℕ → ℕ} {observed : Z → (ℕ → ℕ) → Prop}
    (pair : d.WindowPair placed X budget profile observed) : Nonempty (placed.Window X budget) := by
  obtain ⟨_,_,_,_,win,_⟩ := pair.2.2.2.2.2
  exact ⟨win⟩

/-- The window pair retains the complete named emitter and report inputs. -/
theorem EmittedReport.WindowPair.originalPackets {d : old} {placed : new} {X budget : ℕ} {Z : Type}
    {profile : Z → ℕ → ℕ} {observed : Z → (ℕ → ℕ) → Prop}
    (pair : d.WindowPair placed X budget profile observed) : d.OriginalPackets placed := by
  obtain ⟨_,_,_,_,_,_,_,same⟩ := pair.2.2.2.2.2
  exact same

/-- The charged directory and its observations on a particular emitted bank. -/
def EmittedReport.CandidateWindow (d : old) (X budget : ℕ) {Z : Type}
    (decl : LengthDeclaration a.cube.n a.cube.header.d)
    (label : Fin a.cube.cells → Cube.Label (a.cube.n+1) a.cube.header.d)
    (recv : A → Fin a.cube.cells) (incoming : A → ℕ)
    (profile : Z → ℕ → ℕ) (observed : Z → (ℕ → ℕ) → Prop) : Prop :=
  ∃ z assigned, observed z assigned ∧ ∃ win :
      PinStart.PublishedArgumentWindow a a.id U p decl label recv incoming X dir.description wp wd a.cube.teams a.p.parameters B
        (FragmentRows.Layout.fromFrame ((U u).pub 0).val (readings (PinStart.visits a.id U p).reports.val.2.2))
        (a.controlRows u.val ((U u).pub 0).val offsets ctl live ports) (readings d.emission.output) budget,
        win.profile=profile z ∧ win.assigned=assigned

/-- Supply the registered native charge to the genuine joint report transport,
after identifying the four coordinate fields of the funded source packet. -/
theorem EmittedReport.deploy_issued_packet (d : old) {X budget : ℕ} {Z : Type}
    {decl : LengthDeclaration a.cube.n a.cube.header.d}
    {label : Fin a.cube.cells → Cube.Label (a.cube.n+1) a.cube.header.d} {recv : A → Fin a.cube.cells} {incoming : A → ℕ}
    (coordinates : (d.declaration,d.label,d.recv,d.incoming)=(decl,label,recv,incoming))
    (profile : Z → ℕ → ℕ) (observed : Z → (ℕ → ℕ) → Prop)
    (source : d.CandidateWindow X budget decl label recv incoming profile observed)
    (move : ∀ {T : Type} (header : T → ℕ → ℕ) (returned : T → (ℕ → ℕ) → Prop),
      d.WindowPair d X budget header returned → (placed : new) ×' d.WindowPair placed X budget header returned) :
    Nonempty ((placed : new) ×' d.WindowPair placed X budget profile observed) := by
  obtain ⟨z,assigned,ran,paid,_⟩ := d.reindex_issued_packet (q:=p) rfl HEq.rfl coordinates profile observed source
  obtain ⟨win,headerAt,assignedAt⟩ := paid
  exact ⟨move profile observed ⟨rfl,rfl,HEq.rfl,HEq.rfl,HEq.rfl,z,assigned,ran,⟨win,headerAt,assignedAt⟩,
    win,headerAt,assignedAt,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩⟩

section Rectangle

variable (dir : Packing.Directory.Layout) (base : ℕ) {before after : SignedTaskArena.Layout × ℕ × ℕ}
local notation3 (prettyPrint := false) "table(" c ")" => Packing.RoutingOutputs.bases base c.2.2 c.2.1 dir.entries
local notation3 (prettyPrint := false) "ctrl(" c ")" =>
  Packing.RoutingOutputs.controlsBase base c.2.2 c.2.1 dir.entries ports
local notation3 (prettyPrint := false) "row(" c "," run ")" =>
  EmittedReport c.1 U u run dir (table(c)).ends ctrl(c) (table(c)).livePairs ports E I P A wp wd B J

/-- Deploy the authentic issued window with the true report when both the task
and the physical rectangle feeding its addresses are relabelled. -/
theorem EmittedReport.deploy_issued_rectangle {p₀ : (U u).Prefix before.1.id} {p₁ : (U u).Prefix after.1.id}
    (d : row(before,p₀)) (rect : before=after) (samePrefix : HEq p₀ p₁)
    {X budget : ℕ} {Z : Type} {decl : LengthDeclaration before.1.cube.n before.1.cube.header.d}
    {label : Fin before.1.cube.cells → Cube.Label (before.1.cube.n+1) before.1.cube.header.d}
    {recv : A → Fin before.1.cube.cells} {incoming : A → ℕ}
    (coords : (d.declaration,d.label,d.recv,d.incoming)=(decl,label,recv,incoming))
    (profile : Z → ℕ → ℕ) (observed : Z → (ℕ → ℕ) → Prop)
    (charged : d.CandidateWindow X budget decl label recv incoming profile observed) :
    Nonempty ((placed : row(after,p₁)) ×' d.WindowPair placed X budget profile observed) :=
  d.deploy_issued_packet coords profile observed charged (fun headerAt returned starting =>
    EmittedReport.reindexPublication (before:=before) (after:=after) dir base d
      (fun _ _ report => d.WindowPair report X budget headerAt returned) rect p₁ samePrefix starting)

end Rectangle

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
