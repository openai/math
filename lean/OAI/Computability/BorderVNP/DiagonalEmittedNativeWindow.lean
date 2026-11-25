import OAI.Computability.BorderVNP.DiagonalPairedIssuedWindow

/-! # The paid window on the original emitted report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Evaluator VPVNP.BurstRAM BorderVNP.Cube Physical

variable {teams n w offsets ctl live ports wp wd B J X budget charge : ℕ}
    {a : SignedTaskArena.Layout} {U : Fin (teams+1) → PinStart SparseExterior.driver n w}
    {u : Fin (teams+1)} {p : (U u).Prefix a.id} {dir : Packing.Directory.Layout}
    {E I P A : Type} [Fintype P] [Fintype A]

/-- A window measured on the candidate's actual output gives the original
report's window at the issuer's rate. The four coordinates identify the same
declaration, cell labels, receiving cells and incoming widths. -/
def EmittedReport.windowFromNative
    (d : EmittedReport a U u p dir offsets ctl live ports E I P A wp wd B J)
    {decl : LengthDeclaration a.cube.n a.cube.header.d}
    {label : Fin a.cube.cells → Cube.Label (a.cube.n+1) a.cube.header.d}
    {recv : A → Fin a.cube.cells} {incoming : A → ℕ}
    (coordinates : (d.declaration,d.label,d.recv,d.incoming)=(decl,label,recv,incoming))
    (rate : budget=charge)
    (window : PinStart.PublishedArgumentWindow a a.id U p decl label recv incoming X dir.description wp wd
      a.cube.teams a.p.parameters B
      (FragmentRows.Layout.fromFrame ((U u).pub 0).val (readings (PinStart.visits a.id U p).reports.val.2.2))
      (a.controlRows u.val ((U u).pub 0).val offsets ctl live ports) (readings d.emission.output) budget) :
    d.Window X charge := by
  obtain ⟨declAt,rest⟩ := Prod.mk.inj coordinates
  obtain ⟨labelAt,rest⟩ := Prod.mk.inj rest
  obtain ⟨recvAt,widthAt⟩ := Prod.mk.inj rest
  subst decl label recv incoming charge
  exact window

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
