import OAI.Hierarchy.DescentExteriorShelf
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Physical readbacks shared by the funded dated program and the final verifier -/
namespace Hierarchy.DescentTerminalFundedReadback
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

/-- Original packed selectors, all seventeen exterior columns, and the mounted
suffix survive the dated program. The saved rotations belong to its reached path. -/
structure Capture {w : ℕ} (lo compact j r t e extra : ℕ) (checked finished : Memory w)
    (rotation : Prop) : Prop where
  original : ∀a,lo≤a→a<compact→finished a=checked a
  columns : ∀(col:Fin 17)(u:ℕ),u<DescentExteriorShelf.span j r t e→
    finished ((DescentExteriorShelf.bank j r t e compact col.val).base+u)=
    checked ((DescentExteriorShelf.bank j r t e compact col.val).base+u)
  saved : rotation
  appendix : ∀u,u<extra→finished (compact+17*DescentExteriorShelf.span j r t e+u)=
    checked (compact+17*DescentExteriorShelf.span j r t e+u)

/-- A record of what the paid middle actually wrote into the native memory before
the final reel. The last field permits the selected date's tuple to include its
captured selectors and matrix addresses. -/
structure Receipt {w:ℕ} (code:Procedure w) (ticks:ℕ) (checked finished:Memory w)
    (flag lo compact j r t e extra:ℕ) (dated:Memory w→Prop) : Prop where
  executed : code.Exec checked finished ticks
  cheap : CheapCode code
  seed : finished flag=checked flag
  original : ∀i,lo≤ i→i<compact→finished i=checked i
  columns : ∀(col:Fin 17)(i:ℕ),i<DescentExteriorShelf.span j r t e→
    finished ((DescentExteriorShelf.bank j r t e compact col.val).base+i)=
    checked ((DescentExteriorShelf.bank j r t e compact col.val).base+i)
  appendix : ∀i,i<extra→finished (compact+17*DescentExteriorShelf.span j r t e+i)=
    checked (compact+17*DescentExteriorShelf.span j r t e+i)
  observed : dated finished

theorem Receipt.map {w:ℕ} {code:Procedure w} {ticks:ℕ} {checked finished:Memory w}
    {flag lo compact j r t e extra:ℕ} {p q:Memory w→Prop}
    (read:Receipt code ticks checked finished flag lo compact j r t e extra p)
    (apply_:p finished→q finished) : Receipt code ticks checked finished flag lo compact j r t e extra q :=
  ⟨read.executed,read.cheap,read.seed,read.original,read.columns,read.appendix,apply_ read.observed⟩


end
end Hierarchy.DescentTerminalFundedReadback

end OAI
