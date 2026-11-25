import OAI.ThreeFlat.Diagonal.RefreshStageRuns
import OAI.ThreeFlat.Diagonal.CompressorNodeHalves
import OAI.ThreeFlat.Diagonal.RefreshStageLayout

namespace OAI
/-! # Native local kernel and half-wire records at every refreshed site -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.PhysicalProcedure
open RAM.MotifRows RefreshDemandRows CompressorPacking.Native
variable {W : ℕ}

namespace Records

abbrev HalfColumns := ShrinkStage.Halves.HalfColumns
abbrev Expr := Formula 1

def siteOrdinal (m : ℕ) (current : Word W) (site : Expr) : Expr × Expr :=
  let lanes := field current 8
  let vp := Formula.op .div site lanes
  let block := plus (.op .mul (.op .div vp (.lit m)) lanes) (.op .mod site lanes)
  (block,.op .mod vp (.lit m))

/-- Node-specific five-word kernel directory record. The incident motif starts
at this site's six-word row and no deduplication or padding is needed. -/
def kernel (current : Word W) : Expr :=
  let ix := index current 34
  let site := Formula.op .div ix (.lit 5)
  rowAt 5 (![.load (.lit current.val),site,.lit 2,.lit 1,plus (field current 36) (.op .mul site (.lit 6))])
    (.op .mod ix (.lit 5))

/-- Each new site contains exactly one party in its block's local dense-to-
sparse restriction. The consumed party bit indexes that map. -/
def motif (current : Word W) (m K : ℕ) : Expr :=
  let ix := index current 36
  let z := siteOrdinal m current (.op .div ix (.lit 6))
  let choice := plus (field current 2) (.op .mul z.1 (.lit 3))
  let counts := plus (field current 1) (.op .mul z.1 (.lit K))
  let members := rowAt m (fun j => .lit (2^j.val)) z.2
  rowAt 6 (![z.1,counts,.load (plus choice (.lit 1)),.load choice,.lit 0,members])
    (.op .mod ix (.lit 6))

def halfHeader (current : Word W) (d : ℕ) : Expr :=
  let ix := index current 38
  let site := Formula.op .div ix (.lit 2)
  .select .eq (.op .mod ix (.lit 2)) (.lit 0) (.lit (2*d)) (plus (field current 40) (.op .mul site (.lit (8*d))))

def halfColumns (current : Word W) : HalfColumns := ⟨field current 8,field current 14,field current 15,field current 19⟩

def halves (current : Word W) (d : ℕ) : Expr :=
  ShrinkStage.Halves.record (halfColumns current) d (index current 40)

/-- Four bounded scans run after the graph and widths have been generated.
Every field for a node, including the source-coordinate reverse incidence and
all bit prefixes, is materialized in persistent stage memory. -/
def pipeline (current : Word W) (m d K : ℕ) : Pipeline W :=
  (Pipeline.scan current 34 35 (closed (kernel current))).thenDo
    ((Pipeline.scan current 36 37 (closed (motif current m K))).thenDo
      ((Pipeline.scan current 38 39 (closed (halfHeader current d))).thenDo
        (Pipeline.scan current 40 41 (closed (halves current d)))))

theorem returns (current : Word W) (m d K : ℕ) (mem : Memory W)
    (fit : (pipeline current m d K).fits mem) :
    (pipeline current m d K).program.Spec (fun z => z=mem)
      (fun _ z => z=(pipeline current m d K).run mem) ((pipeline current m d K).ticks mem) :=
  (pipeline current m d K).correct mem fit

end Records
end ThreeFlat.Diagonal.RefreshStageNav

end OAI
