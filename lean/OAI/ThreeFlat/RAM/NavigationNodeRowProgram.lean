import OAI.ThreeFlat.RAM.NavigationNodeFields
import OAI.ThreeFlat.RAM.HeaderScanProcedure
import OAI.ThreeFlat.RAM.MotifRows
import OAI.ThreeFlat.RAM.NextStage

namespace OAI
/-! # Native chronological node header, expression code, and two-column publisher -/

namespace ThreeFlat.RAM.NavigationNodeRows

open Computability.VPVNP.BurstRAM PhysicalPinsExpr PhysicalProcedure MotifRows
open scoped Fin.CommRing
variable {W : ℕ}
abbrev Expr := Formula 1


/-- Offsets four and eleven obey the same control-pointer convention as the preceding
stage archive. Each layer has contiguous node and charge segments in chronological order. -/
def header (b : Banks) (s : Layer) (p : Parent) (next : ℕ) : ℕ → ℕ
  | 0 => b.charges+2*s.first
  | 1 => 2*s.count
  | 2 => b.nodes+8*s.first
  | 3 => 8*s.count
  | 4 => next
  | 5 => s.first
  | 6 => s.kind
  | 7 => s.childCount
  | 8 => s.children
  | 9 => s.kernels
  | 10 => s.incident
  | 11 => if p.finalLayer then 1 else 0
  | 12 => p.first
  | 13 => p.owners
  | _ => 0

def h (b : Banks) (off : ℕ) : Expr := field (.load (.lit b.current)) off

def ix (base i : Expr) (stride off : ℕ) : Expr :=
  .op .add (.op .add base (.op .mul i (.lit stride))) (.lit off)

def fromChildren (b : Banks) (row : Expr) (cap col : ℕ) : Expr :=
  let n := h b 7
  let first := plus (h b 8) (.op .mul row n)
  totals ((List.finRange cap).map fun i =>
    let child := field first i.val
    .select .lt (.lit i.val) n (.load (ix (.lit b.charges) child 2 col)) (.lit 0))

def incidentWidth (b : Banks) (row : Expr) (cap : ℕ) : Expr :=
  let head := ix (h b 10) row 2 0
  totals ((List.finRange cap).map fun i =>
    .select .lt (.lit i.val) (field head 0) (field (field head 1) (4*i.val+2)) (.lit 0))

def motifCopies (b : Banks) (row : Expr) (cap : ℕ) : Expr :=
  let head := ix (h b 9) row 5 0
  .select .eq (h b 6) (.lit 0) (.lit 0) (totals ((List.finRange cap).map fun i =>
    .select .lt (.lit i.val) (field head 3) (field (field head 4) (6*i.val+3)) (.lit 0)))

def traceLeaf (b : Banks) (row yes no : Expr) : Expr :=
  .select .eq (h b 6) (.lit 0) (.select .lt row (.lit b.lanes) yes no) no

def leafPairs (b : Banks) (row : Expr) : Expr :=
  let available := Formula.cut (.lit b.totalPairs) (.op .mul row (.lit b.perLanePairs))
  traceLeaf b row (.select .lt available (.lit b.perLanePairs) available (.lit b.perLanePairs)) (.lit 0)

/-- Native charge output in two-word [work,pairs] order. All children were issued in a
strictly earlier layer. An absolute polynomial factor in unitWork covers recursive copies
and the interpreter. Only the original cursor-zero buckets incur the trace-row charge. -/
def charge (b : Banks) (children halves motifs : ℕ) : Expr :=
  let z := Formula.cut (.reg 0) (h b 0)
  let row := Formula.op .div z (.lit 2)
  let localSize := plus (.lit 1) (plus (incidentWidth b row halves)
    (plus (motifCopies b row motifs) (plus (leafPairs b row) (traceLeaf b row (.lit b.traceWork) (.lit 0)))))
  .select .eq (.op .mod z (.lit 2)) (.lit 0)
    (plus (.op .mul (.lit b.unitWork) localSize) (fromChildren b row children 0))
    (plus (leafPairs b row) (fromChildren b row children 1))

def pick (fields : List Expr) (index : Expr) : Expr :=
  (fields.zipIdx).foldr (fun kv rest => .select .eq index (.lit kv.2) kv.1 rest) (.lit 0)

def node (b : Banks) : Expr :=
  let z := Formula.cut (.reg 0) (h b 2)
  let row := Formula.op .div z (.lit 8)
  let id := plus (h b 5) row
  let parent := Formula.select .eq (h b 11) (.lit 1) id (plus (h b 12) (.load (plus (h b 13) row)))
  let children := h b 7
  let pins := Formula.op .mul (.lit 2) (.load (ix (.lit b.charges) id 2 1))
  pick [h b 6,parent,row,plus (h b 8) (.op .mul row children),children,ix (h b 9) row 5 0,
      ix (h b 10) row 2 0,pins] (.op .mod z (.lit 8))

def procedure (b : Banks) (children halves motifs : ℕ) : Procedure W :=
  (HeaderScan.procedure (b.current : Word W) 0 1 (HeaderScan.closed (charge b children halves motifs))).seq
    ((HeaderScan.procedure (b.current : Word W) 2 3 (HeaderScan.closed (node b))).seq
      (NextStage.procedure (b.current : Word W)))

end ThreeFlat.RAM.NavigationNodeRows

end OAI
