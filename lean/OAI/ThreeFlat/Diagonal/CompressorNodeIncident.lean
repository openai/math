import OAI.ThreeFlat.Diagonal.CompressorUniformRows
import OAI.ThreeFlat.Diagonal.ShrinkLayout

namespace OAI
/-! # Compact incident motif records for a chronological shrinking site

Each candidate follows an old half-edge from a possible child of the site.
A candidate is retained once, at its first physical index, when at least one
of its six parties occupies the specified site. The public arity bound of
this enumeration is independent of the old vertex and lane counts.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents
open RAM.PhysicalPinsExpr Placement
abbrev F := Formula 1

structure Hit where
  key : F
  fields : Fin 6 → F

def eqSite (a b : Site F) : F :=
  .select .eq a.base b.base (.select .eq a.tag b.tag (.select .eq a.lane b.lane (.lit 1) (.lit 0))
    (.lit 0)) (.lit 0)

def mask {m : ℕ} (member : Fin m → F) : F :=
  RAM.MotifRows.totals ((List.finRange m).map fun j =>
    .select .eq (member j) (.lit 1) (.lit (2^j.val)) (.lit 0))

def hit (current : F) (S : Graph.Stage) (K : ℕ) (layout ownerLayout thin inc : Bool)
    (v : Site F) (h : Fin S.degree) (u : Fin (2^S.colors)) (i : Fin S.degree) : Hit :=
  let o := Demand.formulaOps 1
  let f := atField o current
  let g := oldColumns o current
  let p := widthLayout current S
  let e := fromChild o g S.degree ownerLayout thin inc v (.lit h.val) (.lit u.val) (.lit i.val)
  let roles := roleSites o g S.degree layout e
  let present (j : Fin 6) := eqSite (Graph.siteAt roles (ShrinkMotif.role layout j)) v
  let parties := mask present
  let edges := mask (fun j : Fin 8 =>
    .select .eq (present (ShrinkMotif.supplySrc j)) (.lit 1) (present (ShrinkMotif.supplyDst j)) (.lit 0))
  let ix := Demand.physical p e.source e.originalSlot
  let key := Formula.select .eq roles.valid (.lit 1) (.select .eq parties (.lit 0) (.lit 0)
    (.op .add ix (.lit 1))) (.lit 0)
  let row := ShrinkWidth.motifRow g p e.source e.originalSlot
  let counts := Formula.op .add (f countTable) (.op .mul row (.lit K))
  let choice := Formula.op .add (f choiceTable) (.op .mul row (.lit 3))
  ⟨key,![ix,counts,.load (.op .add choice (.lit 1)),.load choice,edges,parties]⟩

def all (current : F) (S : Graph.Stage) (K : ℕ) (layout : Bool) (v : Site F) : List Hit :=
  [false,true].flatMap fun own =>
    [false,true].flatMap fun thin =>
      (List.finRange S.degree).flatMap fun h =>
        (List.finRange (2^S.colors)).flatMap fun u =>
          [false,true].flatMap fun inc =>
            (List.finRange S.degree).map fun i => hit current S K layout own thin inc v h u i

structure FirstHit where
  valid : F
  fields : Fin 6 → F

def firsts (seen : List F) : List Hit → List FirstHit
  | [] => []
  | a :: tail =>
    let fresh := Formula.select .eq a.key (.lit 0) (.lit 0)
      (.select .eq (Template.member a.key seen) (.lit 1) (.lit 0) (.lit 1))
    ⟨fresh,a.fields⟩ :: firsts (a.key :: seen) tail

def occupied (xs : List FirstHit) : F := RAM.MotifRows.totals (xs.map FirstHit.valid)

def ordinalField (field : Fin 6) (n : F) : List FirstHit → F → F
  | [], _ => .lit 0
  | a :: tail, index =>
    let found := Formula.select .eq a.valid (.lit 1) (.select .eq n index (.lit 1) (.lit 0)) (.lit 0)
    .select .eq found (.lit 1) (a.fields field) (ordinalField field n tail (.op .add index a.valid))

def fieldAt (xs : List FirstHit) (i f : F) : F :=
  (List.finRange 6).foldr (fun j z => .select .eq f (.lit j.val) (ordinalField j i xs (.lit 0)) z) (.lit 0)

def siteAt (current : F) (i : F) : Site F :=
  let f := atField (Demand.formulaOps 1) current
  let b := Formula.op .div i (f remaining)
  ⟨.op .div b (f tags),.op .mod b (f tags),.op .mod i (f remaining)⟩

/-- Per-site bounded capacity, including possible duplicate and unused candidates. -/
def capacity (S : Graph.Stage) := 8 * S.degree^2 * 2^S.colors

def rows (current : F) (S : Graph.Stage) (K : ℕ) (layout : Bool) (i : F) : List FirstHit :=
  firsts [] (all current S K layout (siteAt current i))

def count (current : F) (S : Graph.Stage) (K : ℕ) (layout : Bool) (site : F) : F :=
  occupied (rows current S K layout site)

/-- Six equal-length fields at the requested address; the unused suffix reads zero. -/
def record (current : F) (S : Graph.Stage) (K : ℕ) (layout : Bool) (linear : F) : F :=
  let i := Formula.op .div linear (.lit 6)
  fieldAt (rows current S K layout (.op .div i (.lit (capacity S))))
    (.op .mod i (.lit (capacity S))) (.op .mod linear (.lit 6))

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

end OAI
