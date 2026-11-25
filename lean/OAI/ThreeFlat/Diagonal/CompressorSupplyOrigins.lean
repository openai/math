import OAI.ThreeFlat.Diagonal.CompressorBitOrigins

namespace OAI
/-! # Physical origins of the surviving split supply words

The slot identifier is stored once per oriented successor base arc. Search
only the slots of the known source base to locate its identifier. The
arrival half is obtained from its matching forward-slot column.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

open RAM.PhysicalPinsExpr Placement
variable {n : ℕ}

/-- Return the port of the unique matching positive key at the named source base. -/
def portLookup {d : ℕ} (base first key : F n) (ports : List (Fin d)) : F n :=
  ports.foldr (fun i tail => .select .eq (.load (.op .add base (.op .add first (.lit i.val))))
    key (.lit i.val) tail) (.lit 0)

def crossingSite (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n)) (t : Fin 4) :
    Site (F n) :=
  Graph.siteAt (roleSites (Demand.formulaOps n) (oldColumns (Demand.formulaOps n) ptr) S.degree lay e)
    (Graph.roles lay t).1

def crossingBase (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n)) (t : Fin 4) : F n :=
  let o:=Demand.formulaOps n
  Graph.encodeBase o (radices o ptr S) (crossingSite ptr S lay e t)

def crossingKey (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (t : Fin 4) (copy : Fin (S.pieces t)) : F n :=
  let o:=Demand.formulaOps n
  let sites:=roleSites o (oldColumns o ptr) S.degree lay e
  let pair:=Graph.roles lay t
  (Graph.encodeCandidate o (radices o ptr S) S (crossingSite ptr S lay e t) e sites pair.1 pair.2 t copy).key

def crossingPort (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (t : Fin 4) (copy : Fin (S.pieces t)) : F n :=
  portLookup (atField (Demand.formulaOps n) ptr keys) (.op .mul (crossingBase ptr S lay e t) (.lit S.outputDegree))
    (crossingKey ptr S lay e t copy) (List.finRange S.liveDegree)

def crossingMate (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (t : Fin 4) (copy : Fin (S.pieces t)) : F n :=
  let o:=Demand.formulaOps n
  let f:=atField o ptr
  let start:=Formula.op .mul (crossingBase ptr S lay e t) (.lit S.outputDegree)
  .load (.op .add (column o (f nextGraph) (f nextSlots) 1) (.op .add start (crossingPort ptr S lay e t copy)))

def crossing (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party : F n) (t : Fin 4) (copy : Fin (S.pieces t)) (j : F n) : Address n :=
  let half := Formula.select .eq party (.lit (ShrinkMotif.supplySrc (ShrinkMotif.survivor lay t)).val)
    (crossingPort ptr S lay e t copy) (.op .add (.lit S.outputDegree) (crossingMate ptr S lay e t copy))
  ![.lit 2,.lit 0,half,j]

def supplyWidth (ptr : F n) (S : Graph.Stage) (e : Ends (F n)) (edge : F n) : F n :=
  let o := Demand.formulaOps n
  let row := ShrinkWidth.motifRow (oldColumns o ptr) (layout ptr S) e.source e.originalSlot
  .load (.op .add (atField o ptr issued) (.op .add (.op .mul row (.lit 8)) edge))

def supplyCopies (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party width : F n) (t : Fin 4) : List (F n × (F n → Address n)) :=
  (List.finRange (S.pieces t)).map fun copy =>
    (Demand.balanced width (S.pieces t) (.lit copy.val),crossing ptr S lay e party t copy)

def supplyEdgeAddress (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party width j : F n) (i : Fin 8) : Address n :=
  let absorbed : Address n := ![.lit 3,.lit i.val,j,.lit 0]
  let routed := (List.finRange 4).foldr (fun t (tail : Address n) =>
    if ShrinkMotif.survivor lay t = i then locate (supplyCopies ptr S lay e party width t) j
    else tail) absorbed
  let o := Demand.formulaOps n
  let used := o.choose party (.lit (ShrinkMotif.supplySrc i).val) (.lit 1)
    (o.choose party (.lit (ShrinkMotif.supplyDst i).val) (.lit 1) (.lit 0))
  select used routed empty

/-- Local absorbed ordinal is the original edge number within this motif;
its private prefix row is scoped to the current incident motif. -/
def supplyAddress (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party edge j : F n) : Address n :=
  let width := supplyWidth ptr S e edge
  fun c => (List.finRange 8).foldr (fun i tail =>
    .select .eq edge (.lit i.val) (supplyEdgeAddress ptr S lay e party width j i c) tail) (.lit 0)

/-- `ptr` names a memory cell containing the actual stage header. The
incident row begins with the absolute old source arc number. -/
def lookup (S : Graph.Stage) (supply : Bool) (ptr incident party edge j field : F n) : F n :=
  let o := Demand.formulaOps n
  let arc := oldArc ptr S (.load incident)
  let get (lay : Bool) : Address n :=
    if supply then supplyAddress ptr S lay arc party edge j
    else demandAddress ptr S lay arc party edge j
  let mode := atField o ptr selected
  (List.finRange 4).foldr (fun k tail =>
    .select .eq field (.lit k.val) (o.choose mode (.lit 1) (get true k) (get false k)) tail) (.lit 0)

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
