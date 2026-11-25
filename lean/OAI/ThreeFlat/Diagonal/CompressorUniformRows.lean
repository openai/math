import OAI.ThreeFlat.Diagonal.CompressorStageHeader

namespace OAI
/-! # Width-independent row templates for the native chronological scans

The stage-pointer cell is a single literal substitution. All other literals
and every decision-list length depend only on the fixed compressor degrees.
The template work is therefore a uniform bound at all simulator word sizes.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement
open scoped Fin.NatCast
abbrev F := Formula 1
abbrev ptr : F := .param .advice
abbrev f := atField (Demand.formulaOps 1) ptr
abbrev g := oldColumns (Demand.formulaOps 1) ptr
abbrev o := Demand.formulaOps 1

def member (x : F) (xs : List F) : F :=
  xs.foldr (fun j z => .select .eq x j (.lit 1) z) (.lit 0)

def firstFree (banned : List F) (n : ℕ) : F :=
  (List.finRange n).foldr (fun i z => .select .eq (member (.lit i.val) banned) (.lit 1) z (.lit i.val)) (.lit 0)

def oldRead (d : ℕ) (col v : F) (i : Fin d) : F :=
  .load (.op .add (.op .add col (.op .mul v (.lit d))) (.lit i.val))

def color (d : ℕ) : F :=
  let x := Formula.op .sub (.reg 0) (f colors)
  let adjacent (col : F) := (List.finRange d).map fun i => row o (f colors) (oldRead d col x i)
  firstFree (adjacent g.dst ++ adjacent g.src) (2*d+1)

def offset (d t : ℕ) : F :=
  let x := Formula.op .sub (.reg 0) (f offsets)
  let steps (v : F) := Formula.lit 0 :: (List.finRange d).map fun i => oldRead d g.forwardTag v i
  let xor := Formula.op .bitXor (n:=1)
  let part (s z other delta : F) := (steps x).map (xor delta) ++ (steps s).flatMap fun a =>
    (steps z).map fun b => xor (xor (xor delta a) b) (row o (f offsets) other)
  let out := (List.finRange d).flatMap fun i =>
    let y := oldRead d g.dst x i
    part x y y (oldRead d g.forwardTag x i)
  let back := (List.finRange d).flatMap fun i =>
    let y := oldRead d g.src x i
    part y x y (oldRead d g.backTag x i)
  firstFree (out++back) (2^t)

def below (k : F) : List F → F
  | [] => .lit 0
  | a::xs => .op .add (below k xs)
      (.select .eq a (.lit 0) (.lit 0) (.select .lt a k
        (.select .eq (member a xs) (.lit 0) (.lit 1) (.lit 0)) (.lit 0)))

def pick (k : F) (ids : List F) : F :=
  ids.foldr (fun a tail =>
    let ok := Formula.select .eq a (.lit 0) (.lit 0) (.select .eq (below a ids) k (.lit 1) (.lit 0))
    .select .eq ok (.lit 1) a tail) (.lit 0)

def candidates (S : Graph.Stage) (lay rev : Bool) (v : F) : List (Graph.Candidate F) :=
  let r := radices o ptr S
  let b := Placement.Site.mk (.op .div v r.tags : F) (.op .mod v r.tags) (.lit 0)
  (List.finRange 4).flatMap fun t =>
    (List.finRange (S.pieces t)).flatMap fun j =>
      [false,true].flatMap fun thin =>
        (List.finRange S.degree).flatMap fun h =>
          (List.finRange (2^S.colors)).flatMap fun u =>
            [false,true].flatMap fun inc =>
              (List.finRange S.degree).map fun i => Graph.candidateWith o g r S lay rev thin inc b t j h u i

def update (S : Graph.Stage) (lay rev : Bool) (which : Graph.Field) (dest : F) : F :=
  let off := Formula.op .sub (.reg 0) dest
  let v := Formula.op .div off (.lit S.outputDegree)
  let port := Formula.op .mod off (.lit S.outputDegree)
  let cs := candidates S lay rev v
  let ids := cs.map Graph.Candidate.key
  let id := pick port ids
  let get (fn : Graph.Candidate F → F) := cs.foldr (fun x z => .select .eq x.key id (fn x) z) (.lit 0)
  let live := match which with
    | .neighbor => get Graph.Candidate.otherBase
    | .matePort => below id ((candidates S lay (!rev) (get Graph.Candidate.otherBase)).map Graph.Candidate.key)
    | .delta => get Graph.Candidate.shift
    | .identifier => id
  let pad := match which with
    | .neighbor => Formula.op .bitXor v (.lit 1)
    | .matePort => port
    | _ => .lit 0
  .select .lt port (.lit S.liveDegree) live pad

def graph (S : Graph.Stage) (identifier : Bool) : F :=
  let make (layout : Bool) : F := if identifier then update S layout false .identifier (f keys) else
    let len := f nextSlots
    let start := f nextGraph
    let ix := Formula.op .div (.op .sub (.reg 0) start) len
    (List.finRange 6).foldr (fun i z => .select .eq ix (.lit i.val)
      (update S layout (decide (3≤ i.val)) (![Graph.Field.neighbor,.matePort,.delta,.neighbor,.matePort,.delta] i)
        (column o start len i.val)) z) (.lit 0)
  .select .eq (f selected) (.lit 1) (make true) (make false)

def input (S : Graph.Stage) : F :=
  ShrinkWidth.inputPair g (widthLayout ptr S) (f remaining) (.cut (.reg 0) (f demand))

def output (S : Graph.Stage) : F :=
  let make (lay : Bool) := ShrinkWidth.output g (widthLayout ptr S) S lay (f keys) (f issued)
    (f remaining) (.cut (.reg 0) (f nextWidths))
  .select .eq (f selected) (.lit 1) (make true) (make false)

/-- The one public symbolic parameter in a stage row is the address of the
current-header pointer. The installed primitive is a literal, with one instruction. -/
def bindCurrent {n : ℕ} (cell : ℕ) : Formula n → Formula n
  | .reg i => .reg i
  | .param _ => .lit cell
  | .lit v => .lit v
  | .op k x y => .op k (bindCurrent cell x) (bindCurrent cell y)
  | .cut x y => .cut (bindCurrent cell x) (bindCurrent cell y)
  | .load x => .load (bindCurrent cell x)
  | .select k x y s t => .select k (bindCurrent cell x) (bindCurrent cell y) (bindCurrent cell s) (bindCurrent cell t)

theorem bind_work {n : ℕ} (cell : ℕ) (x : Formula n) : (bindCurrent cell x).work = x.work := by
  induction x <;> simp [bindCurrent,Formula.work, *]

def emit {w : ℕ} (cell : Word w) (x : F) : T w := (bindCurrent cell.val x).compile (fun _ => 0)

theorem emit_work {w : ℕ} (cell : Word w) (x : F) : (emit cell x).binds = x.work := by
  rw [emit,Formula.binds_compile,bind_work]

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
