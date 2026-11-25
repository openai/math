import OAI.ThreeFlat.Diagonal.CompressorNativeArc
import OAI.ThreeFlat.Diagonal.CompressorNativeRank
import OAI.ThreeFlat.Diagonal.CompressorPackedAddress

namespace OAI
/-! # Native output-slot descriptors of the shrinking compressor

Each output slot queries a fixed local candidate array, selects its sorted
edge identifier at one end, and ranks that identifier in the local list at
the other end. The sorted identifier includes its parallel-copy ordinal.
The padding suffix uses the same slot ordinal and a nonzero tag translation.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Graph
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.DescriptorExpr Placement
open scoped Fin.NatCast
variable {w k n : ℕ}

structure Stage where
  degree : ℕ
  colors : ℕ
  pieces : Fin 4 → ℕ
  pieceRadix : ℕ
  liveDegree : ℕ
  outputDegree : ℕ

def roles (layout : Bool) (k : Fin 4) : Fin 3 × Fin 3 :=
  if layout then ![(0,1),(0,2),(1,2),(2,1)] k else ![(1,0),(1,2),(0,2),(2,0)] k

def siteAt {A : Type*} (s : RoleSites A) (i : Fin 3) : Site A :=
  if i=0 then s.a else if i=1 then s.b else s.other

def ownerLayout (layout : Bool) (i : Fin 3) : Bool :=
  if i=0 then false else if i=1 then true else layout

abbrev T (w k n : ℕ) := Term w k n

structure Candidate (A : Type*) where
  key : A
  otherBase : A
  shift : A

def encodeBase {A : Type*} (o : Ops A) (r : Radices A) (s : Site A) : A :=
  appendDigit o s.base r.tags s.tag

def Candidate.map {A B : Type*} (f : A → B) (e : Candidate A) : Candidate B :=
  ⟨f e.key,f e.otherBase,f e.shift⟩

def encodeCandidate {A : Type*} (o : Ops A) (r : Radices A) (S : Stage) (base : Site A)
    (arc : Ends A) (s : RoleSites A) (here there : Fin 3) (t : Fin 4) (copy : Fin (S.pieces t)) :
    Candidate A :=
  let a := siteAt s here
  let b := siteAt s there
  let oldPrefix := appendDigit o (encodeBase o r arc.source.site) (o.lit S.degree) arc.originalSlot
  let word := appendDigit o (appendDigit o oldPrefix r.colors arc.source.bits) (o.lit S.degree) arc.source.slot
  let id := o.bin .add (o.lit 1) (appendDigit o (appendDigit o word (o.lit 4) (o.lit t.val))
    (o.lit S.pieceRadix) (o.lit copy.val))
  let key := o.choose s.valid (o.lit 1) (o.choose a.base base.base
    (o.choose a.tag base.tag id (o.lit 0)) (o.lit 0)) (o.lit 0)
  ⟨key,encodeBase o r b,o.bin .bitXor a.lane b.lane⟩

def candidateWith {A : Type*} (o : Ops A) (g : ArcColumns A) (r : Radices A) (S : Stage)
    (lay reverse thin incoming : Bool) (base : Site A) (t : Fin 4)
    (copy : Fin (S.pieces t)) (childSlot : Fin S.degree) (bits : Fin (2^S.colors))
    (edgeSlot : Fin S.degree) : Candidate A :=
  let pair := roles lay t
  let here := if reverse then pair.2 else pair.1
  let there := if reverse then pair.1 else pair.2
  let arc := fromChild o g S.degree (ownerLayout lay here) thin incoming base
    (o.lit childSlot.val) (o.lit bits.val) (o.lit edgeSlot.val)
  encodeCandidate o r S base arc (roleSites o g S.degree lay arc) here there t copy

def candidates (g : ArcColumns (T w k n)) (r : Radices (T w k n)) (S : Stage)
    (lay reverse : Bool) (v : T w k n) : List (Candidate (T w k n)) :=
  let o := terms w k n
  let b := Site.mk (o.bin .div v r.tags) (o.bin .mod v r.tags) (o.lit 0)
  (List.finRange 4).flatMap fun t =>
    (List.finRange (S.pieces t)).flatMap fun j =>
      [false,true].flatMap fun thin =>
        (List.finRange S.degree).flatMap fun h =>
          (List.finRange (2^S.colors)).flatMap fun u =>
            [false,true].flatMap fun inc =>
              (List.finRange S.degree).map fun i =>
                candidateWith o g r S lay reverse thin inc b t j h u i

inductive Field | neighbor | matePort | delta | identifier deriving DecidableEq

def field (f : Candidate (T w k n) → T w k n) (key : T w k n) :
    List (Candidate (T w k n)) → T w k n
  | [] => .literal 0
  | x::xs => .select .eq x.key key (f x) (field f key xs)

/-- One table column is written in row-major order (new base, new outgoing
or incoming port). Calling this for each field provides both adjacencies
and the shifts. A fresh zero-padding edge changes only the tag digit. -/
def updateRow (g : ArcColumns (T w k 1)) (r : Radices (T w k 1)) (S : Stage)
    (lay reverse : Bool) (which : Field) (dest tagMask : T w k 1) : T w k 1 :=
  let o := terms w k 1
  let addr := o.bin .sub (.result 0) dest
  let site := o.bin .div addr (o.lit S.outputDegree)
  let port := o.bin .mod addr (o.lit S.outputDegree)
  let cs := candidates g r S lay reverse site
  let ids := cs.map Candidate.key
  let id := Rank.pick port ids ids
  let other := field Candidate.otherBase id cs
  let live := match which with
    | .identifier => id
    | .neighbor => other
    | .delta => field Candidate.shift id cs
    | .matePort => Rank.rank id ((candidates g r S lay (!reverse) other).map Candidate.key)
  let pad := match which with
    | .identifier => o.lit 0
    | .neighbor => o.bin .bitXor site tagMask
    | .matePort => port
    | .delta => o.lit 0
  .select .lt port (o.lit S.liveDegree) live pad

end ThreeFlat.Diagonal.CompressorPacking.Native.Graph

end OAI
