import OAI.Hierarchy.DescentDonorWidths
import OAI.Hierarchy.DescentDonorShape
import OAI.Hierarchy.DescentPackedMatchShape

namespace OAI
/-! # Local numerical decoding of the matching board and old actor registers -/
namespace Hierarchy.DescentPacking.PackedMatch
open DescentSIMDLookup PackedLocalMatch
open scoped Classical Fin.CommRing
noncomputable section
variable {s : Shape}

def interval (wt : Fin s.packs→ℕ) (u : Fin s.packs) (j : ℕ) : Prop :=
  ProtocolRAMPortRanks.«prefix» wt Fin.val u≤j ∧ j<ProtocolRAMPortRanks.«prefix» wt Fin.val u+wt u

def redirects (x : Inputs s) (out : Output s) (u : Fin s.packs) (j : Fin s.pairs) : Bool :=
  decide ((out.row j 0).val=1 ∧ interval (s:=s) (need x) u (out.row j 3).val)

def headRow (x : Inputs s) (out : Output s) (u : Fin s.packs) :=
  (List.finRange s.pairs).find? (redirects x out u)

/-- The reported thick token is decoded by the same chosen layout, from
columns 9/10 of the true matched row. A silent or unassigned pack keeps
its original short slot. -/
def centerAt (l : Bool) (table : Output s) (j : Fin s.pairs) : Cell s.digit :=
  table.row j (if l then 10 else 9)

namespace Local

/-- Zero denotes the thick receiver. A thin pack uses its one-based index in the
actual short list, including a pack with zero currently matched units. -/
def readPack {D : Type*} [DecidableEq D] (rows : List (List D)) (x : D) : ℕ :=
  ((List.finRange rows.length).find? fun i=>decide (x∈rows.get i)).elim 0 (fun i=>i.val+1)

/-- A self address has first coordinate zero; direct neighbor v uses v+1. -/
abbrev Address := ℕ×ℕ×ℕ

def thickAddress {r D p b : ℕ} (u : Panel r D p b) (lay : Bool) (center : ℕ) : Address :=
  if lo : center%r<r then
    if lay then
      if hi : center/r<D then (center/r+1,leaf (u.peerWinner ⟨center/r,hi⟩ ⟨center%r,lo⟩).val,0)
      else (0,0,0)
    else (0,leaf (u.winner ⟨center%r,lo⟩).val,0)
  else (0,0,0)

/-- The lookup scans the short source pack and its physical matching window.
The layout bit is the actually selected common branch. -/
def resolved {r D p b : ℕ} (B profile : ℕ) (u : Panel r D p b) (lay : Bool) (x : Fin r) : Address :=
  let s:=shape r D p profile
  let leafAt:=leaf (u.winner x).val
  let packsAt:=packs u (s).bins B leafAt
  let slot:=readPack packsAt x
  let f:=inputs s B leafAt u (fun _=>0)
  let data:=decodeOutput s (lookupCell s (encodeInput f))
  if bounds : 0<slot ∧ slot≤(s).packs then
    match headRow f data ⟨slot-1,by omega⟩ with
    | none=>(0,leafAt,slot)
    | some j=>thickAddress u lay (centerAt lay data j).val
  else (0,leafAt,slot)

def location {Z : Type} {D : ℕ} (next : Z→Fin D→Option Z) (root : Z) (q : Address) : Option Z :=
  if q.1=0 then some root else if ok : q.1-1<D then next root ⟨q.1-1,ok⟩ else none

namespace Owners

def cell (r D d : ℕ) (q : Address) : Cell (digits r D d*3) :=
  encode (digits r D d) 3 ![word _ q.1,word _ q.2.1,word _ q.2.2]

def render (r D p d B profile : ℕ) (x : Cell (inputBits r D p d)) : Cell ((digits r D d*3)*r) :=
  let b : Cell 1×Cell (d*fields r D p):=finProdFinEquiv.symm (finCongr (pow_add 2 1 (d*fields r D p)) x)
  let u:=decodePanel b.2
  encode (digits r D d*3) r (fun j=>cell r D d (resolved B profile u (decide (b.1.val=1)) j))

end Owners
end Local
end
end Hierarchy.DescentPacking.PackedMatch

end OAI
