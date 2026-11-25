import OAI.Hierarchy.DescentPackedOwnerWord
import OAI.Hierarchy.DescentPackedReverseMatch
import OAI.Hierarchy.DescentNativeDonorROM

namespace OAI
/-! The fixed finite matching query and its old and newborn donor addresses. -/

namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSIMDLookup DescentSixParty
open scoped Classical BigOperators Fin.CommRing
noncomputable section

/-- The first hop chooses the old endpoint; the root component of its address
is the subsequent move of this endpoint's whole thin pack. -/
abbrev Walk := ℕ×Address

def bornRoot {s : Shape} (row : Fin 12→Cell (s).digit) (lay : Bool) (j : Fin 6) (r : ℕ) : ℕ×ℕ :=
  let dst (b : ℕ) := (b/r+1,b%r)
  (![(0,(row 9).val),dst (row 10).val,dst (row 7).val] : Fin 3→(ℕ×ℕ)) (cluster lay j)

/-- The peer register is the once-exchanged local owner block. Both relative
hops are kept so a receiver can use its fixed-width donor chart directly. -/
def look {r D : ℕ} (own : Fin r→Address) (peer : Fin D→Fin r→Address) (where_ : ℕ×ℕ) : Walk :=
  (where_.1,if atBlock : where_.2<r then
    if where_.1=0 then own ⟨where_.2,atBlock⟩ else
    if atPeer : where_.1-1<D then peer ⟨where_.1-1,atPeer⟩ ⟨where_.2,atBlock⟩ else (0,0,0)
    else (0,0,0))

structure Heads where
  old : Walk
  born : Option (Fin 6→Walk)

def actorHeads {r D p d : ℕ} (B profile : ℕ) (u : Panel r D p d) (l : Bool)
    (own : Fin r→Address) (peer : Fin D→Fin r→Address) (x : Fin r) (outSlot : Fin p) : Heads :=
  let s:=shape r D p profile
  let f:=inputs s B (leaf (u.winner x).val) u (fun _=>0)
  let table:=decodeOutput s (lookupCell s (encodeInput f))
  let old:=look own peer (0,x.val)
  let id:=word (s).digit (x.val*p+outSlot.val)
  ⟨old,(reverse table true id).map (fun j t=>look own peer (bornRoot (s:=s) (table.row j) l t r))⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local

namespace Hierarchy.DescentPacking.PackedMatch.Local.Owners
open DescentSIMDLookup
open scoped Classical Fin.CommRing
variable {r D d : ℕ}
noncomputable section

abbrev Register (r D d : ℕ) := Cell ((digits r D d*3)*r)

def addressed (v : Register r D d) (x : Fin r) : Address :=
  let q:=(encode (digits r D d) 3).symm ((encode (digits r D d*3) r).symm v x)
  ((q 0).val,(q 1).val,(q 2).val)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Owners

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section

def query {r D p d : ℕ} (B profile : ℕ) (panel : Panel r D p d) (block : Fin r) (slot : ℕ) (side : Bool) :=
  let fmt:=shape r D p profile
  let x:=inputs fmt B (leaf (panel.winner block).val) panel (fun _=>0)
  reverse (decodeOutput fmt (lookupCell fmt (encodeInput x))) side (word fmt.digit (block.val*p+slot))

def markedChoice {r D p d : ℕ} (B profile : ℕ) (panel : Panel r D p d) (block : Fin r) (slot : ℕ) :=
  (query B profile panel block slot false).isSome || (query B profile panel block slot true).isSome

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

namespace Hierarchy.DescentHaloWalkRAM.ActorPath
open DescentPacking.PackedMatch.Local
noncomputable section

def slot (D n : ℕ) : Fin (D+1) :=if live : n≠0 ∧ n-1<D then ⟨n-1,by omega⟩ else Fin.last D

def hops (D : ℕ) (a b : ℕ) : Path D := ![slot D a,slot D b,Fin.last D,Fin.last D]

def index (D : ℕ) (w : Walk) : Fin (breadth D):=finFunctionFinEquiv (hops D w.1 w.2.1)

end
end Hierarchy.DescentHaloWalkRAM.ActorPath

end OAI
