import OAI.Hierarchy.DescentOrdinaryPaletteProgram

namespace OAI
/-! Gathering a true old scalar or one of the six new primitive tokens for every source origin. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPacking.PackedMatch.Local DescentHaloWalkRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSixParty.Chronology
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {w : ℕ} (L : Layout) (base : ℕ) (B : L.Inputs)
local notation "H" => L.hosts
local notation "J" => L.groups
local notation "O" => L.oldGroups
local notation "M" => L.oldWork
local notation "P" => L.ports
local notation "D" => L.degree
local notation "k" => L.k
local notation "K" => L.oldNodes
local notation "cap" => L.capacity
local notation "b" => L.primitiveBits
local notation "header" => L.portStart base
local notation "dict" => L.references (L.bookStart base)
local notation "spread" => L.spreadStart base
local notation "roster" => DescentScalarHaloPortROM.chart H O M P header B.halo

structure Stock where
  previous : Fin L.blocks→Fin H→Fin O→Cell (b*K)
  newborn : Fin L.fields→Fin H→Fin O→Cell b
  origin : Fin L.blocks→Fin L.successors→Fin J→Cell (L.originBits*L.newNodes)
  next : Fin H→Fin P→Option (Fin H)

section
variable {L}

def Stock.cells (S : L.Stock) (h : Fin H) (g : Fin O) (j : Fin L.candidates) : Cell b :=
  (S.next h (bookRoot D k K cap j)).elim 0 (fun t=>
    item S.previous (fun x port who=>S.newborn (L.bornIndex x port who)) (bookBlock D k K cap j) (bookItem D k K cap j) t g)
def Stock.pool (S : L.Stock) (h : Fin H) (g : Fin O) :=encode b L.candidates (S.cells h g)
def Stock.onBlock (S : L.Stock) :=DescentScalarBookReshape.book (Q:=L.lows) (r:=L.blocks) (fun _=>S.pool)

end

structure Observed (S : L.Stock) (m : Memory w) : Prop where
  past : ∀x,Reads (B.previous x) (S.previous x) L.priorLanes m
  born : ∀x,Reads (B.newborn x) (S.newborn x) L.birthLanes m
  origin : ∀x,Reads (B.origin x) (S.origin x) L.originLanes m
  halo : ∀h i,m (B.halo.base+(h.val*P+i.val))=(target (S.next h i):Word w)

structure Capacity : Prop where
  past : ∀x,H*chunks O L.priorLanes≤(B.previous x).size
  born : ∀x,H*chunks O L.birthLanes≤(B.newborn x).size
  origin : ∀x,L.successors*chunks J L.originLanes≤(B.origin x).size
  prior_live : 0<L.priorLanes
  birth_live : 0<L.birthLanes
  origin_live : 0<L.originLanes
  work_live : 0<L.workLanes

theorem before_bank {x : Bank} {out n : ℕ} (fits : x.Fits w out) (i : Fin n) (size : n≤x.size) :
    x.base+i.val<out :=(Nat.add_lt_add_left (i.isLt.trans_le size) _).trans_le fits.2.2

theorem carry_reads {h g n a fence : ℕ} {x : Bank} {u : Fin h→Fin g→Cell a} {m o : Memory w}
    (fit : x.Fits w fence) (size : h*chunks g n≤x.size) (eqm : ∀i,i<fence→ o i=m i)
    (got : Reads x u n m) : Reads x u n o :=
  fun r=>(eqm _ (before_bank fit (row h g n r) size)).trans (got r)

theorem field_sources (m : Memory w) (e : L.Early base B w) (S : L.Stock)
    (room : spread<2^w)
    (wired : Mounted roster S.next m O M)
    (old : ∀x,Reads (L.prior.bank base x) (S.previous x) M m)
    (birth : ∀x,Reads (L.births.bank (L.birthStart base) x) (S.newborn x) M m)
    (data : (dict).Issued m) :
    Source (L.pool base B) S.pool M m :=by
  obtain ⟨p,q,r,s,t,_,_,_⟩:=L.cuts base
  have ef:=r.trans (s.trans t)
  have eb:=q.trans ef
  have access (g : Bank) (fit : g.Fits w spread) (size : H*chunks O M≤g.size) :=
    (DescentScalarHaloPortROM.geometry H O M P header spread B.halo g t room (widen (p.trans eb) e.halo) e.slots fit size).1
  have past x:=L.prior.placed base (w:=w) (eb.trans_lt room) x
  have fresh x:=L.births.placed (L.birthStart base) (w:=w) (ef.trans_lt room) x
  have tables:=(dict).rooms (w:=w) le_rfl room
  have field (j : Fin L.candidates) : Source (L.field base B j) (fun h g=>S.cells h g j) M m :=
    ScalarOperand.source roster _ _ (dict).dictionary spread m S.next wired S.previous _
      old (fun x t q=>birth (L.bornIndex x t q))
      (fun x=>access _ (widen eb (past x).1) (past x).2)
      (fun x t q=>access _ (widen ef (fresh (L.bornIndex x t q)).1) (fresh (L.bornIndex x t q)).2)
      tables.dictionary data.dictionary _ _ _
  have complete :
      (fun h g => encode b L.candidates (fun j =>
        if j ∈ List.finRange L.candidates then S.cells h g j else 0)) = S.pool := by
    funext h g
    apply congrArg (encode b L.candidates)
    funext j
    exact ite_eq_left (List.mem_finRange j)
  rw [← complete]
  exact Gather.collected (dict).gates (L.field base B) spread (tables.fields _ (L.field_fit base B e room)) m
    data.fields S.cells field (List.finRange _)

end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout

end OAI
