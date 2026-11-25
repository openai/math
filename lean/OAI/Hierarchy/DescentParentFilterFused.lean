import OAI.Hierarchy.DescentPackedParentFilterRAM
import OAI.Hierarchy.DescentParentFilterRoster
import OAI.Hierarchy.DescentPackedMatchedAll

namespace OAI
/-! # Inline the eleven actual raw parent fields in the short parallel-rank stream -/
namespace Hierarchy.DescentParallelBase.ParentFilter.Fused
open DescentSIMDLookup DescentHaloWalkRAM DescentSharedCableNames DescentPackedZip
open DescentColonies DescentSixParty DescentPackedOperand.Public
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {D oldHosts Q K L b w H G M c : ℕ}
local notation "P" => breadth D
local notation "peerCount" => P*P*Q
local notation "wd" => PackedBase.width peerCount K L

/-- Alphabet size for every prior raw scalar, including the missing-path rank. -/
def capacity (D Q K L : ℕ) :=
  breadth D+1+Q+breadth D*breadth D*Q+K+(L+1)+2

def fieldBits (D Q K L : ℕ) := Nat.clog 2 (capacity D Q K L)

theorem field_room (R : Fin oldHosts→Fin D→Option (Fin oldHosts)) (v : Fin oldHosts×Fin Q)
    (p : Fin P) (old : Fin oldHosts) (s : ParentFilter.Source P Q K L) (i : Fin 11)
    (room : capacity D Q K L≤2^b) : Machine.fields R v p old s i<2^b := by
  have rst:=Rebase.value_le R .rank v.1 p
  have srcLow:=s.src.low.isLt
  have dstLow:=s.dst.low.isLt
  have vLow:=v.2.isLt
  have srcRank:=(localRank R old s.src.path).isLt
  have dstRank:=(localRank R old s.dst.path).isLt
  have srcPeer:=(peer R v.1 p s.src).isLt
  have dstPeer:=(peer R v.1 p s.dst).isLt
  have ticket:=s.ticket.isLt
  have mass:=s.weight.isLt
  have upper : s.upper.toNat<2 := by cases s.upper <;> decide
  unfold capacity at room
  fin_cases i <;> simp [Machine.fields] <;> omega

theorem field_fits (R : Fin oldHosts→Fin D→Option (Fin oldHosts)) (v : Fin oldHosts×Fin Q)
    (p : Fin P) (old : Fin oldHosts) (s : ParentFilter.Source P Q K L) (i : Fin 11) :
    Machine.fields R v p old s i<2^(fieldBits D Q K L) :=
  field_room R v p old s i (Nat.le_pow_clog (by decide) _)

/-- A previous raw row and the actual receiver/path that selected it. -/
structure Raw (R : Fin oldHosts→Fin D→Option (Fin oldHosts)) (Q K L b : ℕ) where
  receiver : Fin oldHosts×Fin Q
  path : Fin (breadth D)
  host : Fin oldHosts
  parent : ParentFilter.Source (breadth D) Q K L
  small : ∀i,Machine.fields R receiver path host parent i<2^b

variable {R : Fin oldHosts→Fin D→Option (Fin oldHosts)}
def columns (r : Option (Raw R Q K L b)) (i : Fin 11) : Cell b :=
  r.elim 0 (fun x=>⟨Machine.fields R x.receiver x.path x.host x.parent i,x.small i⟩)

def filtered (r : Option (Raw R Q K L b)) : Option (Entry peerCount K L) :=
  r.bind (fun x=>filter R x.receiver x.path x.host x.parent)

theorem field_read (r : Option (Raw R Q K L b)) :
    Machine.scalar D Q K L b (encode b 11 (columns r))=PackedBase.word (filtered r) := by
  cases r with
  | none =>
    have empty : encode b 11 (columns (none:Option (Raw R Q K L b)))=0 := by
      apply Fin.ext
      change (finFunctionFinEquiv (fun _ : Fin 11=>(0:Cell b))).val=0
      simp []
    rw [empty,Machine.absent]
    rfl
  | some x => exact Machine.at_cell R x.receiver x.path x.host x.parent x.small

local notation "Gather" => DescentPacking.PackedMatch.Local.Gather.assembly

def expression (tables : Fin 11→Tables) (field : Fin 11→Expr) (lut : Tables) :=
  lut.read (Gather tables field) (.lit 0)

/-- A lookup expression can be sampled directly from the original memory. No
intermediate table of processed output words is needed between the two lookups. -/
theorem sourced (tables : Fin 11→Tables) (field : Fin 11→Expr) (lut : Tables) (out : Bank) (m : Memory w)
    (bounds : DescentPacking.PackedMatch.Local.Gather.Bounds (d:=b) (M:=M) (w:=w) tables field out.base)
    (fixed : ∀i,Static (tables i) (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) i) M m)
    (raw : Fin H→Fin G→Option (Raw R Q K L b))
    (live : ∀i,DescentPackedZip.Source (field i) (fun h g=>columns (raw h g) i) M m)
    (layout : DescentPackedZip.Fits lut (Gather tables field) (.lit 0) (b*11) 0 M out.base w)
    (table : Static lut (fun s (_:Cell 0)=>Machine.scalar D Q K L b s) M m)
    (space : out.base+H*chunks G M<2^w) :
    DescentPackedZip.Source (expression tables field lut) (fun h g=>PackedBase.word (filtered (raw h g))) M m := by
  obtain ⟨_,issued,_⟩:=Machine.run tables field lut out m bounds fixed (fun h g=>columns (raw h g)) live layout table space
  intro p
  have rd:=issued p
  rw [ProtocolRAMGeneratedWrite.read_image] at rd
  simpa only [expression,field_read] using rd

theorem expression_work (tables : Fin 11→Tables) (field : Fin 11→Expr) (lut : Tables) (limit : ℕ)
    (cost : ∀i,(field i).work≤limit) : (expression tables field lut).work≤13+11*(limit+11) := by
  have proof:=DescentPacking.PackedMatch.Local.Gather.collect_work tables field (List.finRange 11) limit cost
  rw [List.length_finRange] at proof
  simp only [expression,DescentPackedZip.work,Expr.work,DescentPacking.PackedMatch.Local.Gather.assembly]
  omega

def operation (slot : Fin c) (tables : Fin 11→Tables) (fields : Fin c→Fin 11→Expr) (lut compare : Tables) :=
  Stream.instruction compare (expression tables (fields slot) lut) (fun j=>expression tables (fields j) lut)

theorem operation_work (slot : Fin c) (tables : Fin 11→Tables) (fields : Fin c→Fin 11→Expr)
    (lut compare : Tables) (limit : ℕ) (cost : ∀j i,((fields j) i).work≤limit) :
    (operation slot tables fields lut compare).work≤1+c*(2*(13+11*(limit+11))+12) := by
  have all := fun j=>expression_work tables (fields j) lut limit (cost j)
  have main:=Stream.work compare (expression tables (fields slot) lut) (fun j=>expression tables (fields j) lut)
    (13+11*(limit+11)) all
  apply main.trans
  have bound := all slot
  gcongr; omega

section Geometry
variable {U E X T V : Type} [Fintype E] [DecidableEq U] [Fintype X] [Fintype T]
    {n O : ℕ} {B : Ends U n} (C : Blocks B E) (R : Fin oldHosts→Fin D→Option (Fin oldHosts))
    (symm : ∀v u i,R v i=some u→∃j,R u j=some v)
    (Z : Measured C R X T V Q O K L) (shelf : Measured.Shelf C R Z)
    (small : ∀h path x (s : ParentFilter.Source (breadth D) Q K L) i,Machine.fields R (Z.venue h) path (Z.loc x).1 s i<2^b)
local notation "res" => Measured.roster C R symm Z

def previous (h : U) (p : Fin P) (x : X) : Option (Raw R Q K L b) :=
  (shelf.issued h x).map (fun s=>⟨Z.venue h,p,(Z.loc x).1,s,small h p x s⟩)

def fetched (h : U) : Fin (P*O) → Option (Raw R Q K L b) :=
  Resident.collected h (fun u=>(Z.venue u).1) Z.loc (Gather.reaching R) (previous C R Z shelf small h)

theorem fetched_read (h : U) (j : Fin (P*O)) :
    filtered (fetched C R Z shelf small h j)=place ((res).address h) ((res).entry h) j := by
  rw [←Measured.literal_all C R symm Z shelf h]
  unfold fetched Resident.collected
  let xy : Fin P×Fin O:=finProdFinEquiv.symm j
  change filtered ((Gather.select (Gather.reaching R) (Z.venue h).1 xy.1).bind _)=
    (Gather.select (Gather.reaching R) (Z.venue h).1 xy.1).bind _
  cases look : Gather.select (Gather.reaching R) (Z.venue h).1 xy.1 with
  | none => rfl
  | some u =>
    simp only [Option.bind_some,Resident.oldAt]
    split
    next ok =>
      simp only [previous, Measured.deposited, filtered, Option.bind_map, Function.comp_def]
    next no => rfl

def cell (hosts : Fin H→Fin G→Option U) (j : Fin (P*O)) (h : Fin H) (g : Fin G) :=
  (hosts h g).bind (fun home=>fetched C R Z shelf small home j)

theorem row_read (hosts : Fin H→Fin G→Option U) (j : Fin (P*O)) (h : Fin H) (g : Fin G) :
    filtered (cell C R Z shelf small hosts j h g)=(res).field hosts j h g := by
  cases active : hosts h g with
  | none => simp [cell,Roster.field,active,filtered]
  | some home => simpa only [cell,Roster.field,active,Option.bind_some] using
      fetched_read C R symm Z shelf small home j

end Geometry

section Issued
variable {F Pn J V E X T V₀ : Type} [Field F] [Fintype Pn] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    [Fintype E] [Fintype X] [Fintype T] {d k i O : ℕ} {bits : Pn→ℕ}
    {W : DescentSixParty.MarkedWorld F d Pn bits} {gadget : DescentSixParty.PoweredGadget F} {price ε : ℝ}
variable (A : DescentSixParty.GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ)
    (schedule : DescentCompiler.AtomSchedule) (ready : A.StateBounds schedule i) (sites : Stage.Host J V k ↪ ℕ)
local notation "B" => Stage.source A native
local notation "U" => Stage.Host J V k
local notation "stream" => Stage.stream A native
variable (C : Blocks (Stage.source A native) E) (R : Fin oldHosts→Fin D→Option (Fin oldHosts))
    (symm : ∀v u i,R v i=some u→∃j,R u j=some v)
    (Z : Measured C R X T V₀ Q O K A.cap) (shelf : Measured.Shelf C R Z)
    (small : ∀h p x (s : ParentFilter.Source (breadth D) Q K A.cap) i,Machine.fields R (Z.venue h) p (Z.loc x).1 s i<2^b)
    (hosts : Fin H→Fin G→Option (Stage.Host J V k))
local notation "raw" => cell C R Z shelf small hosts
local notation "roster" => Measured.roster C R symm Z
local notation "bw" => PackedBase.width (P*P*Q) K A.cap

omit [Fintype Pn] in
/-- A single genuine scan. The mounted source fields here are the previous path,
raw endpoints, flags, ticket and mass, before filtering or ranking. -/
theorem run (tables : Fin 11→Tables) (fields : Fin (P*O)→Fin 11→Expr)
    (filterTable compare : Tables) (out : Bank) (m : Memory w)
    (bounds : ∀ j,DescentPacking.PackedMatch.Local.Gather.Bounds (d:=b) (M:=M) (w:=w) tables (fields j) out.base)
    (fixed : ∀i,Static (tables i) (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) i) M m)
    (live : ∀ j i,DescentPackedZip.Source (fields j i) (fun h g=>columns (raw j h g) i) M m)
    (filterFit : ∀ j,DescentPackedZip.Fits filterTable (Gather tables (fields j)) (.lit 0) (b*11) 0 M out.base w)
    (filterROM : Static filterTable (fun s (_:Cell 0)=>Machine.scalar D Q K A.cap b s) M m)
    (slot : Fin (P*O))
    (pairFit : ∀ j,DescentPackedZip.Fits compare (expression tables (fields slot) filterTable)
      (expression tables (fields j) filterTable) bw bw M out.base w)
    (compareROM : Static compare (Stream.compareWord (P*P*Q) K A.cap) M m)
    (space : out.base+H*chunks G M<2^w) (packedWord : Packed.bits A.cap*M≤w)
    (hm : 0<M) (h : Fin H) (g : Fin G) (host : U) (here : hosts h g=some host)
    (e : Local C host) (atRow : (roster).address host e=slot) (target : Bool) :
    let op := operation slot tables fields filterTable compare
    let done := image out.base (H*chunks G M) op m
    let first:=(stream).symm (C.order ⟨e.val,⟨0,e.property.1⟩⟩)
    (scan w out.base (H*chunks G M) op).Exec m done (4+H*chunks G M*(2*op.work+4)) ∧
      digit (Packed.bits A.cap) (lane g hm).val (done (out.base+(row H G M (position h g hm)).val)).val=
        (endpoint A native schedule ready sites target first).wire.val ∧ CheapCode (scan w out.base (H*chunks G M) op) := by
  have cells (j : Fin (P*O)) : DescentPackedZip.Source (expression tables (fields j) filterTable)
      (fun h g=>PackedBase.word ((roster).field hosts j h g)) M m := by
    have physical := sourced tables (fields j) filterTable out m (bounds j) fixed (raw j) (live j)
      (filterFit j) filterROM space
    simpa only [row_read C R symm Z shelf small hosts] using physical
  exact stream_first A native schedule ready sites C roster hosts slot compare _ _ out m pairFit compareROM
    (cells slot) cells space packedWord hm h g host here e atRow target

end Issued

end
end Hierarchy.DescentParallelBase.ParentFilter.Fused

end OAI
