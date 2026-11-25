import OAI.Hierarchy.DescentOrdinaryBornRolePorts
import OAI.Hierarchy.DescentGatheredVectorReshape
import OAI.Hierarchy.DescentOrdinaryOriginMask

namespace OAI
/-! The ordinary donor walk and stable node order carry each of the three fields of a
newborn operand to the receiving host. They use exactly the ordinary mask's old-node slots. -/
namespace Hierarchy.DescentOrdinaryMouthReturn
open DescentOrdinaryBorn DescentOrdinaryAtomFieldRAM.ScalarOperand DescentSIMDLookup
open DescentPackedColony DescentSixParty.Chronology ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  B : DescentOrdinaryBorn.Chart
  degree : ℕ
  depth : ℕ
  oldNodes : ℕ
  newNodes : ℕ
  lows : ℕ
  groups : ℕ
  radix : ℕ
  lanes : ℕ
  blocks_eq : B.blocks=2^depth

namespace Layout
variable (L : Layout)
abbrev Ref := Refs L.degree L.depth L.oldNodes L.B.cap
abbrev Val (nb mb : ℕ) := Values L.degree L.depth L.oldNodes L.B.cap L.B.hosts L.B.groups L.B.bits nb mb

def pages := L.B.args*3
def bits := L.B.bits*L.newNodes
def start (floor : ℕ) := RolePorts.endAddress L.B floor
def raw (floor : ℕ) : Bank :=
  ⟨L.start floor,Nat.clog 2 (L.pages*DescentVectorBookReshape.sourceWords L.B.hosts L.lows L.groups L.lanes)⟩
def transpose (floor : ℕ) := L.start floor+(L.raw floor).size
def out (floor : ℕ) := DescentVectorBookReshape.output (L.transpose floor) L.pages L.B.hosts L.lows
  L.groups L.radix L.bits L.lanes
def nextRows := (L.B.hosts*L.lows)*chunks L.groups L.lanes
def endAddress (floor : ℕ) := L.out floor+L.pages*DescentVectorBookReshape.rows L.B.hosts L.lows
  L.groups L.radix L.lanes+2^Nat.clog 2 L.nextRows
def returned (floor : ℕ) (arg : Fin L.B.args) (field : Fin 3) (block : Fin L.radix) : Bank :=
  ⟨DescentScalarBookReshape.dest L.B.hosts L.lows L.groups L.lanes
    (DescentVectorBookReshape.destBase (L.out floor) L.B.hosts L.lows L.groups L.radix L.lanes
      (finProdFinEquiv (arg,field))) block,Nat.clog 2 L.nextRows⟩

def refs (floor : ℕ) (C : Fin L.B.args→Fin L.lows→L.Ref) (page : Fin L.pages) (low : Fin L.lows) : L.Ref :=
  let z : Fin L.B.args×Fin 3:=finProdFinEquiv.symm page
  {C z.1 low with birth:=fun b seat party=>RolePorts.bank L.B floor (b.cast L.blocks_eq.symm) seat party z.1 z.2}

def vals {nb mb} (V : Fin L.B.args→Fin L.lows→L.Val nb mb) (chip : Fin L.B.hosts→Fin L.B.groups→Cell L.B.chipBits)
    (page : Fin L.pages) (low : Fin L.lows) : L.Val nb mb :=
  let z : Fin L.B.args×Fin 3:=finProdFinEquiv.symm page
  { V z.1 low with
    born := fun b seat party h g =>
      RolePorts.value L.B.bits
        (DescentOrdinaryBorn.pointerAt L.B.demand L.B.grain L.B.scale
          (chipDonor L.B.format (chip h g) (finProdFinEquiv (b.cast L.blocks_eq.symm,seat))) party z.1.val) z.2 }

def gather (floor w : ℕ) (C : Fin L.B.args→Fin L.lows→L.Ref) : NativePhase w :=
  let c:=L.refs floor C
  ⟨DescentGatheredVectorReshape.program c L.B.hosts L.B.groups L.groups L.radix L.lanes L.bits
      (L.transpose floor) (L.out floor) w (L.raw floor),
    DescentGatheredVectorReshape.ticks c L.B.hosts L.B.groups L.groups L.radix L.lanes L.bits (L.raw floor),
    DescentGatheredVectorReshape.result c L.B.hosts L.B.groups L.groups L.radix L.lanes L.bits
      (L.transpose floor) (L.out floor) (L.raw floor),
    DescentGatheredVectorReshape.cheap c L.B.hosts L.B.groups L.groups L.radix L.lanes L.bits
      (L.transpose floor) (L.out floor) w (L.raw floor)⟩

def phase (chip : Bank) (floor w : ℕ) (C : Fin L.B.args→Fin L.lows→L.Ref) : NativePhase w :=
  (RolePorts.phase L.B chip floor w).seq (L.gather floor w C)

theorem bounds (floor : ℕ) :
    floor≤L.start floor ∧ L.start floor≤L.transpose floor ∧ L.transpose floor≤L.out floor ∧
      L.out floor+L.pages*DescentVectorBookReshape.rows L.B.hosts L.lows L.groups L.radix L.lanes≤L.endAddress floor := by
  refine ⟨(RolePorts.order L.B floor).1.trans (RolePorts.order L.B floor).2,Nat.le_add_right ..,?_,Nat.le_add_right ..⟩
  exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))

theorem placed {w} (floor : ℕ) (arg : Fin L.B.args) (f : Fin 3) (b : Fin L.radix) (space : L.endAddress floor<2^w) :
    (L.returned floor arg f b).Fits w (L.endAddress floor) ∧ L.nextRows≤(L.returned floor arg f b).size := by
  let p : Fin L.pages:=finProdFinEquiv (arg,f)
  have block : b.val*L.nextRows≤DescentVectorBookReshape.rows L.B.hosts L.lows L.groups L.radix L.lanes :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt b.isLt)
  have page:=Nat.mul_le_mul_right (DescentVectorBookReshape.rows L.B.hosts L.lows L.groups L.radix L.lanes)
    (Nat.succ_le_of_lt p.isLt)
  rw [Nat.succ_mul] at page
  have top : (L.returned floor arg f b).base+(L.returned floor arg f b).size≤L.endAddress floor := by
    change (L.out floor+p.val*DescentVectorBookReshape.rows L.B.hosts L.lows L.groups L.radix L.lanes)+b.val*L.nextRows+
      2^Nat.clog 2 L.nextRows≤L.out floor+L.pages*DescentVectorBookReshape.rows L.B.hosts L.lows L.groups L.radix L.lanes+
        2^Nat.clog 2 L.nextRows
    omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (top.trans_lt space),top⟩,Nat.le_pow_clog (by decide) _⟩

theorem room {w} (floor : ℕ) (space : L.endAddress floor<2^w) :
    DescentVectorBookReshape.Room L.pages L.B.hosts L.lows L.groups L.radix L.bits L.lanes w
      (L.transpose floor) (L.out floor) (L.raw floor) := by
  have ax:=L.bounds floor
  have bound : L.transpose floor<2^w:=ax.2.2.1.trans_lt ((Nat.le_add_right ..).trans_lt (ax.2.2.2.trans_lt space))
  exact DescentVectorBookReshape.arranged (L.transpose floor) (L.raw floor)
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt bound,le_rfl⟩ (Nat.le_pow_clog (by decide) _) (ax.2.2.2.trans_lt space)

private theorem raw_bound (floor : ℕ) (same : L.B.groups=L.groups*L.radix) (hm : 0<L.lanes) (hr : 0<L.radix) :
    (L.raw floor).base+(L.pages*L.lows)*(L.B.hosts*chunks L.B.groups (L.lanes*L.radix))≤L.transpose floor :=by
  rw [same,chunks_group L.groups L.lanes L.radix hm hr]
  simpa only [raw,transpose,Bank.size,DescentVectorBookReshape.sourceWords,Nat.mul_assoc] using
    Nat.add_le_add_left (Nat.le_pow_clog (by decide : 1<2)
      (L.pages*(L.lows*(L.B.hosts*chunks L.groups L.lanes)))) (L.start floor)

theorem any {w} (chip : Bank) (floor : ℕ) (C : Fin L.B.args→Fin L.lows→L.Ref) (m : Memory w)
    (old : chip.Fits w floor) (same : L.B.groups=L.groups*L.radix) (hm : 0<L.lanes) (hr : 0<L.radix)
    (early : ∀p l,((L.refs floor C p l).expr L.B.hosts).inputEnd≤L.start floor)
    (space : L.endAddress floor<2^w) :
    (L.phase chip floor w C).Runs m ∧
      ∀i,i<floor ∨ L.endAddress floor≤ i → (L.phase chip floor w C).image m i=m i :=by
  have ax:=L.bounds floor
  have cut:=L.raw_bound floor same hm hr
  have high:=ax.2.2.2.trans_lt space
  have outLt : L.out floor<2^w:=(Nat.le_add_right ..).trans_lt high
  have role:=RolePorts.any L.B chip floor m old (ax.2.1.trans_lt (ax.2.2.1.trans_lt outLt))
  let mid:=RolePorts.image L.B chip floor m
  have last : (L.gather floor w C).Runs mid := DescentGatheredVectorReshape.exec (L.refs floor C) L.B.hosts L.B.groups L.groups L.radix L.lanes L.bits
    (L.transpose floor) (L.out floor) (L.raw floor) mid early (cut.trans_lt (ax.2.2.1.trans_lt outLt)) (L.room floor space)
  refine ⟨NativePhase.seq_runs _ _ m role.1 last,?_⟩
  intro i outside
  have h1 : i<(L.raw floor).base ∨ (L.raw floor).base+(L.pages*L.lows)*(L.B.hosts*chunks L.B.groups (L.lanes*L.radix))≤ i :=by
    rcases outside with lo|hi
    · exact .inl (lo.trans_le ax.1)
    · exact .inr (cut.trans (ax.2.2.1.trans ((Nat.le_add_right ..).trans (ax.2.2.2.trans hi))))
  have transEnd : L.transpose floor+DescentVectorBookReshape.cells L.pages L.B.hosts L.lows L.groups L.radix L.bits L.lanes≤L.out floor :=
    (L.room floor space).early
  have firstEnd:=ax.1.trans (ax.2.1.trans ax.2.2.1)
  have step:=DescentGatheredVectorReshape.frame (L.refs floor C) L.B.hosts L.B.groups L.groups L.radix L.lanes L.bits
    (L.transpose floor) (L.out floor) (L.raw floor) mid i h1
    (outside.imp (·.trans_le (ax.1.trans ax.2.1)) (fun hi=>transEnd.trans ((Nat.le_add_right ..).trans (ax.2.2.2.trans hi))))
    (outside.imp (·.trans_le firstEnd) (ax.2.2.2.trans ·))
  exact step.trans (role.2.2 i (outside.imp_right (fun hi=>ax.2.1.trans (ax.2.2.1.trans ((Nat.le_add_right ..).trans (ax.2.2.2.trans hi))))))


theorem framed {w} (chip : Bank) (floor : ℕ) (C : Fin L.B.args→Fin L.lows→L.Ref) (m : Memory w)
    (old : chip.Fits w floor) (same : L.B.groups=L.groups*L.radix) (hm : 0<L.lanes) (hr : 0<L.radix)
    (early : ∀p l,((L.refs floor C p l).expr L.B.hosts).inputEnd≤L.start floor)
    (space : L.endAddress floor<2^w) :
    ∀i,i<floor ∨ L.endAddress floor≤ i → (L.phase chip floor w C).image m i=m i :=
  (L.any chip floor C m old same hm hr early space).2

theorem measured_issued {nb mb w} (chip : Bank) (floor : ℕ) (C : Fin L.B.args→Fin L.lows→L.Ref) (m : Memory w)
    (V : Fin L.B.args→Fin L.lows→L.Val nb mb) (data_ : Fin L.B.hosts→Fin L.B.groups→Cell L.B.chipBits)
    (hm : 0<L.lanes) (hr : 0<L.radix) (same : L.B.groups=L.groups*L.radix)
    (space : L.endAddress floor<2^w)
    (measured : ∀p l,Measured (L.refs floor C p l) (L.vals V data_ p l) L.newNodes (L.lanes*L.radix)
      (L.start floor) (RolePorts.image L.B chip floor m)) (arg : Fin L.B.args) (field : Fin 3) (b : Fin L.radix) :
    Reads (L.returned floor arg field b)
      (DescentScalarBookReshape.book (fun l h g=>(L.vals V data_ (finProdFinEquiv (arg,field)) l).book
        L.newNodes h (g.cast same.symm)) b) L.lanes ((L.phase chip floor w C).image m) :=by
  have seen:=DescentGatheredVectorReshape.run (L.refs floor C) (L.vals V data_) (L.transpose floor) (L.out floor)
    L.newNodes (L.raw floor) (RolePorts.image L.B chip floor m) hm hr same (fun g=>g.cast same.symm) (fun _=>rfl)
    measured (L.room floor space)
  exact seen.2.1 (finProdFinEquiv (arg,field)) b

/-- The receiver digit at a live born candidate equals the old host's own short mouth field. -/
theorem born_value {nb mb} (V : Fin L.B.args→Fin L.lows→L.Val nb mb) (chip : Fin L.B.hosts→Fin L.B.groups→Cell L.B.chipBits)
    (arg : Fin L.B.args) (field : Fin 3) (low : Fin L.lows) (here donor : Fin L.B.hosts) (group : Fin L.B.groups)
    (walk : Fin (DescentHaloWalkRAM.breadth L.degree)) (b : Fin (2^L.depth)) (seat : Fin L.B.cap) (party : Fin 6)
    (node : Fin L.newNodes) :
    let i:=finProdFinEquiv (finProdFinEquiv (walk,b),(finSumFinEquiv (.inr (finProdFinEquiv (seat,party))) :
      Fin (L.oldNodes+L.B.cap*6)))
    let val:=L.vals V chip (finProdFinEquiv (arg,field)) low
    let bit:=(encode 1 _).symm (DescentOrdinaryOriginMask.marked (V arg low) here group)
    DescentSortedRoster.indexed (V arg low).walks here walk=some donor →
      bit i≠0 → DescentPackedLocalAtoms.earlier bit i=node.val →
      (encode L.B.bits L.newNodes).symm (val.book L.newNodes here group) node =
        RolePorts.value L.B.bits (pointerAt L.B.demand L.B.grain L.B.scale
          (chipDonor L.B.format (chip donor group) (finProdFinEquiv (b.cast L.blocks_eq.symm,seat))) party arg.val) field :=by
  intro i val bit visit live serial
  unfold Values.book DescentPackedLocalAtoms.pack
  simp only [val, vals, Equiv.symm_apply_apply]
  refine (DescentPackedLocalAtoms.field_at bit _ i live node serial).trans ?_
  have parts := finProdFinEquiv.symm_apply_apply (seat,party)
  have left : (finProdFinEquiv (seat,party)).divNat = seat := congrArg Prod.fst parts
  have right : (finProdFinEquiv (seat,party)).modNat = party := congrArg Prod.snd parts
  simp [i,DescentOrdinaryAtomFieldRAM.bookRoot,DescentOrdinaryAtomFieldRAM.bookBlock,
    DescentOrdinaryAtomFieldRAM.bookItem,item,visit,left,right]

end Layout
end
end Hierarchy.DescentOrdinaryMouthReturn

end OAI
