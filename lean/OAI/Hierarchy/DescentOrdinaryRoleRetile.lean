import OAI.Hierarchy.DescentOverlapTariff
import OAI.Hierarchy.DescentPackedColumnHardware
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! Convert the whole finite role roster of every old block to the consuming port pitch. -/
namespace Hierarchy.DescentOrdinaryRoleRetile
open DescentSIMDLookup DescentPackedColony
open DescentSixParty.Chronology ProtocolRAM DescentPackedZip DescentColonies.SplitRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
structure Layout where
  blocks : ℕ
  hosts : ℕ
  groups : ℕ
  beforeLanes : ℕ
  afterLanes : ℕ
  bits : ℕ

namespace Layout
variable (L : Layout) (base : ℕ) (prior : Fin L.blocks→Bank)
def rows:=L.hosts*chunks L.groups L.afterLanes
def output:=Overlap.dest base L.hosts L.groups L.beforeLanes L.afterLanes L.bits
set_option quotPrecheck false
local notation "h" => L.hosts
local notation "g" => L.groups
local notation "a" => L.bits
local notation "out" => L.output base
local notation "nrows" => L.rows
local notation "n" => L.blocks
def roof := out+n*nrows+2^(Nat.clog 2 (nrows+1))
theorem translated : L.roof base=base+L.roof 0:=by
  simp only [roof,output,Overlap.dest,Overlap.dictBase,Nat.zero_add,Nat.add_assoc]

theorem base_le : base≤L.roof base:=by rw [translated];exact Nat.le_add_right ..

def bank (x : Fin L.blocks) : Bank := ⟨out+x.val*nrows,Nat.clog 2 (nrows+1)⟩
def expr (i : ℕ) : Expr :=
  if live:i<n then Overlap.body base h g L.beforeLanes L.afterLanes a (prior ⟨i,live⟩) else .lit 0

def scans:=DescentPackedFlowBatch.passes out nrows nrows (expr L base prior) 0 n
local notation "warm" m => Overlap.seeded base h g L.beforeLanes L.afterLanes a m
def phase (w : ℕ) : NativePhase w where
  program:=(Overlap.tables base h g L.beforeLanes L.afterLanes a w).seq (ProtocolRAM.program w (scans L base prior))
  ticks:=(8+10*(out-base))+clock (scans L base prior)
  image:=fun m=>result (scans L base prior) (warm m)
  cheap:=by
    apply cheap_seq
    · apply cheap_seq <;> apply DescentOrdinaryAtomFieldRAM.ROM.cheap
    · apply program_cheap

variable {w:ℕ} (m:Memory w) (old:∀x,(prior x).Fits w base) (room:roof L base<2^w)
include room in
private theorem sufficient : Overlap.finish base h g L.beforeLanes L.afterLanes a < 2^w := by
  have size:nrows≤2^(Nat.clog 2 (nrows+1)):=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  change out+nrows<2^w
  unfold roof at room
  omega

include m old room in
private theorem expr_fits (i : ℕ) (hi : i<n) : (expr L base prior i).Fits w out := by
  obtain ⟨_,ptr,lut,_,_,_⟩:=Overlap.resident base m (sufficient L base room)
  have early:=old ⟨i,hi⟩
  have before : base≤out:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have fit:(prior ⟨i,hi⟩).Fits w out:=⟨early.1,early.2.1,early.2.2.trans before⟩
  rw [expr,dite_eq_left hi]
  apply fits_total
  intro j
  exact ⟨⟨ptr _,trivial⟩,trivial,trivial,lut _,⟨ptr _,trivial⟩,fit,ptr _,trivial⟩

include room in
private theorem last_page : out+n*nrows<2^w:=
  (Nat.le_add_right (out+n*nrows) (2^Nat.clog 2 (nrows+1))).trans_lt room

include old room in
theorem any : (phase L base prior w).Runs m ∧
    ∀i,i<base ∨ roof L base ≤ i → (phase L base prior w).image m i=m i :=by
  have mount:=Overlap.resident base m (sufficient L base room)
  have pass:=DescentPackedFlowBatch.execute out nrows nrows n (expr L base prior) (warm m)
    (expr_fits L base prior m old room) (last_page L base room) le_rfl
  have before:base≤out:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  refine ⟨?_,?_⟩
  · intro P R K mach pc reg pins stop rom advice cfg raw enter same
    exact Procedure.Exec.then mount.1 pass.1 mach pc reg pins stop rom advice cfg raw enter same
  intro i away
  rcases away with low|high
  · exact (pass.2.2 i (low.trans_le before)).trans (mount.2.2.2.2.2 i (.inl low))
  · have end_:out+n*nrows ≤ i :=(Nat.le_add_right (out+n*nrows) (2^Nat.clog 2 (nrows+1))).trans high
    exact (DescentPackedFlowBatch.above out nrows nrows _ (warm m) 0 n i le_rfl (by simpa using end_)).trans
      (mount.2.2.2.2.2 i (.inr ((Nat.le_add_right ..).trans end_)))

include room in
theorem placed (x : Fin L.blocks) :
    (L.bank base x).Fits w (L.roof base) ∧ nrows≤(L.bank base x).size:=by
  have bound:=Nat.mul_le_mul_right nrows x.isLt.le
  have end_:(L.bank base x).base+(L.bank base x).size≤L.roof base:=by
    exact Nat.add_le_add_right (Nat.add_le_add_left bound out) (2^Nat.clog 2 (nrows+1))
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (end_.trans_lt room),end_⟩,
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)⟩

include old room in
theorem reads (x : Fin L.blocks) (value : Fin h→Fin g→Cell a) (live : 0<L.beforeLanes)
    (capacity : h*chunks g L.beforeLanes≤(prior x).size) (read : Reads (prior x) value L.beforeLanes m) :
    Reads (L.bank base x) value L.afterLanes ((L.phase base prior w).image m) :=by
  have limit:=sufficient L base room
  have scan:=DescentPackedFlowBatch.execute out nrows nrows n (L.expr base prior) (warm m)
    (expr_fits L base prior m old room) (last_page L base room) le_rfl
  have ex:L.expr base prior x.val=Overlap.body base h g L.beforeLanes L.afterLanes a (prior x):=by
    simp only [expr,dite_eq_left x.isLt]
  intro r
  have hit:=scan.2.1 x (row h g L.afterLanes r)
  rw [ex] at hit
  have native:=Overlap.read base (prior x) m value live (old x) capacity read limit r
  have one:=ProtocolRAMGeneratedWrite.read_image out nrows (Overlap.body base h g L.beforeLanes L.afterLanes a (prior x)) (warm m) (row h g L.afterLanes r)
  exact hit.trans (one.symm.trans native)

end Layout
end
end Hierarchy.DescentOrdinaryRoleRetile

end OAI
