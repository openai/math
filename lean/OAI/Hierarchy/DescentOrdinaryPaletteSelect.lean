import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! Read each successor's original donor number and return the corresponding primitive token. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint
open DescentSIMDLookup DescentPackedZip
open DescentOrdinaryAtomFieldRAM.ROM DescentPackedColony DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {N K b d H G M w : ℕ}

def applyOrigin (origin : Cell d) (pool : Fin N→Cell b) : Cell b :=
  if origin.val=0 then 0 else if inside : origin.val-1<N then pool ⟨_,inside⟩ else 0

def select (ids : Cell (d*K)) (pool : Cell (b*N)) : Cell (b*K) :=
  encode b K (fun n=>applyOrigin ((encode d K).symm ids n) ((encode b N).symm pool))

private theorem blank (b n : ℕ) : encode b n (fun _=>0)=0:=by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin n=>(0:Cell b))).val=0
  simp []

theorem dead : select (N:=N) (K:=K) (d:=d) (b:=b) 0 0=0:=by
  have dig : (encode d K).symm 0=fun _=>0 := (encode d K).symm_apply_eq.mpr (blank d K).symm
  simp only [select,dig,applyOrigin,Fin.val_zero,ite_true,blank]

theorem selected (ids : Cell (d*K)) (pool : Cell (b*N)) (n : Fin K) (j : Fin N)
    (owned : (((encode d K).symm ids) n).val=j.val+1) :
    (encode b K).symm (select ids pool) n=(encode b N).symm pool j :=by
  simp only [select,Equiv.symm_apply_apply,applyOrigin,owned,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,
    dite_eq_left j.isLt]

theorem padded (ids : Cell (d*K)) (pool : Cell (b*N)) (n : Fin K)
    (vacant : ((encode d K).symm ids) n=0) :
    (encode b K).symm (select ids pool) n=0:=by simp [select,applyOrigin,vacant]

structure Shape where
  donors : ℕ
  nodes : ℕ
  originBits : ℕ
  primitiveBits : ℕ
  blocks : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ

namespace Shape
variable (C : Shape)
local notation "fn" => select (N:=C.donors) (K:=C.nodes) (d:=C.originBits) (b:=C.primitiveBits)
def rows := C.hosts*chunks C.groups C.lanes
def width := (C.originBits*C.nodes+C.primitiveBits*C.donors)*C.lanes
def output (base : ℕ) :=base+2*2^C.width
def roof (base : ℕ) :=C.output base+C.blocks*C.rows+2^Nat.clog 2 (C.rows+1)
def bank (base : ℕ) (x : Fin C.blocks) : Bank :=⟨C.output base+x.val*C.rows,Nat.clog 2 (C.rows+1)⟩
def lut (base : ℕ) := joined (binary fn C.lanes) C.width base id
def term (base : ℕ) (ids pool : Fin C.blocks→Bank) (j : ℕ) : Expr :=
  if h : j<C.blocks then (C.lut base).read (.lookup (ids ⟨_,h⟩) .row) (.lookup (pool ⟨_,h⟩) .row) else .lit 0
def scans (base : ℕ) (ids pool : Fin C.blocks→Bank) :=
  DescentPackedFlowBatch.passes (C.output base) C.rows C.rows (C.term base ids pool) 0 C.blocks
def phase (base : ℕ) (ids pool : Fin C.blocks→Bank) (w : ℕ) : NativePhase w where
  program := (mount (binary fn C.lanes) C.width w base).seq (program w (C.scans base ids pool))
  image := fun m=>result (C.scans base ids pool) (after (binary fn C.lanes) C.width base m)
  ticks := (4+10*(2*2^C.width))+clock (C.scans base ids pool)
  cheap := by
    apply cheap_seq
    · apply DescentOrdinaryAtomFieldRAM.ROM.cheap
    · apply program_cheap

theorem translated (base : ℕ) : C.roof base=base+C.roof 0:=by simp [roof,output,Nat.add_assoc]
theorem base_le (base : ℕ) : base≤C.roof base:=by rw [C.translated];exact Nat.le_add_right ..

theorem pages_room (i : Fin 2) : ((binary fn C.lanes) i).bits≤C.width:=by
  fin_cases i <;> simp [binary,width,Nat.add_mul]

theorem fits {base : ℕ} (ids pool : Fin C.blocks→Bank) (old : ∀x,(ids x).Fits w base ∧ (pool x).Fits w base)
    (room : C.roof base<2^w) (x : Fin C.blocks) :
    DescentPackedZip.Fits (C.lut base) (.lookup (ids x) .row) (.lookup (pool x) .row)
      (C.originBits*C.nodes) (C.primitiveBits*C.donors) C.lanes (C.output base) w:=by
  have low : base≤C.output base:=Nat.le_add_right ..
  have top : C.output base<2^w:=((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans_lt room
  have page (i : Fin 2) :=bank_room (binary fn C.lanes) C.width base (C.output base) i (C.pages_room i) le_rfl top
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ low ⟨(old x).1,trivial⟩,
    ProtocolRAMGeneratedWrite.fits_mono _ low ⟨(old x).2,trivial⟩,page 0,page 1,rfl,rfl⟩

theorem any (base : ℕ) (ids pool : Fin C.blocks→Bank) (m : Memory w)
    (old : ∀x,(ids x).Fits w base ∧ (pool x).Fits w base) (room : C.roof base<2^w) :
    (C.phase base ids pool w).Runs m ∧ ∀ i, i < base ∨ C.roof base ≤ i → (C.phase base ids pool w).image m i=m i:=by
  let mid:=after (binary fn C.lanes) C.width base m
  have low : base≤C.output base:=Nat.le_add_right ..
  have tail : C.output base+C.blocks*C.rows<2^w:=(Nat.le_add_right ..).trans_lt room
  have book:=DescentOrdinaryAtomFieldRAM.ROM.run (binary fn C.lanes) C.width base m ((Nat.le_add_right _ _).trans_lt tail)
  have ok (j : ℕ) (hj : j<C.blocks) : (C.term base ids pool j).Fits w (C.output base):=by
    have q:=C.fits ids pool old room ⟨j,hj⟩
    rw [term,dite_eq_left hj]
    exact ⟨q.apply,q.right,q.shift,q.left⟩
  have pub:=DescentPackedFlowBatch.execute (C.output base) C.rows C.rows C.blocks (C.term base ids pool) mid ok tail le_rfl
  refine ⟨?_,?_⟩
  · intro P R K mach pc reg pins stop rom advice cfg raw enter same
    exact Procedure.Exec.then book.1 pub.1 mach pc reg pins stop rom advice cfg raw enter same
  intro a away
  have prior:=frame (binary fn C.lanes) C.width base m a (away.imp_right (((Nat.le_add_right _ _).trans (Nat.le_add_right ..)).trans ·))
  rcases away with lo|hi
  · exact (pub.2.2 a (lo.trans_le low)).trans prior
  · exact (DescentPackedFlowBatch.above (C.output base) C.rows C.rows (C.term base ids pool) mid 0 C.blocks a le_rfl (by simp only [Nat.zero_add]; exact (Nat.le_add_right _ _).trans hi)).trans prior

end Shape
end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint

end OAI
