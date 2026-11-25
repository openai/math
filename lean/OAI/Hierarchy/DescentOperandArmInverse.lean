import OAI.Hierarchy.DescentOperandRouteRAM
import OAI.Hierarchy.DescentVenueRAM

namespace OAI
/-! # The inverse dictionary from a selected old cable to its demand arm -/

namespace Hierarchy.DescentOperandArmInverse
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentOrdinaryDestRAM
open scoped Fin.CommRing Classical
noncomputable section

structure Layout where
  pairs : Bank
  dest : ℕ
  addresses : ℕ
  values : ℕ

variable {w ne n : ℕ} (s : Layout)

structure Fits (s : Layout) (w ne n : ℕ) : Prop where
  pairCount : 9*n≤ s.pairs.size
  source : s.pairs.base+s.pairs.size≤ s.dest
  table : s.dest+ne≤ s.addresses
  scratch : s.addresses+n≤ s.values
  room : s.values+n<2^w

private def add (x y : Expr) := Expr.op .add x y
def pairEdge (side : Fin 2) := Expr.lookup s.pairs (add (times 9 .row) (.lit (1+side.val)))
def address (side : Fin 2) := add (.lit s.dest) (pairEdge s side)
def value (ne : ℕ) (side : Fin 2) := add (.lit ne) (add (times 10 .row) (.lit side.val))

def arm (ne : ℕ) (i : Fin n) (side : Fin 2) := ne+10*i.val+side.val

variable (pick : Fin n × Fin 2 ↪ Fin ne)
def addr (side : Fin 2) (i : Fin n) := s.dest+(pick (i,side)).val

def Stored (m : Memory w) := ∀ (i : Fin n) (t : Fin 2),
  m (s.pairs.base+(9*i.val+(1+t.val)))=(pick (i,t)).val

def step (w n ne : ℕ) (side : Fin 2) :=
  ProtocolRAMGeneratedWrite.program w s.addresses s.values n (address s side) (value ne side)

def after (side : Fin 2) (m : Memory w) :=
  ProtocolRAMGeneratedWrite.image s.addresses s.values (address s side) (value ne side)
    (addr s pick side) (fun i=>(arm ne i side:Word w)) m

private theorem times_end (k : ℕ) : (times k .row).inputEnd=0 := by
  induction k with
  | zero=>rfl
  | succ k ih=>simp [times,Expr.inputEnd,ih]

theorem step_exec (fit : Fits s w ne n) (side : Fin 2) (m : Memory w) (load : Stored s pick m) :
    (step s w n ne side).Exec m (after s pick side m)
      (ProtocolRAMGeneratedWrite.work n (address s side) (value ne side)) := by
  have room:=fit.room
  have sep:=fit.scratch
  have target:=fit.table
  have source:=fit.source
  have count:=fit.pairCount
  apply ProtocolRAMGeneratedWrite.run
  · apply Expr.fits_of_inputEnd _ _ (by omega)
    simp [address,pairEdge,add,Expr.inputEnd,times_end];omega
  · apply Expr.fits_of_inputEnd _ _ (by omega)
    simp [value,add,Expr.inputEnd,times_end]
  · exact sep
  · exact room
  · intro i
    have k:=i.isLt
    have t:=side.isLt
    have lookup: s.pairs.read m ((9*i.val+(1+side.val):ℕ):Word w)=(pick (i,side)).val :=
      (DescentVenueRAM.bank_at _ _ _ (by omega) (by omega)).trans (load i side)
    change (s.dest:Word w)+s.pairs.read m ((times 9 .row).eval m (i.val:Word w)+((1+side.val:ℕ):Word w))=_
    rw [times_eval]
    push_cast at lookup ⊢
    simpa [addr,Expr.eval] using congrArg (fun x : Word w=>(s.dest:Word w)+x) lookup
  · intro i
    change (ne:Word w)+((times 10 .row).eval m _+(side.val:Word w))=_
    rw [times_eval]
    simp [arm,Expr.eval,Nat.cast_add,Nat.cast_mul,add_assoc]
  · intro i;have hi:=(pick (i,side)).isLt;unfold addr;omega
  · intro i j;have hj:=(pick (j,side)).isLt;unfold addr;omega
  · intro i j;have hj:=(pick (j,side)).isLt;unfold addr;omega

theorem read_arm (side : Fin 2) (m : Memory w) (i : Fin n) :
    after s pick side m (addr s pick side i)=(arm ne i side:Word w) :=
  ProtocolRAMGeneratedWrite.read _ _ _ _ _ _ _ (fun _i _j h=>
    congrArg Prod.fst (pick.injective (Fin.ext (Nat.add_left_cancel h)))) i

theorem frame (fit : Fits s w ne n) (side : Fin 2) (m : Memory w) (a : ℕ)
    (low : a<s.addresses) (away : ∀i,a≠addr s pick side i) :
    after s pick side m a=m a :=
  ProtocolRAMGeneratedWrite.frame _ _ _ _ _ _ _ _ away (.inl low)
    (.inl (by have:=fit.scratch;omega))

def program (w ne n : ℕ) :=
  ((scan w s.dest ne .row).seq (step s w n ne 0)).seq (step s w n ne 1)

def output (m : Memory w) := after s pick 1 (after s pick 0 (image s.dest ne .row m))

def ticks (ne n : ℕ) := (4+ne*(2*Expr.row.work+4))+
  ProtocolRAMGeneratedWrite.work n (address s 0) (value ne 0)+
  ProtocolRAMGeneratedWrite.work n (address s 1) (value ne 1)

private theorem pair_low (fit : Fits s w ne n) (i : Fin n) (t : Fin 2) :
    s.pairs.base+(9*i.val+(1+t.val))<s.dest := by
  have:=fit.pairCount;have:=fit.source;have:=i.isLt;have:=t.isLt;omega

theorem execute (fit : Fits s w ne n) (m : Memory w) (load : Stored s pick m) :
    (program s w ne n).Exec m (output s pick m) (ticks s ne n) := by
  let initial:=image s.dest ne .row m
  have limit : s.dest+ne<2^w := by
    have := fit.table
    have := fit.scratch
    have := fit.room
    omega
  have init : (scan w s.dest ne .row).Exec m initial (4+ne*(2*Expr.row.work+4)) := by
    intro P R K machine
    exact scan_exec (w:=w) s.dest ne .row m trivial limit machine
  have fields : Stored s pick initial := by
    intro i t
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (pair_low s fit i t))).trans (load i t)
  have retained : Stored s pick (after s pick 0 initial) := by
    intro i t
    have low := pair_low s fit i t
    exact (frame s pick fit 0 initial _ (by have := fit.table; omega)
      (by intro j; unfold addr; omega)).trans (fields i t)
  intro P R K machine
  exact Procedure.Exec.then (Procedure.Exec.then init (step_exec s pick fit 0 initial fields))
    (step_exec s pick fit 1 (after s pick 0 initial) retained) machine

/-- At a selected operand only its destination leg is redirected to this new arm.
The source leg continues to use the original ordinal. -/
theorem selected (fit : Fits s w ne n) (m : Memory w) (i : Fin n) (side : Fin 2) :
    output s pick m (addr s pick side i)=(arm ne i side:Word w) := by
  fin_cases side
  · rw [output,frame s pick fit]
    · exact read_arm s pick _ _ i
    · have:=fit.table;have:=(pick (i,0)).isLt;unfold addr;omega
    · intro j h
      have eqn:=pick.injective (Fin.ext (Nat.add_left_cancel h))
      have bad : (0:Fin 2)=1 := congrArg Prod.snd eqn
      exact (by decide : (0:Fin 2)≠1) bad
  · exact read_arm s pick 1 _ i

theorem untouched (fit : Fits s w ne n) (m : Memory w) (e : Fin ne)
    (unpicked : ∀i t,e≠pick (i,t)) : output s pick m (s.dest+e.val)=(e.val:Word w) := by
  have low : s.dest+e.val<s.addresses := by have:=e.isLt;have:=fit.table;omega
  have separate (t : Fin 2) (i : Fin n) : s.dest+e.val≠addr s pick t i :=
    fun h=>unpicked i t (Fin.ext (Nat.add_left_cancel h))
  exact (frame s pick fit _ _ _ low (separate 1)).trans ((frame s pick fit _ _ _ low (separate 0)).trans
    (ProtocolRAMGeneratedWrite.read_image s.dest ne .row _ e))

end
end Hierarchy.DescentOperandArmInverse

end OAI
