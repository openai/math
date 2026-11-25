import OAI.Hierarchy.DescentPrivateEdgeCounter
import OAI.Hierarchy.ProtocolRAMStaticPorts

namespace OAI
/-! # Native exponent from accumulated private bits and the count of occupied private words -/

namespace Hierarchy.DescentPrivateExponentRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentPrivateEdgeCounter
open scoped Fin.CommRing

structure Banks where
  totalBits : ℕ
  usedWords : ℕ
  usedBits : ℕ
  deadBits : ℕ

variable {w : ℕ}

def Banks.minus (B : Banks) := Expr.op .sub (cell B.totalBits) (cell B.usedBits)

export Banks (minus)

def Banks.program (B : Banks) (w p : ℕ) :=
  (ProtocolRAMStaticPorts.program w B.usedBits 1 p (cell B.usedWords)).seq
    (scan w B.deadBits 1 (minus B))

export Banks (program)

def Banks.steps (B : Banks) (p : ℕ) :=
  ProtocolRAMStaticPorts.work 1 p (cell B.usedWords)+(4+1*(2*(minus B).work+4))

export Banks (steps)

theorem steps_eq (B : Banks) (p : ℕ) : steps B p=56+4*ProtocolRAMPortScale.bitWidth p := by
  simp [steps,ProtocolRAMStaticPorts.work,minus,cell,Expr.work]
  omega

structure Banks.Room (B : Banks) (w : ℕ) : Prop where
  volume : B.totalBits<B.usedBits
  active : B.usedWords<B.usedBits
  temp : B.usedBits<B.deadBits
  endMem : B.deadBits+1<2^w

export Banks (Room)

def index (used : ℕ) : Fin 1→Fin (used+1) := fun _=>⟨used,Nat.lt_succ_self _⟩

def Banks.scaled (B : Banks) (p used : ℕ) (m : Memory w) :=
  ProtocolRAMStaticPorts.image B.usedBits p (index used) m

export Banks (scaled)

def Banks.result (B : Banks) (p used : ℕ) (m : Memory w) :=
  ProtocolRAM.image B.deadBits 1 (minus B) (scaled B p used m)

export Banks (result)

private theorem cell_fits {a out : ℕ} (far : a<out) (room : 1<2^w) : (cell a).Fits w out :=
  ⟨⟨by simp [Bank.size],by simpa [Bank.size] using room,by simpa [Bank.size] using far⟩,trivial⟩

theorem Banks.run (B : Banks) (p used : ℕ) (m : Memory w) (space : Room B w)
    (seen : m B.usedWords=(used:Word w)) :
    (program B w p).Exec m (result B p used m) (steps B p) := by
  have last:=space.endMem
  have t:=space.temp
  have v:=space.volume
  have u:=space.active
  have hw : 1<2^w := by omega
  have scale : (ProtocolRAMStaticPorts.program w B.usedBits 1 p (cell B.usedWords)).Exec m (scaled B p used m) (ProtocolRAMStaticPorts.work 1 p (cell B.usedWords)) := ProtocolRAMStaticPorts.run B.usedBits p (index used) (cell B.usedWords) m
    (cell_fits u hw) (by omega) (fun i=>by rw [cell_read];exact seen)
  have finish : (scan w B.deadBits 1 (minus B)).Exec (scaled B p used m) (result B p used m) (4+1*(2*(minus B).work+4)) := scan_exec B.deadBits 1 (minus B) (scaled B p used m)
    (show (minus B).Fits w B.deadBits from ⟨cell_fits (by omega) hw,cell_fits t hw⟩) last
  intro P R C M pc reg pub exit rom advice cfg raw enter equal
  exact Procedure.Exec.then scale finish M pc reg pub exit rom advice cfg raw enter equal

export Banks (run)

theorem Banks.read (B : Banks) (p used allBits : ℕ) (m : Memory w) (space : Room B w)
    (bits : m B.totalBits=(allBits:Word w)) (live : used*p≤allBits) :
    result B p used m B.deadBits=((allBits-used*p:ℕ):Word w) := by
  have val:=ProtocolRAMGeneratedWrite.read_image B.deadBits 1 (minus B) (scaled B p used m) (0:Fin 1)
  rw [show result B p used m B.deadBits=(minus B).eval (scaled B p used m) 0 by simpa [result] using val]
  change (cell B.totalBits).eval (scaled B p used m) 0-(cell B.usedBits).eval (scaled B p used m) 0=_
  rw [cell_read,cell_read]
  have atScale:=ProtocolRAMStaticPorts.read B.usedBits p (index used) m (0:Fin 1)
  rw [show scaled B p used m B.usedBits=((used*p:ℕ):Word w) by simpa [scaled,index] using atScale]
  rw [scaled,ProtocolRAMStaticPorts.frame _ _ _ _ _ (.inl space.volume),bits,Nat.cast_sub live]

export Banks (read)

theorem Banks.frame (B : Banks) (p used : ℕ) (m : Memory w) (a : ℕ)
    (keepTemp : a≠B.usedBits) (keepOut : a≠B.deadBits) :
    result B p used m a=m a := by
  rw [result,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega),scaled,
    ProtocolRAMStaticPorts.frame _ _ _ _ _ (by omega)]

export Banks (frame)

end Hierarchy.DescentPrivateExponentRAM

end OAI
