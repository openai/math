import OAI.Hierarchy.DescentExteriorCalendarTableData
import OAI.Hierarchy.DescentExteriorShelfNumbers

namespace OAI
/-! # One common selected matrix register installs the literal service for all slabs -/
namespace Hierarchy.DescentExteriorShelf
open DescentGL DescentExterior DescentExteriorMatrixUpdate Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w j r t e : ℕ}
local notation "H" => span j r t e
local notation "k" => j+(j+r)

def broadcast (atWord:ℕ) : Expr := .lookup ⟨atWord,0⟩ (.lit 0)
def issued (origin atWord:ℕ) (m:Memory w) := image (origin+span j r t e) e (broadcast atWord) m

theorem broadcast_run (origin atWord:ℕ) (m:Memory w) (positive:0<w)
    (below:atWord<origin+H) (capacity:origin+H+e<2^w) :
    (scan w (origin+H) e (broadcast atWord)).Exec m (issued (j:=j) (r:=r) (t:=t) (e:=e) origin atWord m)
      (4+16*e) ∧ CheapCode (scan w (origin+H) e (broadcast atWord)) := by
  have safe:(broadcast atWord).Fits w (origin+H):=by
    refine ⟨⟨?_,?_,?_⟩,trivial⟩
    · change 0 < 1
      decide
    · change 1 < 2^w
      exact Nat.one_lt_two_pow (by omega)
    · change atWord+1 ≤ _
      omega
  have ran : (scan w (origin+H) e (broadcast atWord)).Exec m
      (image (origin+H) e (broadcast atWord) m) (4+e*(2*(broadcast atWord).work+4)) :=
    scan_exec (origin+H) e (broadcast atWord) m safe capacity
  have clock : 4+e*(2*(broadcast atWord).work+4) = 4+16*e :=
    congrArg (4+·) (Nat.mul_comm ..)
  rw [clock] at ran
  exact ⟨@ran, @scan_cheap w (origin+H) e (broadcast atWord)⟩

end
end Hierarchy.DescentExteriorShelf

/-! # The native dated matrix accumulator and the final slab broadcast -/
namespace Hierarchy.DescentExteriorShelf
open DescentGL DescentExterior DescentExteriorMatrixUpdate Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w e j r t : ℕ}
set_option quotPrecheck false
local notation "H" => span j r t e

def publish (j r t e w origin age : ℕ) (cells : ℕ→Cell) :=
  (dated cells w age).seq (scan w (origin+span j r t e) e (broadcast (cells age).old.base))

def published (j r t e origin age : ℕ) (cells : ℕ→Cell) (m : Memory w) :=
  issued (j:=j) (r:=r) (t:=t) (e:=e) origin (cells age).old.base (reached cells m age)

/-- The bounded native execution is total even for headers which fail verification. -/
theorem publish_run (origin age dim : ℕ) (sizes : ℕ→ℕ) (cells : ℕ→Cell) (m : Memory w)
    (fits : ∀i<age,(cells i).Room w dim (sizes i)) (positive : 0<w)
    (before : (cells age).old.base < origin+H) (room : origin+H+e < 2^w) :
    (publish j r t e w origin age cells).Exec m (published j r t e origin age cells m)
      ((4+58*age)+(4+16*e)) ∧ CheapCode (publish j r t e w origin age cells) := by
  have first:=execution cells m age dim sizes fits
  have last:=broadcast_run origin (cells age).old.base (reached cells m age) positive before room
  refine ⟨?_,cheap_seq first.2 last.2⟩
  intro P R K machine
  exact Procedure.Exec.then first.1 last.1 machine

theorem reached_frame (cells : ℕ→Cell) (m : Memory w) (age a : ℕ)
    (away : ∀i<age,(cells i).updated ≠ a) : reached cells m age a=m a := by
  induction age with
  | zero=>rfl
  | succ i ih=>
    have disj : ¬((cells i).updated ≤ a ∧ a < (cells i).updated+1):=by
      have h:=away i (Nat.lt_succ_self _)
      omega
    simp only [reached,Cell.after,ProtocolRAM.image,fillSegment,ite_eq_right disj]
    exact ih (fun k hk=>away k (by omega))

/-- Any sticky verdict or other low register survives both the dates and the matrix publication. -/
theorem published_frame (origin age : ℕ) (cells : ℕ→Cell) (m : Memory w) (a : ℕ)
    (away : ∀i<age,(cells i).updated ≠ a) (outside : a < origin+H ∨ origin+H+e ≤ a) :
    published j r t e origin age cells m a=m a := by
  have disj : ¬(origin+H ≤ a ∧ a < origin+H+e):=by omega
  simp only [published,issued,ProtocolRAM.image,fillSegment,ite_eq_right disj]
  exact reached_frame cells m age a away

end
end Hierarchy.DescentExteriorShelf

/-! # The physically retained per-date rotation words give the complete matrix execution -/
namespace Hierarchy.DescentExteriorMatrixUpdate
open DescentGL DescentExterior DescentPackedColony.Phase.Arena
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
structure Reel where
  old : ℕ→ℕ
  rotation : ℕ→ℕ
  table : ℕ→ℕ
  output : ℕ→ℕ
  localWidth : ℕ→ℕ

def Reel.cells (P : Reel) (d age : ℕ) : Cell :=
  cell (P.old age) (P.rotation age) (P.table age) (P.output age) d (P.localWidth age)

end
end Hierarchy.DescentExteriorMatrixUpdate

/-! # Literal start word and the fixed total execution of the final cumulative matrix pass -/
namespace Hierarchy.DescentExteriorMatrixUpdate
open DescentColonies DescentGL DescentExterior DescentExteriorShelf
open scoped Classical Fin.CommRing
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w j r t e : ℕ}

def initialCode (d : ℕ) := matrixCode (Spine.start (fun _ : Unit=>(0 : Bits d)) (fun _=>())).matrix

theorem initialCode_eq {E A : Type} {d : ℕ} (raw : E→Bits d) (host : E→A) :
    initialCode d=matrixCode (Spine.start raw host).matrix := rfl

def initialized (old d : ℕ) (m : Memory w) := image old 1 (.lit (initialCode d).val) m

theorem «initialize» (old d : ℕ) (m : Memory w) (space : old+1 < 2^w) :
    (scan w old 1 (.lit (initialCode d).val)).Exec m (initialized old d m) 10 ∧
    CheapCode (scan w old 1 (.lit (initialCode d).val)) ∧
    initialized old d m old=((initialCode d).val:Word w) ∧
    ∀a,old ≠ a→initialized old d m a=m a := by
  refine ⟨@scan_exec w old 1 (.lit (initialCode d).val) m trivial space,@scan_cheap w old 1 (.lit (initialCode d).val),?_,?_⟩
  · simp [initialized,ProtocolRAM.image,fillSegment,Expr.eval]
  · intro a apart
    have absent : ¬(old ≤ a ∧ a < old+1):=by omega
    rw [initialized,ProtocolRAM.image,fillSegment,ite_eq_right absent]

structure Reel.Room (P : Reel) (w d age fence origin : ℕ) : Prop where
  boot : fence ≤ P.old 0
  startLow : P.old 0 < origin
  startFit : P.old 0+1 < 2^w
  previous : ∀i<age,P.old i < P.output i
  rotation : ∀i<age,P.rotation i < P.output i
  table : ∀i<age,P.table i+pages d (P.localWidth i) ≤ P.output i
  fit : ∀i<age,P.output i+1 < 2^w
  retained : ∀i<age,fence ≤ P.output i
  high : ∀i<age,P.output i < origin
  join : ∀i<age,P.output i=P.old (i+1)
  address : P.old age < origin

def Reel.program (P : Reel) (j r t e w d age origin : ℕ) :=
  (scan w (P.old 0) 1 (.lit (initialCode d).val)).seq
    (publish j r t e w origin age (P.cells d))

def Reel.result (P : Reel) (j r t e d age origin : ℕ) (m : Memory w) :=
  published j r t e origin age (P.cells d) (initialized (P.old 0) d m)

theorem Reel.run (P : Reel) (d age fence origin : ℕ) (m : Memory w)
    (physical : P.Room w d age fence origin) (pos : 0 < w)
    (bounded : origin+span j r t e+e < 2^w) :
    (P.program j r t e w d age origin).Exec m (P.result j r t e d age origin m)
      (10+((4+58*age)+(4+16*e))) ∧ CheapCode (P.program j r t e w d age origin) ∧
    ∀a,a < fence→P.result j r t e d age origin m a=m a := by
  have ready:=«initialize» (P.old 0) d m physical.startFit
  have charge:=fun i (hi : i<age)=>cell_room (P.old i) (P.rotation i) (P.table i) (P.output i) d
    (P.localWidth i) w (physical.previous i hi) (physical.rotation i hi) (physical.table i hi) (physical.fit i hi)
  have last:=publish_run (j:=j) (r:=r) (t:=t) (e:=e) origin age d P.localWidth (P.cells d)
    (initialized (P.old 0) d m) charge pos (by change P.old age < _;have:=physical.address;omega) bounded
  refine ⟨?_,cheap_seq ready.2.1 last.2,?_⟩
  · intro labels regs keys machine
    exact Procedure.Exec.then ready.1 last.1 machine
  intro a low
  have initial : P.old 0 ≠ a:=by have:=physical.boot;omega
  have lower : a < origin:=low.trans_le (physical.boot.trans physical.startLow.le)
  exact (published_frame (j:=j) (r:=r) (t:=t) (e:=e) origin age (P.cells d) _ a
    (fun i hi=>by change P.output i ≠ a;have:=physical.retained i hi;omega) (.inl (by omega))).trans
    (ready.2.2.2 a initial)

end
end Hierarchy.DescentExteriorMatrixUpdate

end OAI
