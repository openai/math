import OAI.Hierarchy.DescentTerminalPointerInputs
import OAI.Hierarchy.DescentTerminalPointerColumns
import OAI.Hierarchy.DescentTerminalNodeDigit
import OAI.Hierarchy.DescentTerminalPointerFrame
import OAI.Hierarchy.DescentTerminalPointerBasis
import OAI.Hierarchy.DescentSignedCableCodec

namespace OAI
/-! # Producing the entire last scalar argument family from genuine short state pages -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentSIMDLookup DescentOperandStateBanks DescentSharedCableNames ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {D cap N A groups H w d : ℕ}

namespace CellInputs
variable (t : CellInputs D cap N A)
def privateAt (i : Fin (N*A)) : Option ℕ :=
  if t.active i then match t.pointer i with
    | .privateWord a=>some a
    | _=>none
  else none

def argument (q scale psize : ℕ) (i : Fin (N*A)) :=
  if t.active i then convert q cap scale psize (grains t.chips) (present t.privateAt) (t.pointer i) else 0

theorem at_slot (q scale psize : ℕ) (i : Fin (N*A)) (on : t.active i) : t.argument q scale psize i=
    convert q cap scale psize (grains t.chips) (present t.privateAt) (t.pointer i) :=ite_eq_left on
end CellInputs

/-- The original-copy pointer remains immutable until the final remixed cohort
lookup. The matrix and frozen-host roster are scalar fields, shared by group lanes. -/
def decode (D : ℕ) (s : Widths) (pin : ℕ→ℕ→ℕ→ℕ) (raw : Source cap N A d) (g : ℕ) : CellInputs D cap N A where
  n:=digit s.nodes g (raw ncol).val
  arity j:=s.nodeDigit s.arity j.val g (raw (acol j)).val
  pointer j:=
    let read:=fun f : Fin 4=>s.nodeDigit (s.pointer f) (nodeOf j).val g (raw (pcol f j)).val
    if read 0=0 then .privateWord (read 2)
    else if read 0=1 then .cable (read 1) (read 2) (read 3)
    else .pin (pin (raw mcol).val (raw fcol).val (read 2)) (read 3)
  chips j:=DescentSignedCableCodec.decode D cap ((digit (DescentSignedCableCodec.width D cap) g (raw (scol j)).val:ℕ):Cell _)

def output (cap N A D groups d bits q scale psize : ℕ) (s : Widths) (rank : ℕ→ℕ→ℕ→ℕ)
    (x : Source cap N A d) : Cell ((bits*(N*A))*groups) :=
  encode _ groups (fun g=>encode bits (N*A) (fun j=>((decode D s rank x g.val).argument q scale psize j:Cell bits)))

theorem issued (cap N A D groups bits q scale psize : ℕ) (s : Widths) (rank : ℕ→ℕ→ℕ→ℕ)
    (base : ℕ) (src : Fin (columns cap N A)→ Bank) (mem : Memory w)
    (room : DescentTerminalPointerFrame.Room src base d H w) (board : Fin H→ Source cap N A d)
    (read : ∀h j,mem ((src j).base+h.val)=((board h j).val:Word w))
    (fits : (bits*(N*A))*groups≤w) :
    let family:=output cap N A D groups d bits q scale psize s rank
    let n:=columns cap N A
    let start:=base+DescentTerminalPointerFrame.size n d
    let done:=DescentTerminalPointerFrame.result base src H family mem
    (DescentTerminalPointerFrame.program w base src H family).Exec mem done
      ((4+10*DescentTerminalPointerFrame.size n d)+(4+H*(16+26*n))) ∧
    CheapCode (DescentTerminalPointerFrame.program w base src H family) ∧
    (∀h : Fin H,done (start+h.val)=((family (board h)).val:Word w)) ∧
    (∀(h : Fin H) (g : Fin groups) (j : Fin (N*A)),
      let t:=decode D s rank (board h) g.val
      t.argument q scale psize j < 2^bits→
        digit bits j.val (digit (bits*(N*A)) g.val (done (start+h.val)).val)=t.argument q scale psize j) ∧
    ∀j,j < base ∨ start+H≤j→ done j=mem j := by
  dsimp only
  let f:=output cap N A D groups d bits q scale psize s rank
  obtain ⟨exec,cheap,frame⟩:=DescentTerminalPointerFrame.run base src f mem room
  have printed:=DescentTerminalPointerFrame.read base src f mem room board read
  refine ⟨exec,cheap,printed,?_,frame⟩
  intro h g j small
  rw [printed,Fin.val_cast_of_lt ((f (board h)).isLt.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) fits))]
  simp only [f,output,digit_encode,Fin.val_cast_of_lt small]

end
end Hierarchy.DescentTerminalPointerDigits

end OAI
