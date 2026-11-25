import OAI.Hierarchy.DescentTerminalSortRAM
import OAI.Hierarchy.DescentTerminalSortLex
import OAI.Hierarchy.ProbeStageColumnScan

namespace OAI
/-! # Form three measured old-edge keys and stably publish original edge IDs -/

namespace Hierarchy.DescentOldOccurrenceRAM
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w n g t : ℕ}

def bank (base n bits j : ℕ) : Bank := ⟨base+j*n,bits⟩
def scratch (base n bits : ℕ) := base+2*n+2^bits
def keyPass (base n : ℕ) (keys : Fin 3 → Expr) := columns n base (List.ofFn keys)

def program (w base n g t bits : ℕ) (keys : Fin 3 → Expr) : Procedure w :=
  (ProtocolRAM.program w (keyPass base n keys)).seq
    (DescentTerminalSortRAM.program w (scratch base n bits) n t t (g+1) bits
      (bank base n bits 0) (bank base n bits 1) (bank base n bits 2))

def ticks (base n g t : ℕ) (keys : Fin 3 → Expr) :=
  clock (keyPass base n keys)+DescentTerminalSortRAM.time n t t (g+1)

theorem ticks_le (base n g t limit : ℕ) (keys : Fin 3 → Expr) (cost : ∀j,(keys j).work ≤ limit) :
    ticks base n g t keys ≤ 4+3*(4+n*(2*limit+4))+(93+243*n+18*(t+t+(g+1))) := by
  have bound := columns_clock n base limit (List.ofFn keys) (by
    intro e he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    exact cost j)
  simpa only [ticks,keyPass,DescentTerminalSortRAM.time_eq,List.length_ofFn] using
    Nat.add_le_add_right bound (93+243*n+18*(t+t+(g+1)))

def finish (base n g t bits : ℕ) := DescentTerminalSortRAM.endAddress (scratch base n bits) n t t (g+1) bits
def output (base n g t bits : ℕ) := DescentTerminalSortRAM.output (scratch base n bits) n t t (g+1) bits

def state (base bits : ℕ) (keys : Fin 3 → Expr)
    (origin : Fin n → Fin (g+1)) (mid low : Fin n → Fin t) (m : Memory w) :=
  DescentTerminalSortRAM.state (scratch base n bits) bits
    (bank base n bits 0) (bank base n bits 1) (bank base n bits 2)
    origin mid low (result (keyPass base n keys) m)

/-- The map is sorted-position to original edge index. Inactive rows share a
sentinel origin and occur after every occupied source. -/
theorem run (base bits : ℕ) (keys : Fin 3 → Expr)
    (origin : Fin n → Fin (g+1)) (mid low : Fin n → Fin t) (m : Memory w)
    (readers : ∀j,(keys j).Fits w base)
    (inputs : ∀i : Fin n,∀j : Fin 3,(keys j).eval m (i.val:Word w)=
      ((![ (origin i).val,(mid i).val,(low i).val ] j : ℕ):Word w))
    (fits : n≤2^bits) (room : finish base n g t bits<2^w) :
    let o := state base bits keys origin mid low m
    (program w base n g t bits keys).Exec m o (ticks base n g t keys) ∧
      (∀i : Fin n,(output base n g t bits).read o (i.val:Word w)=
        ((DescentTerminalSortRAM.order origin mid low i).val:Word w)) ∧
      ∀x < base,o x=m x := by
  intro o
  let a := result (keyPass base n keys) m
  let start := scratch base n bits
  have last : base+2*n+2^bits < 2^w := by
    unfold finish at room
    rw [DescentTerminalSortRAM.end_eq] at room
    dsimp [scratch] at room
    omega
  have canRead : ∀ e∈List.ofFn keys,e.Fits w base := by
    intro e he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    exact readers j
  have pre : (ProtocolRAM.program w (keyPass base n keys)).Exec m a (clock (keyPass base n keys)) :=
    columns_exec (List.ofFn keys) m (columns_safe _ (le_refl base) canRead (by simp;omega))
  have posted (i : Fin n) (j : Fin 3) : (bank base n bits j.val).read a (i.val:Word w)=
      ((![ (origin i).val,(mid i).val,(low i).val ] j:ℕ):Word w) := by
    have rd := columns_read (List.ofFn keys) m (le_refl base) canRead j.val (by simp) i
    change a ((base+j.val*n)+(i.val:Word w).val%(2^bits))=_
    rw [Fin.val_cast_of_lt (by have := i.isLt;omega),Nat.mod_eq_of_lt (i.isLt.trans_le fits)]
    simp only [List.getElem_ofFn] at rd
    exact rd.trans (inputs i j)
  have bf (j : Fin 3) : (bank base n bits j.val).Fits w start := by
    have le : j.val*n ≤ 2*n := Nat.mul_le_mul_right n (by have := j.isLt;omega)
    exact ⟨Nat.two_pow_pos _,by change 2^bits < 2^w;omega,by change base+j.val*n+2^bits ≤ base+2*n+2^bits;omega⟩
  obtain ⟨go,read,fixed⟩ := DescentTerminalSortRAM.run start bits
    (bank base n bits 0) (bank base n bits 1) (bank base n bits 2) origin mid low a fits room
    (bf 0) (bf 1) (bf 2) (fun i=>posted i 0) (fun i=>posted i 1) (fun i=>posted i 2)
  refine ⟨Procedure.Exec.then pre go,read,?_⟩
  intro x hx
  exact (fixed x (by dsimp [start,scratch];omega)).trans (columns_frame _ m (.inl hx))

end
end Hierarchy.DescentOldOccurrenceRAM

end OAI
