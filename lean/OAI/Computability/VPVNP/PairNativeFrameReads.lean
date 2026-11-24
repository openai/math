import OAI.Computability.VPVNP.PrimedInputRAMOnce
import OAI.Computability.VPVNP.RAMSuccessor
import Mathlib.Data.ZMod.Defs

/-! # Reading the terminal vertex's six descriptor words

The surrounding ordinal dispatch passes the address of the terminal header
in register zero and the role offset in register one. Only the six named
descriptor offsets cause external probes. The addresses are computed with
the two-bit literals available to the fixed pair program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeFrame
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

/-- Register indices for the 24-word work bank shared by the header reader and frame
arithmetic. -/
abbrev R := Fin 24
/-- Native instruction flows for the terminal frame, with 24 work registers and eleven public
operands. -/
abbrev Code := Flow 24 11

variable {w : ℕ}

/-- Header registers 3, 17, 4, 5, 6 and 8 receive the absolute row base,
row words, row stride, base radix, lane radix and auxiliary shadow span. -/
def destinations : Fin 6 → R := ![3,17,4,5,6,8]
/-- Header offsets for the absolute row base, row word count, row stride, base radix, lane
radix and shadow span, in read order. -/
def offsets : Fin 6 → ℕ := ![4,5,15,18,19,20]

private def advance (dst src : R) : ℕ → Code
  | 0 => .line (.copy dst src)
  | n+1 => .seq (advance dst src n) (.line (.binary .add dst dst 15))

private theorem advance_run (pub : Fin 11 → Word w) (st : Word w) (m : Memory w) (rs : Regs w 24)
    (dst src : R) (hd : dst ≠ 15) (one : rs 15 = 1) (n : ℕ) :
    Flow.Exec pub st (advance dst src n) rs m (List.replicate (n+1) .tick)
      (Function.update rs dst (rs src + (n : Word w))) m := by
  induction n with
  | zero => simpa [advance] using (show Flow.Exec pub st (.line (.copy dst src)) rs m [.tick]
        (Function.update rs dst (rs src)) m from .line rfl)
  | succ n ih =>
    let mid := Function.update rs dst (rs src+(n : Word w))
    have h : Flow.Exec pub st (.line (.binary .add dst dst 15)) mid m [.tick]
        (Function.update rs dst (rs src+((n+1 : ℕ) : Word w))) m := by
      apply Flow.Exec.line
      simp only [Op.effect,BinaryOp.eval,mid,Function.update_self,Function.update_of_ne hd.symm,
        Function.update_idem,one,Nat.cast_add,Nat.cast_one,add_assoc]
    simpa only [advance,List.replicate_succ',List.replicate_one] using ih.seq h

/-- Copy the header pointer from register zero, advance it by `off` unit steps, and load the
addressed external word into `dst`. -/
def readField (dst : R) (off : ℕ) : Code := .seq (advance dst 0 off) (.line (.read dst dst))

/-- Trace for reading one header field, with one pointer-copy tick, `off` increment ticks, and
a read carrying the value from memory. -/
def fieldEvents (header : Word w) (m : Memory w) (off : ℕ) : List (Event w) :=
  List.replicate (off+1) .tick ++ [.read (header+off) (m (header+off).val)]

private theorem read_run (pub : Fin 11 → Word w) (st : Word w) (m : Memory w) (rs : Regs w 24)
    (dst : R) (hd : dst ≠ 15) (one : rs 15 = 1) (off : ℕ) :
    Flow.Exec pub st (readField dst off) rs m (fieldEvents (rs 0) m off)
      (Function.update rs dst (m (rs 0+off).val)) m := by
  let mid := Function.update rs dst (rs 0+(off : Word w))
  have h : Flow.Exec pub st (.line (.read dst dst)) mid m
      [.read (rs 0+off) (m (rs 0+off).val)] (Function.update rs dst (m (rs 0+off).val)) m := by
    apply Flow.Exec.line; simp [Op.effect,mid,Function.update_idem]
  exact (advance_run pub st m rs dst 0 hd one off).seq h

/-- Initialize the unit register and load all six terminal descriptor words into their assigned
work registers. -/
def reads : Code :=
  .seq (.line (.constant 15 1)) (.seq (readField 3 4) (.seq (readField 17 5) (.seq (readField 4 15)
    (.seq (readField 5 18) (.seq (readField 6 19) (readField 8 20))))))

/-- Ordered event trace for the complete header reader, starting with the unit initialization
and ending with the shadow-span read. -/
def readEvents (header : Word w) (m : Memory w) :=
  .tick :: (fieldEvents header m 4 ++ (fieldEvents header m 5 ++ (fieldEvents header m 15 ++
    (fieldEvents header m 18 ++ (fieldEvents header m 19 ++ fieldEvents header m 20)))))

private def withField (header : Word w) (m : Memory w) (dst : R) (off : ℕ) (rs : Regs w 24) :=
  Function.update rs dst (m (header+off).val)

/-- Work bank after the header reader sets register 15 to one and installs the six external
field values in their destinations. -/
def loaded (header : Word w) (m : Memory w) (rs : Regs w 24) :=
  let set := withField header m
  set 8 20 (set 6 19 (set 5 18 (set 4 15 (set 17 5 (set 3 4 (Function.update rs 15 1))))))

theorem reads_run (pub : Fin 11 → Word w) (st : Word w) (m : Memory w) (rs : Regs w 24) :
    Flow.Exec pub st reads rs m (readEvents (rs 0) m) (loaded (rs 0) m rs) m := by
  let set := withField (rs 0) m
  let z := Function.update rs (15 : R) 1
  let a := set 3 4 z
  let b := set 17 5 a
  let c := set 4 15 b
  let d := set 5 18 c
  let e := set 6 19 d
  have load : Flow.Exec pub st (.line (.constant 15 1)) rs m [.tick] z m := .line rfl
  have read (u : Regs w 24) (dst : R) (off : ℕ) (hd : dst ≠ 15) (h : u 15 = 1) (hdr : u 0 = rs 0) :
      Flow.Exec pub st (readField dst off) u m (fieldEvents (rs 0) m off) (set dst off u) m := by
    simpa only [set,withField,hdr] using read_run pub st m u dst hd h off
  refine load.seq ((read z 3 4 (by decide) rfl rfl).seq ((read a 17 5 (by decide) rfl rfl).seq
    ((read b 4 15 (by decide) rfl rfl).seq ((read c 5 18 (by decide) rfl rfl).seq
    ((read d 6 19 (by decide) rfl rfl).seq (read e 8 20 (by decide) rfl rfl))))))

theorem reads_cost (header : Word w) (m : Memory w) :
    (readEvents header m).length = 94 ∧ countProbes (readEvents header m) = 6 ∧ choiceBits (readEvents header m) = [] := by
  exact ⟨rfl,rfl,rfl⟩

end PairSimulation.NativeFrame

end VPVNP
end Computability
end OAI
