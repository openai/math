import OAI.Computability.VPVNP.RAMProgram

namespace OAI
/-! # The two memory banks of a local RAM trace

External and private registers use separate banks of the same address-sorted
probe trace. A private RAM address occupies the second half of a widened word.
-/

namespace ThreeFlat.Diagonal.TraceBanks

open Computability.VPVNP.BurstRAM
open Computability.VPVNP.BurstRAM.PrivateRAM

variable {w p r : ℕ}

/-- Extend a word with a zero high bit. This is also its external-bank address. -/
def wide (x : Word w) : Word (w + 1) :=
  ⟨x.val, by rw [Nat.pow_succ]; have := x.isLt; omega⟩

/-- Drop the extra high bit from a word used in the two-bank execution. -/
def narrow (x : Word (w + 1)) : Word w := Fin.ofNat _ x.val

@[simp] theorem narrow_wide (x : Word w) : narrow (wide x) = x := by
  apply Fin.ext
  simp [narrow, wide]

/-- Add a high address bit to identify a private-memory access. -/
def privateAddress (x : Word w) : Word (w + 1) :=
  ⟨2 ^ w + x.val, by rw [Nat.pow_succ]; have := x.isLt; omega⟩

/-- One combined physical memory agrees on every usable address of the
native external memory and the native private memory. -/
structure Matches (bank : Memory (w + 1)) (ext : Memory w)
    (prv : Word w → Word w) : Prop where
  external : ∀ a : Word w, bank a.val = wide (ext a.val)
  privateWord : ∀ a : Word w, bank (privateAddress a).val = wide (prv a)

/-- Initially the external addresses hold exactly the input and the private
half starts with zeros. -/
def inputBank (ext : Memory w) : Memory (w + 1) :=
  fun j => if j < 2 ^ w then wide (ext j) else wide 0

theorem matches_inputBank (ext : Memory w) : Matches (inputBank ext) ext (fun _ => 0) where
  external a := by simp [inputBank, a.isLt]
  privateWord a := by
    have h : ¬2 ^ w + a.val < 2 ^ w := by omega
    simp [inputBank, privateAddress, h]

theorem Matches.write_external {bank : Memory (w+1)} {ext : Memory w} {prv : Word w → Word w}
    (m : Matches bank ext prv) (a v : Word w) :
    Matches (writeMemory bank (wide a) (wide v)) (writeMemory ext a v) prv where
  external b := by
    by_cases h : b.val = a.val <;> simp [writeMemory, wide, h, m.external]
  privateWord b := by
    have h : (privateAddress b).val ≠ a.val := by
      have := a.isLt
      simp only [privateAddress]
      omega
    simp [writeMemory, wide, h, m.privateWord]

theorem Matches.write_private {bank : Memory (w+1)} {ext : Memory w} {prv : Word w → Word w}
    (m : Matches bank ext prv) (a v : Word w) :
    Matches (writeMemory bank (privateAddress a) (wide v)) ext (Function.update prv a v) where
  external b := by
    have h : b.val ≠ (privateAddress a).val := by
      have := b.isLt
      simp only [privateAddress]
      omega
    simp [writeMemory, h, m.external]
  privateWord b := by
    by_cases h : b = a
    · subst b
      simp [writeMemory]
    · have h' : (privateAddress b).val ≠ (privateAddress a).val := fun eq =>
        h (Fin.ext (Nat.add_left_cancel eq))
      simp [writeMemory, h', Function.update_of_ne h, m.privateWord]

/-- Project combined probe records to the trace kept by the original RAM.
Private reads and writes were local ticks in that trace. -/
def nativeEvent : Event (w+1) → Event w
  | .tick => .tick
  | .choice b => .choice b
  | .read a v => if a.val < 2 ^ w then .read (narrow a) (narrow v) else .tick
  | .write a v => if a.val < 2 ^ w then .write (narrow a) (narrow v) else .tick

@[simp] theorem nativeEvent_read_external (a v : Word w) :
    nativeEvent (.read (wide a) (wide v)) = .read a v := by simp [nativeEvent, wide, narrow, a.isLt]

@[simp] theorem nativeEvent_write_external (a v : Word w) :
    nativeEvent (.write (wide a) (wide v)) = .write a v := by simp [nativeEvent, wide, narrow, a.isLt]

@[simp] theorem nativeEvent_read_private (a v : Word w) :
    nativeEvent (.read (privateAddress a) (wide v)) = .tick := by simp [nativeEvent, privateAddress]

@[simp] theorem nativeEvent_write_private (a v : Word w) :
    nativeEvent (.write (privateAddress a) (wide v)) = .tick := by simp [nativeEvent, privateAddress]

def nativeReport (s : Report (w+1)) : Report w :=
  ⟨s.events.map nativeEvent, s.result.map narrow⟩

theorem nativeReport_prepend (es : Option (Report (w+1))) (e : Event (w+1)) :
    (es.map (Report.prepend e)).map nativeReport =
      (es.map nativeReport).map (Report.prepend (nativeEvent e)) := by
  cases es <;> rfl

end ThreeFlat.Diagonal.TraceBanks

end OAI
