import OAI.Computability.BorderVNP.CellPacketChunk

/-! # Native reading of a three-word sparse cell descriptor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open VPVNP.BurstRAM CellPacketEncode

/-- The table opcode distinguishing natural-word and opaque-site ranges. -/
def Chunk.kind : Chunk → ℕ | .words .. => 0 | .box .. => 1

/-- Physical base of this range in the team memory. -/
def Chunk.base : Chunk → ℕ | .words a _ | .box a _ _ => a

/-- The public count field denotes words or length-header bits. -/
def Chunk.count : Chunk → ℕ | .words _ xs => xs.length | .box _ h _ => h

/-- The scalar descriptor's exclusive input end is within the declared total input extent. -/
theorem Chunk.count_end_le (c : Chunk) : c.base+c.count ≤ c.endSource := by
  cases c <;> simp [Chunk.base, Chunk.count, Chunk.endSource]

/-- The packet loop retains the stop register, external input range, scratch and burst bases,
and the fixed arithmetic constants. Register 2 is the advancing directory cursor. -/
def Persistent (a b : Reg → ℕ) : Prop :=
  ∀ i : Reg, (i.val ≤ 9 ∧ i ≠ 2) ∨ i = 18 → b i = a i

theorem Persistent.trans {a b c : Reg → ℕ} (f : Persistent a b) (g : Persistent b c) :
    Persistent a c := fun i hi => (g i hi).trans (f i hi)

/-- The integer zero, one and two are invariant under a persistent-register update. -/
theorem Persistent.constants {a b : Reg → ℕ} (h : Persistent a b) (hc : Constants a) : Constants b :=
  ⟨(h 0 (by decide)).trans hc.1, (h 1 (by decide)).trans hc.2.1, (h 18 (by decide)).trans hc.2.2⟩

/-- The word and bit emitters retain all persistent packet controls. -/
theorem persistent_of_fixed {a b : Reg → ℕ} (h : Fixed a b) : Persistent a b := by
  intro i hi
  have small : i.val ≤ 9 ∨ i = 18 := hi.imp And.left id
  apply h <;> intro he <;> subst i <;> norm_num at small

/-- Read kind, source and length from consecutive table cells. The source end in register
15 is computed from the count; for a private box this is the end of the length header. -/
def loadChunk : Code := .block [
  .load 10 2, .binary .add 2 2 1, .load 14 2, .binary .add 2 2 1,
  .load 15 2, .binary .add 2 2 1, .binary .add 15 14 15]

/-- Execute the descriptor reads with the actual initialized shared memory and preserve
the packet writer's destination cursor. -/
theorem loadChunk_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (c : Chunk) (a : ℕ) (hs : readings s 2 = a)
    (const : Constants (readings s)) (row : WordsAt (readings m) a c.descriptor)
    (hdesc : a+3 < 2^w) (hsrc : c.endSource < 2^w) :
    BoundedRun pub macros loadChunk s m 7 (fun z =>
      Persistent (readings s) z.reg ∧ z.reg 2 = a+3 ∧ z.reg 10 = c.kind ∧
      z.reg 14 = c.base ∧ z.reg 15 = c.base+c.count ∧ z.reg 20 = readings s 20 ∧ z.mem = readings m) := by
  have len : c.descriptor.length = 3 := by cases c <;> rfl
  have h0 : readings m a = c.kind := by
    have h := row ⟨0,by omega⟩
    cases c <;> exact h
  have h1 : readings m (a+1) = c.base := by
    have h := row ⟨1,by omega⟩
    cases c <;> exact h
  have h2 : readings m (a+2) = c.count := by
    have h := row ⟨2,by omega⟩
    cases c <;> exact h
  have hsum := c.count_end_le.trans_lt hsrc
  have hsafe : loadChunk.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [loadChunk, Code.block, Code.fixedSafe, Code.safeReadOnly,
      Code.fixedEval, Code.evalNat, addressOpFits, addressOp, NatState.ofWords,
      hs, const.2.1, h1, h2]
    omega
  apply (loadChunk.runFixed pub macros s m hsafe).mono (by decide)
  rintro z rfl
  constructor
  · intro i hi
    have n2 : i ≠ 2 := by rcases hi with h | rfl; exact h.2; decide
    have n10 : i ≠ 10 := by rcases hi with h | rfl; intro e; subst i; norm_num at h; decide
    have n14 : i ≠ 14 := by rcases hi with h | rfl; intro e; subst i; norm_num at h; decide
    have n15 : i ≠ 15 := by rcases hi with h | rfl; intro e; subst i; norm_num at h; decide
    simp [loadChunk, Code.block, Code.fixedEval, Code.evalNat, NatState.ofWords, n2, n10, n14, n15]
  · simp (config := {decide := true}) [loadChunk, Code.block, Code.fixedEval, Code.evalNat,
      addressOp, NatState.ofWords, hs, const.2.1, h0, h1, h2]

end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
