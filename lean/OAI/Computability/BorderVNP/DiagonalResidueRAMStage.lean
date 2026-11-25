import OAI.Computability.BorderVNP.DiagonalResidueRAMPayload

/-!
# Unpacking residue advice supplied as distributed literal bits

Frame fields 28, 19, 29 and 30 supply the dense input-bit base, packed
output base, number of words and physical word width. The first six
decoded words are loaded into registers 32–37 using individual probes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM VPVNP.BooleanTranscript RoutingISA

/-- Load a shared frame word through register 47, using 60 as address scratch. -/
def readField (dst : Reg) (f : Word 8) : Code := .block [
  .constant 60 f, .binary .add 60 47 60, .load dst 60]

/-- Complete register initialization for the existing ordinary bit-packing routine. -/
def packRegisters : Code := .block [
  readField 50 28, readField 53 19, readField 51 29, readField 52 30,
  .copy 48 53, .constant 63 1]

/-- Get the public frame address before reading any shared header word. -/
def beginPack : Code := .seq (.publicWord 47 0) packRegisters

/-- Load one decoded operand, retaining the pointer to the next operand. -/
def operand (r : Reg) : Code := .seq (.load r 48) (.binary .add 48 48 63)

/-- Read the six operands from the front of the packed literal data. -/
def loadHeader : Code := .block [operand 32, operand 33, operand 34, operand 35, operand 36, operand 37]

/-- Before entry evaluation the team runs only fixed finite operations. -/
def prepare : Code := .seq beginPack (.seq DiagonalTallyBits.pack (.seq loadHeader gather))

/-- The complete staged reader, including its residue query's final true-bit guard. -/
def stagedReader : Code := .seq prepare reader

variable {w u v k : ℕ}

/-- Physical memory frame operands for the packed, delivered bit payload. -/
def packFrame (pub : Arg → Word w) (m : Memory w) (dense start count : ℕ) : Prop :=
  let b := (pub 0).val
  m (b+28) = word w dense ∧ m (b+19) = word w start ∧
    m (b+29) = word w count ∧ m (b+30) = word w w

/-- Read the four actual physical frame words and preserve the packed base
for the next stage. This takes fifteen instructions on any starting bank. -/
theorem beginPack_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (dense start count : ℕ) (h : packFrame pub m dense start count)
    (hb : (pub 0).val+30 < 2^w) :
    ∃ z, Exact pub mac beginPack s m [] 15 z m ∧ z 50 = word w dense ∧ z 53 = word w start ∧
      z 51 = word w count ∧ z 52 = word w w ∧ z 63 = 1 ∧ z 48 = word w start := by
  let t := Function.update s (47 : Reg) (pub 0)
  let e := effect false t m packRegisters
  have hpub : Exact pub mac (.publicWord 47 0) s m [] 1 t m :=
    ⟨[tick w],Runs.localStep _ rfl rfl,by simp [TraceOK,tick]⟩
  have htrace : TraceOK e.trace [] 14 := by simp [e,packRegisters,readField,Code.block,effect,TraceOK,tick]
  have hrest : Exact pub mac packRegisters t m [] 14 e.bank m :=
    ⟨_,effect_runs pub mac false t m packRegisters (by decide),htrace⟩
  refine ⟨e.bank,hpub.seq hrest,?_⟩
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  have val (n : ℕ) (hn : n ≤ 30) :
      ((pub 0) + word w n).val = (pub 0).val + n := by
    have hv := word_val w n (by omega)
    change ((pub 0).val + (word w n).val) % 2^w = _
    rw [hv,Nat.mod_eq_of_lt (by omega)]
  simp only [e,packRegisters,readField,Code.block,effect]
  simp [BinaryOp.eval, t, Function.update]
  change m ((pub 0)+word w 28).val = _ ∧ m ((pub 0)+word w 19).val = _ ∧
    m ((pub 0)+word w 29).val = _ ∧ m ((pub 0)+word w 30).val = _ ∧ _ ∧ _
  rw [val 28 (by decide),val 19 (by decide),val 29 (by decide),val 30 (by decide)]
  refine ⟨h₀,h₁,h₂,h₃,rfl,?_⟩
  change m ((pub 0)+word w 19).val = _
  rw [val 19 (by decide)]; exact h₁

/-- Directly reading the six known header words yields precisely the register
frame accepted by the generic native entry evaluator. -/
theorem loadHeader_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (start : ℕ) (d : Frame)
    (hp : s 48 = word w start) (hone : s 63 = 1) (hf : start+5 < 2^w)
    (h : Words m start (headerWords w d)) :
    ∃ z, Exact pub mac loadHeader s m [] 12 z m ∧ d.loaded z := by
  let e := effect false s m loadHeader
  refine ⟨e.bank,⟨e.trace,effect_runs pub mac false s m loadHeader (by decide),?_⟩,?_⟩
  · simp [e,loadHeader,operand,Code.block,effect,TraceOK,tick]
  · have atField (n : ℕ) (hn : n<6) := h ⟨n,hn⟩
    have step (a : ℕ) : word w a+1 = word w (a+1) := (word_add w a 1).symm
    simp only [Frame.loaded,e,loadHeader,operand,Code.block,effect]
    simp [BinaryOp.eval, Function.update, hp,hone,step,-word_add,Nat.add_assoc]
    simp only [word_val w start (by omega),word_val w (start+1) (by omega),
      word_val w (start+2) (by omega),word_val w (start+3) (by omega),
      word_val w (start+4) (by omega),word_val w (start+5) hf]
    exact ⟨atField 0 (by decide),atField 1 (by decide),atField 2 (by decide),
      atField 3 (by decide),atField 4 (by decide),atField 5 (by decide)⟩

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
