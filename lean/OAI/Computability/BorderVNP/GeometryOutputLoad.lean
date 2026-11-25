import OAI.Computability.BorderVNP.DiagonalResidueRAMStage

/-! # Load the output references of the geometry circuit

Five shared frame words locate the reference stream, temporary bit array,
packed result array, word count, and width. The first reference names the
validity bit. Remaining references are supplied in low-to-high bit order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryOutput

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM

/-- Shared output-frame operands, with the source pointer addressing the validity reference. -/
structure Layout where
  /-- Address of the validity reference followed by all word-bit references. -/
  refs : ℕ
  /-- Address of the temporary bit stream. -/
  temp : ℕ
  /-- First address of the result word array. -/
  dest : ℕ
  /-- Number of result words. -/
  count : ℕ
  /-- Number of significant bits in each result word. -/
  width : ℕ

/-- The five addresses and sizes are read from the public geometry frame. -/
def Layout.loaded {w : ℕ} (l : Layout) (pub : Arg → Word w) (m : Memory w) : Prop :=
  let b := (pub 0).val
  m (b+104) = word w l.refs ∧ m (b+105) = word w l.temp ∧
    m (b+106) = word w l.dest ∧ m (b+107) = word w l.count ∧ m (b+108) = word w l.width

/-- The gather loop's persistent registers also retain the operands for packing. -/
def Layout.gatherFrame (l : Layout) (valid : Bool) : Frame :=
  ⟨l.temp,l.count,l.width,l.dest,valid.toNat,l.count*l.width⟩

/-- Read the fields and dereference the validity wire, then advance past it. -/
def loadFields : Code := .block [
  readField 42 104, readField 32 105, readField 35 106, readField 33 107, readField 34 108,
  .constant 38 1, .constant 39 0, .copy 40 32, .copy 41 39,
  .binary .mul 37 33 34, .load 43 42, .load 36 43, .binary .add 42 42 38]

/-- Find the shared frame and load the output-stage operands. -/
def loadOutput : Code := .seq (.publicWord 47 0) loadFields

variable {w : ℕ}

/-- Native effects of the header reads, including a constant, input, or gate
selected by the first reference. The initial bank may be arbitrary. -/
theorem loadOutput_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (a : ℕ) (valid : Bool)
    (h : l.loaded pub m) (hb : (pub 0).val+108 < 2^w)
    (hr : l.refs < 2^w) (ha : a < 2^w)
    (href : m l.refs = word w a) (hv : m a = wordBit w valid) :
    ∃ z, Exact pub mac loadOutput s m [] 24 z m ∧
      (l.gatherFrame valid).stable z ∧ z 40 = word w l.temp ∧ z 41 = 0 ∧
      z 42 = word w (l.refs+1) := by
  let t := Function.update s (47 : Reg) (pub 0)
  let e := effect false t m loadFields
  have first : Exact pub mac (.publicWord 47 0) s m [] 1 t m :=
    ⟨[tick w], Runs.localStep m rfl rfl, by simp [TraceOK,tick]⟩
  have rest : Exact pub mac loadFields t m [] 23 e.bank m :=
    ⟨_,effect_runs pub mac false t m loadFields (by decide),
      by simp [loadFields,readField,Code.block,effect,TraceOK,tick]⟩
  refine ⟨e.bank,first.seq rest,?_⟩
  obtain ⟨h₀,h₁,h₂,h₃,h₄⟩ := h
  have val (n : ℕ) (hn : n ≤ 108) : ((pub 0)+word w n).val = (pub 0).val+n := by
    change ((pub 0).val + (word w n).val) % 2^w = _
    rw [word_val _ _ (by omega),Nat.mod_eq_of_lt (by omega)]
  simp only [e,loadFields,readField,Code.block,effect,Frame.stable,Frame.loaded,Layout.gatherFrame]
  simp [BinaryOp.eval,t,Function.update]
  change ((m ((pub 0)+word w 105).val = word w l.temp ∧
    m ((pub 0)+word w 107).val = word w l.count ∧
    m ((pub 0)+word w 108).val = word w l.width ∧
    m ((pub 0)+word w 106).val = word w l.dest ∧
    m (m (m ((pub 0)+word w 104).val).val).val = word w valid.toNat ∧
    m ((pub 0)+word w 107).val * m ((pub 0)+word w 108).val = word w (l.count*l.width)) ∧ (1 : Word w) = 1) ∧
    m ((pub 0)+word w 105).val = word w l.temp ∧ m ((pub 0)+word w 104).val + 1 = word w l.refs+1
  rw [val 104 (by decide),val 105 (by decide),val 106 (by decide),val 107 (by decide),
    val 108 (by decide),h₀,h₁,h₂,h₃,h₄,word_val _ _ hr,href,word_val _ _ ha,hv,word_mul]
  simp [wordBit,word]

end GeometryOutput

end BorderVNP
end Computability
end OAI
