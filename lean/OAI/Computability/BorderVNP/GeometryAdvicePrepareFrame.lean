import OAI.Computability.BorderVNP.DiagonalResidueRAMStage

/-! # Physical operands for unpacking a team's geometry circuit

Four public directory words specify the delivered bit array, the packed array,
its full length (including the output-reference directory), and the physical word
width. The packet uses the same six-word circuit header as the residue reader.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryAdvicePrepare

open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM VPVNP.BooleanTranscript RoutingISA
open DiagonalResidueRAM

variable {w u k : ℕ}

/-- Geometry advice directory fields for dense bits, packed words, word count and width. -/
def frame98 (pub : Arg → Word w) (m : Memory w) (dense start count : ℕ) : Prop :=
  let b := (pub 0).val
  m (b+98) = word w dense ∧ m (b+99) = word w start ∧
    m (b+100) = word w count ∧ m (b+101) = word w w

private def registers : Code := .block [
  readField 50 98, readField 53 99, readField 51 100, readField 52 101,
  .copy 48 53, .constant 63 1]

/-- Load the four geometry-frame operands and retain the header pointer. -/
def beginPack : Code := .seq (.publicWord 47 0) registers

/-- Fixed instruction sequence unpacking the entire payload and gathering the query. -/
def prepare : Code := .seq beginPack (.seq DiagonalTallyBits.pack (.seq loadHeader gather))

/-- Evaluate the packed Boolean gate table after its physical operands are ready. -/
def stage : Code := .seq prepare evaluate

/-- Instruction count through header loading and query gathering. -/
def prepareTicks (u count w : ℕ) : ℕ := 15 + DiagonalTallyBits.ticks count w + 12 + 11 + 7*u + 1

/-- Instruction count through the last shared gate and the validity load. -/
def stageTicks (u k count w : ℕ) : ℕ := prepareTicks u count w + (14*k+11)

/-- Memory layout for the whole packet and the gate valuation, including each query source. -/
structure Layout (base start dense : ℕ) (src : Fin u → ℕ) (k w count : ℕ) : Prop where
  /-- The gate valuation ends before the packed advice starts. -/
  valuation : gateBase base u 0 + k ≤ start
  /-- One past the packed advice fits in an address word. -/
  packed : start+count < 2^w
  /-- One past the source stream fits in an address word. -/
  denseFit : dense+count*w < 2^w
  /-- Packed stores preserve every unread advice bit. -/
  denseSeparate : dense+count*w ≤ start ∨ start+count ≤ dense
  /-- The public query addresses fit. -/
  sourceFit : ∀ i, src i < 2^w
  /-- Gathering query bits preserves the remaining query sources. -/
  sourceQuery : ∀ i, src i < base ∨ base+2+u ≤ src i
  /-- Unpacking the packet preserves all query sources. -/
  sourcePacked : ∀ i, src i < start ∨ start+count ≤ src i

/-- Reading the geometry directory sets all pack operands, without modifying memory. -/
theorem beginPack_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (dense start count : ℕ) (h : frame98 pub m dense start count)
    (hb : (pub 0).val+101 < 2^w) :
    ∃ z, Exact pub mac beginPack s m [] 15 z m ∧ z 50 = word w dense ∧ z 53 = word w start ∧
      z 51 = word w count ∧ z 52 = word w w ∧ z 63 = 1 ∧ z 48 = word w start := by
  let t := Function.update s (47 : Reg) (pub 0)
  let e := effect false t m registers
  have rd : Exact pub mac (.publicWord 47 0) s m [] 1 t m :=
    ⟨[tick w], Runs.localStep _ rfl rfl, by simp [TraceOK,tick]⟩
  have tr : TraceOK e.trace [] 14 := by simp [e,registers,readField,Code.block,effect,TraceOK,tick]
  have rs : Exact pub mac registers t m [] 14 e.bank m :=
    ⟨_,effect_runs pub mac false t m registers (by decide),tr⟩
  refine ⟨e.bank,rd.seq rs,?_⟩
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  have val (n : ℕ) (hn : n ≤ 101) : ((pub 0) + word w n).val = (pub 0).val+n := by
    change ((pub 0).val + (word w n).val) % 2^w = _
    rw [word_val w n (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [e,registers,readField,Code.block,effect]
  simp [BinaryOp.eval,t,Function.update]
  change m ((pub 0)+word w 98).val = _ ∧ m ((pub 0)+word w 99).val = _ ∧
    m ((pub 0)+word w 100).val = _ ∧ m ((pub 0)+word w 101).val = _ ∧ _ ∧ _
  rw [val 98 (by decide),val 99 (by decide),val 100 (by decide),val 101 (by decide)]
  refine ⟨h₀,h₁,h₂,h₃,rfl,?_⟩
  change m ((pub 0)+word w 99).val = _
  rw [val 99 (by decide)]
  exact h₁

end GeometryAdvicePrepare

end BorderVNP
end Computability
end OAI
