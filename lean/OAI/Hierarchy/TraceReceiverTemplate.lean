import OAI.Hierarchy.TraceNativeScale
import OAI.ThreeFlat.Diagonal.TraceBitAddresses
import OAI.ThreeFlat.Diagonal.TracePortCardinality
import OAI.ThreeFlat.RAM.FixedTraceImage
import OAI.ThreeFlat.RAM.FixedTraceProgram
import OAI.ThreeFlat.RAM.HistoryCompiledRows

namespace OAI
/-! # The structural word vector for local reads of one verifier row -/

namespace Hierarchy.TraceReceiverTemplate

open ThreeFlat Diagonal RAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {W q : ℕ}

/-- The original eleven-word gate and port records, a canonical metadata ID per
local gate, and the eighteen public registers of the fixed address enumerator. -/
def count (G : BitNetwork F q) := FixedTraceImage.count G + G.cells + FixedTraceProgram.P

omit [Field F] [Fintype F] in
/-- Fitting the single received bank suffices for every absolute local
source, gate, port, and parameter address of the fixed enumerator. -/
theorem room (G : BitNetwork F q) (dst : ℕ) (fit : dst+count G < 2^W) (internal : G.internal ≤ G.cells) :
    dst+11*G.cells+11*q ≤ 2^W ∧ 2+q+G.internal < 2^W ∧ G.cells < 2^W ∧ 11 < 2^W ∧
    dst+FixedTraceImage.count G+G.cells+FixedTraceProgram.P ≤ 2^W := by
  simp only [count,FixedTraceImage.count,FixedTraceProgram.P] at fit ⊢
  omega

def registers (v : Fin 11 → Word W) : Fin FixedTraceProgram.P → Word W :=
  Fin.append (fun _ : Fin 2 => 0) (Fin.append (fun _ : Fin 5 => 0) v)

@[simp] theorem public_extra (v : Fin 11 → Word W) (i : Fin 11) :
    registers v (FixedTraceProgram.extra i) = v i := by simp [registers, FixedTraceProgram.extra]

noncomputable def scalar (G : BitNetwork F q) (code : FieldCode F W)
    (keys : Fin q → TraceAddressRecord.Record) (args : Fin 11 → Word W) (a : ℕ) : Word W :=
  if a < FixedTraceImage.count G then FixedTraceImage.word G code keys a
  else if h : a - FixedTraceImage.count G < G.cells then
    (((HistoryCompiledRows.library G).id ⟨a-FixedTraceImage.count G,h⟩).val : Word W)
  else if h : a - (FixedTraceImage.count G+G.cells) < FixedTraceProgram.P then
    registers args ⟨a-(FixedTraceImage.count G+G.cells),h⟩
  else 0

section Readouts
variable (G : BitNetwork F q) (code : FieldCode F W) (keys : Fin q → TraceAddressRecord.Record)
    (args : Fin 11 → Word W)

omit [Field F] in
theorem gate (i : Fin G.cells) (j : Fin 11) :
    scalar G code keys args (11*i.val+j.val) = BitLayout.record G code i j := by
  have h : 11*i.val+j.val < FixedTraceImage.count G := by
    unfold FixedTraceImage.count
    have := i.isLt
    have := j.isLt
    omega
  simpa [scalar,h] using FixedTraceImage.gate G code keys i j

omit [Field F] in
theorem port (i : Fin q) (j : Fin 11) :
    scalar G code keys args (11*G.cells+(11*i.val+j.val)) =
      (TraceAddressReader.fields (keys i) j : Word W) := by
  have h : 11*G.cells+(11*i.val+j.val) < FixedTraceImage.count G := by
    unfold FixedTraceImage.count
    have := i.isLt
    have := j.isLt
    omega
  simpa [scalar,h] using FixedTraceImage.port G code keys i j

omit [Field F] in
theorem label (i : Fin G.cells) : scalar G code keys args (FixedTraceImage.count G+i.val) =
    (((HistoryCompiledRows.library G).id i).val : Word W) := by
  simp [scalar,i.isLt]

omit [Field F] in
theorem arg (i : Fin 11) :
    scalar G code keys args (FixedTraceImage.count G+G.cells+(FixedTraceProgram.extra i).val) =
      args i := by
  have h : ¬ FixedTraceImage.count G+G.cells+(FixedTraceProgram.extra i).val <
      FixedTraceImage.count G := by omega
  have g : ¬ FixedTraceImage.count G+G.cells+(FixedTraceProgram.extra i).val -
      FixedTraceImage.count G < G.cells := by omega
  simp [scalar,h,g,(FixedTraceProgram.extra i).isLt]

end Readouts

variable {w pc regs slots S base d fuel : ℕ} (M : Machine (64*w) pc regs slots)
    (fit : NativeTrace.Fits M S base d fuel) (hF : Fintype.card F ≤ 2^(64*w)) (st : Word (64*w))
set_option quotPrecheck false

local notation "G" => TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs slots d
local notation "keys" => TraceBitDescriptor.records (p:=pc) (r:=regs) (k:=slots) (d:=d)
  fit.width base S fuel

def coefficient : ℕ := 12*(10^26+400)*66^14+18

set_option maxHeartbeats 1000000 in
open TraceDistribution in
theorem count_bound (hc : Fintype.card F ≤ 64*w) (hp : pc ≤ 64*w) (hr : regs ≤ 64*w)
    (hs : slots ≤ 64*w) (hd : d ≤ 64*w) : count G ≤ coefficient*(w+1)^14 := by
  let X := 66*(w+1)
  have smaller : 64*w+2 ≤ X := by dsimp [X]; omega
  have grow : X^3 ≤ X^14 := Nat.pow_le_pow_right (by dsimp [X]; positivity) (by decide)
  have shrink : 64*w+1≤X := by dsimp [X]; omega
  have g : (G).cells ≤ 10^26*X^14 := (native_cells M fit hF st hc hp hr hs hd).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left shrink _))
  have a : Fintype.card (TraceStaticRow.Port (64*w) pc regs slots d) ≤ 400*X^14 := by
    rw [TraceStaticRow.card_ports]
    apply (TraceStaticRow.portCount_of_le le_rfl hp hr hs hd).trans
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left smaller _).trans grow)
  have one : 1 ≤ (w+1)^14 := one_le_pow₀ (by omega)
  have total : count G ≤ 12*(10^26+400)*X^14+18 := by
    unfold count FixedTraceImage.count
    dsimp only [FixedTraceProgram.P]
    omega
  apply total.trans
  dsimp only [X,coefficient]
  rw [mul_pow]
  nlinarith

theorem packing_work_of_count {w C n : ℕ} (bound : n≤C*(w+1)^14) :
    n*(5*(64*w)+6)+6≤(326*C+6)*(w+1)^15 := by
  have one : 1≤(w+1)^15 := one_le_pow₀ (by omega)
  calc
    _ ≤ (C*(w+1)^14)*(326*(w+1))+6 := by exact Nat.add_le_add_right (Nat.mul_le_mul bound (by omega)) _
    _ = (326*C)*(w+1)^15+6 := by ring
    _ ≤ _ := by rw [Nat.add_mul]; omega

/-- Reading the immutable verifier template from actual bits uses a polynomial
number of RAM ticks at every permitted physical architecture. -/
theorem work_bound (hc : Fintype.card F≤64*w) (hp : pc≤64*w) (hr : regs≤64*w)
    (hs : slots≤64*w) (hd : d≤64*w) :
    count G*(5*(64*w)+6)+6≤(326*coefficient+6)*(w+1)^15 :=
  packing_work_of_count (count_bound M fit hF st hc hp hr hs hd)

noncomputable def words (code : FieldCode F (64*w)) (raw gateBase : ℕ) :
    Fin (count G) → Word (64*w) :=
  fun i => scalar G code keys (FixedTraceProgram.publicWords G code S
    (TraceUniformRow.SharedCount (64*w) pc regs slots d fuel) raw gateBase
    (gateBase+11*(G).cells)) i.val


end Hierarchy.TraceReceiverTemplate

end OAI
