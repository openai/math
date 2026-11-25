import OAI.ThreeFlat.Diagonal.NativeTrace
import OAI.ThreeFlat.RAM.CapacityPadding
import Mathlib.Order.Filter.AtTopBot.Basic

namespace OAI
/-! # Reading the evaluator's own instruction bytes on the real input tape

The architecture is chosen before the approximation. One field of w² bits
contains two executable tables, the universally run tick program followed
by the accelerated evaluator. The evaluator's machine header is mounted
in place within that same bit field. External pairs and replacement data
are read from different, explicitly located portions of the tape. -/

namespace Hierarchy.GridDescription
open ThreeFlat
open Diagonal Diagonal.TraceBitHeader RAM RAM.SelfAdvice
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory
open Filter

def capacity (w : ℕ) := w/1024

/-- Each outer compiler column can occupy a separate interval of this width.
The control words and the actual low contraction image use the same 64w-bit RAM. -/
def sector (w : ℕ) : ℕ := 2^(32*w)

theorem sectors_fit {w : ℕ} (large : 1≤w) : 64*sector w < 2^(64*w) := by
  change 2^6*2^(32*w)<2^(64*w)
  rw [←pow_add]
  exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mpr (by omega)

theorem small_before_sector {w : ℕ} (wpos : 0<w) : 2^(4*w)<sector w :=
  (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mpr (by omega)


theorem eventually_fits (p r k : ℕ) : ∀ᶠ w : ℕ in atTop, p≤capacity w ∧ r≤capacity w ∧ k≤capacity w := by
  filter_upwards [eventually_ge_atTop (1024*(p+r+k))] with w hw
  unfold capacity
  omega

/-- Even when both programs fill the preselected architecture their
serialized instructions and operand words fit the original code field. -/
theorem room {w p k p' k' : ℕ} (age : 1024≤w)
    (p1 : p≤capacity w) (k1 : k≤capacity w) (p2 : p'≤capacity w) (k2 : k'≤capacity w) :
    SelfAdvice.Fits (64*w) p k p' k' 0 (w^2) := by
  have space := Nat.div_mul_le_self w 1024
  change p≤w/1024 at p1
  change k≤w/1024 at k1
  change p'≤w/1024 at p2
  change k'≤w/1024 at k2
  have control : (1+6*p+k+ (1+6*p'+k'))*64 ≤ w := by omega
  constructor
  unfold textSize
  simpa only [Nat.add_zero,pow_two,Nat.add_mul,Nat.mul_assoc] using Nat.mul_le_mul_right w control

/-- All machine dimensions can be chosen in advance and padded uniformly
in the age. Both external data and code are part of S. -/
theorem evaluatorFits {w u p r k S mount fuel : ℕ} (M : Machine (64*w) p r k)
    (large : 2≤w) (upper : u≤2*w) (hp : 0<p) (labels : p≤w) (regs : r≤w)
    (words : k≤w) (input : S≤2^u) (time : fuel≤2^u) (code : mount+(1+6*p+k)*(64*w)≤S) :
    NativeTrace.Fits M S mount (u+1) fuel := by
  have field : w ≤ 2^(64*w) := (show w≤64*w by omega).trans Nat.lt_two_pow_self.le
  have clock : 2^u ≤ 2^(64*w) := Nat.pow_le_pow_right (by decide) (by omega)
  have next : 2^(64*w)≤2^(64*w+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have text : 1+6*p+k≤2^(64*w) := (show 1+6*p+k≤64*w by omega).trans Nat.lt_two_pow_self.le
  refine ⟨by omega,(labels.trans field).trans next,hp,input.trans clock,(time.trans clock).trans next,
    ?_,⟨lt_of_lt_of_le (show 14<2^4 by decide) (Nat.pow_le_pow_right (by decide) (by omega)),regs.trans field,text⟩,code⟩
  rw [show 1+(u+1)=(u+1)+1 by omega,pow_succ,pow_succ]
  omega

variable {W p r k p' r' k' raw q : ℕ}
variable (tick : Machine W p r k) (evaluator : Machine W p' r' k')
def code : Fin q → Bool := SelfAdvice.description tick evaluator (Fin.elim0 : Fin 0 → Bool)

/-- A single tape, containing external pair endpoints, the common code and
all remaining fixed data in order. The tail may include arbitrarily many
replacement-network bits, while the code has the fixed length q. -/
def input (pair : Fin raw → Bool) (a : Fin q → Bool) (fixed : ℕ → Bool) (i : ℕ) : Bool :=
  if h : i<raw then pair ⟨i,h⟩ else if h : i-raw<q then a ⟨i-raw,h⟩ else fixed (i-raw-q)

theorem pair_at (pair : Fin raw → Bool) (a : Fin q → Bool) (fixed : ℕ → Bool) (i : Fin raw) :
    input pair a fixed i.val=pair i := by simp [input,i.isLt]
theorem code_at (pair : Fin raw → Bool) (a : Fin q → Bool) (fixed : ℕ → Bool) (i : Fin q) :
    input pair a fixed (raw+i.val)=a i := by simp [input,i.isLt]
theorem fixed_at (pair : Fin raw → Bool) (a : Fin q → Bool) (fixed : ℕ → Bool) (i : ℕ) :
    input pair a fixed (raw+q+i)=fixed i := by
  simp [input,show ¬raw+q+i<raw by omega,show raw+q+i-raw=q+i by omega]

/-- The very same bits that are readable as input form the operative
evaluator instruction table. Neither its output nor its trace is encoded. -/
theorem text_at (room : SelfAdvice.Fits W p k p' k' 0 q) (pair : Fin raw → Bool)
    (fixed : ℕ→Bool) (i : Fin (textSize W p' k')) :
    input pair (code (q:=q) tick evaluator) fixed (raw+textSize W p k+i.val) =
      NativeTrace.executable evaluator i := by
  have hi : textSize W p k+i.val<q := by have := i.isLt; have := room.room; omega
  rw [Nat.add_assoc,show textSize W p k+i.val = (⟨_,hi⟩ : Fin q).val from rfl,
    code_at,NativeTrace.executable_bits]
  exact SelfAdvice.h_bits tick evaluator _ room i

theorem tick_at (room : SelfAdvice.Fits W p k p' k' 0 q) (pair : Fin raw → Bool)
    (fixed : ℕ→Bool) (i : Fin (textSize W p k)) :
    input pair (code (q:=q) tick evaluator) fixed (raw+i.val) = NativeTrace.executable tick i := by
  have hi : i.val<q := by have := i.isLt; have := room.room; omega
  rw [show i.val=(⟨_,hi⟩ : Fin q).val from rfl,code_at,NativeTrace.executable_bits]
  exact SelfAdvice.tick_bits tick evaluator _ room i

/-- The native volume estimate can budget the full bit array at its last
possible mount. Installing an executable already present earlier in the
array preserves the same clock, grid depth and input length. -/
theorem at_lower_mount {S base mount d fuel : ℕ}
    (fit : NativeTrace.Fits evaluator S base d fuel) (earlier : mount≤base) :
    NativeTrace.Fits evaluator S mount d fuel :=
  ⟨fit.width,fit.labels,fit.positive,fit.header,fit.time,fit.grid,fit.text,
    (Nat.add_le_add_right earlier _).trans fit.mount⟩

/-- Genuine weighted execution on the unmodified initial tape, including
the structurally generated evaluator itself and a literal common code. -/
theorem native_trace {F : Type*} [Field F] [Fintype F] {S d fuel : ℕ}
    (room : SelfAdvice.Fits W p k p' k' 0 q) (hf : Fintype.card F≤2^W)
    (fit : NativeTrace.Fits evaluator S (raw+textSize W p k) d fuel) (st : Word W)
    (pair : Fin raw → Bool) (fixed : ℕ→Bool) :
    let tape := input pair (code (q:=q) tick evaluator) fixed
    (NativeTrace.network evaluator fit hf st).eval (fun i => tape i.val) =
      value (FieldCode.ofCardLe hf) evaluator fuel st (initialMemory S (fun j => binaryWord W (tape j))) := by
  intro tape
  let mount := raw+textSize W p k
  have eqAt (i : ℕ) (h : mount ≤ i ∧ i-mount<textSize W p' k') :
      NativeTrace.executable evaluator ⟨i-mount,h.2⟩ = tape i := by
    have atLocation := text_at tick evaluator room pair fixed ⟨i-mount,h.2⟩
    dsimp only [Fin.val_mk] at atLocation
    change tape (mount+(i-mount)) = _ at atLocation
    rw [Nat.add_sub_of_le h.1] at atLocation
    exact atLocation.symm
  have same : advicePins (S:=S) mount (NativeTrace.executable evaluator) tape = (fun i => tape i.val) := by
    funext i
    unfold advicePins
    split
    · exact eqAt _ (by assumption)
    · rfl
  have saved : memoryWithAdvice mount (NativeTrace.executable evaluator)
      (initialMemory S (fun j => binaryWord W (tape j))) =
      initialMemory S (fun j => binaryWord W (tape j)) := by
    funext i
    unfold memoryWithAdvice
    split
    next h =>
      have area : mount+(1+6*p'+k')*W≤S := fit.mount
      have inside : mount ≤ i ∧ i-mount<(1+6*p'+k')*W := h
      have live : i<S := by omega
      rw [initialMemory,ite_eq_left live,eqAt _ h]
      rfl
    next => rfl
  rw [←same,←saved]
  exact NativeTrace.installed evaluator fit hf st tape

end Hierarchy.GridDescription

end OAI
