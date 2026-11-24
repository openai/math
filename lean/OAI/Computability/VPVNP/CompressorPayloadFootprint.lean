import OAI.Computability.VPVNP.CompressorPayloadCall
import OAI.Computability.VPVNP.CompressorFlowFootprint

/-!
# Probe addresses of the admitted motif payload call

The only external read obtains the repetition count from the preceding header
word. All writes fall in the reserved supply-coordinate array. These address
bounds apply to every admitted execution and every initial register bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PayloadFootprint

open BurstRAM PrimedInputRAM PrimedStackRAM MotifChoiceRAM SourceTransport
open FlowFootprint
open private storeEvents from OAI.Computability.VPVNP.CompressorPayloadWrite
open private load_exec loadEvents from OAI.Computability.VPVNP.CompressorPayloadCall

variable {r k w n : ℕ}

private theorem scale_private (dst src : Fin r) (bits : List Bool) :
    privateOnly (scaleDigits (k := k) dst src bits) = true := by
  induction bits with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [scaleDigits,privateOnly,privateOp,ih]

theorem prepare_private (n factor den : ℕ) : privateOnly (prepareBounds n factor den) = true := by
  simp [prepareBounds,privateOnly,scaleFixed,scale_private,privateOp]

theorem choose_private (n : ℕ) : privateOnly (choosePayload n) = true := by
  have zero (is : List (Fin n)) : privateOnly (unitSlots is) = true := by
    induction is with
    | nil => rfl
    | cons i is ih => simp [unitSlots,privateOnly,privateOp,ih]
  have scan (is : List (Fin n)) : privateOnly (MotifChoiceRAM.scan is) = true := by
    induction is with
    | nil => rfl
    | cons i is ih => exact Bool.and_eq_true_iff.mpr ⟨rfl,ih⟩
  exact Bool.and_eq_true_iff.mpr ⟨zero _,scan _⟩

private theorem append {readable writable : ℕ → Prop} {es fs : List (Event w)}
    (first : Reads readable es ∧ Writes writable es) (rest : Reads readable fs ∧ Writes writable fs) :
    Reads readable (es++fs) ∧ Writes writable (es++fs) :=
  ⟨fun a v h => (List.mem_append.mp h).elim (first.1 a v) (rest.1 a v),
   fun a v h => (List.mem_append.mp h).elim (first.2 a v) (rest.2 a v)⟩

private theorem store_bounds (base : ℕ) (vs : List (Word w)) (fit : base+vs.length ≤ 2^w) :
    Reads (fun _ => False) (storeEvents base vs) ∧
      Writes (fun i => base ≤ i ∧ i < base+vs.length) (storeEvents base vs) := by
  induction vs generalizing base with
  | nil => simp [storeEvents,Reads,Writes]
  | cons x xs ih =>
    simp only [List.length_cons] at fit
    obtain ⟨rd,wr⟩ := ih (base+1) (by omega)
    constructor <;> intro a v hv
    · apply rd a v
      simpa [storeEvents] using hv
    · simp only [storeEvents,List.mem_cons,Event.write.injEq,reduceCtorEq,false_or] at hv
      rcases hv with ⟨rfl,rfl⟩ | hv
      · simp [Fin.val_natCast,Nat.mod_eq_of_lt (show base < 2^w by omega)]
      · have h := wr a v hv
        simp only [List.length_cons]; omega

private theorem write_bounds (base : Word w) (v : Fin n → Word w) (fit : base.val+n ≤ 2^w) :
    Reads (fun i => i = (base-1).val) (PayloadWrite.writeEvents base v) ∧
    Writes (fun i => base.val ≤ i ∧ i < base.val+n) (PayloadWrite.writeEvents base v) := by
  obtain ⟨rd,wr⟩ := store_bounds base.val (List.ofFn v) (by simpa using fit)
  constructor <;> intro a x hv <;> simp only [PayloadWrite.writeEvents,List.mem_cons,reduceCtorEq,false_or] at hv
  · exact (rd a x hv).elim
  · simpa using wr a x hv

theorem storedCall (pub : Fin n → Word w) (base : Word w) {factor denominator : ℕ}
    {rs out : Regs w (6+n)} {m m' es} (fit : base.val+n ≤ 2^w)
    (run : Flow.Exec pub base (PayloadWrite.storedCall n factor denominator) rs m es out m') :
    Reads (fun i => i = (base-1).val) es ∧ Writes (fun i => base.val ≤ i ∧ i < base.val+n) es := by
  cases run with | seq start store =>
  cases start with | seq load prep =>
  cases store with | seq choice write =>
  obtain ⟨_,hl,_⟩ := load_exec pub base rs m
  have eqLoad := events_eq hl (by rfl) load
  obtain ⟨_,hs⟩ := PayloadWrite.writePayload_exec pub base _ _ _ (fun _ => rfl) fit
  have eqWrite := events_eq hs (PayloadWrite.writeEvents_spec _ _ m fit).2.2.1 write
  apply append (append ?_ (bounds_of_noProbes _ _ (noProbes (prepare_private ..) prep)))
    (append (bounds_of_noProbes _ _ (noProbes (choose_private _) choice)) ?_)
  · rw [← eqLoad]
    constructor <;> intro a v hv <;> simp [loadEvents] at hv
    exact congrArg Fin.val hv.1
  · rw [← eqWrite]
    exact write_bounds base _ fit

/-- Native form of the payload call's read and write bounds. -/
theorem execute (pub : Fin n → Word w) (base : Word w) (factor denominator : ℕ)
    (mem : Memory w) (fuel : ℕ) (bits : List Bool) (rep : Report w) (fit : base.val+n ≤ 2^w)
    (run : let machine := ((PayloadWrite.storedCall n factor denominator).template none).instantiate w pub
      BurstRAM.execute machine.program fuel (machine.program.start base) mem bits = some rep) :
    Reads (fun i => i = (base-1).val) rep.events ∧
      Writes (fun i => base.val ≤ i ∧ i < base.val+n) rep.events := by
  obtain ⟨_,_,he,_⟩ := (Flow.template_execute_iff (PayloadWrite.storedCall n factor denominator)
    none pub base (fun _ => 0) (fun _ => 0) mem fuel bits rep).mp run
  exact storedCall pub base fit he

end CompressorRecords.PayloadFootprint

end VPVNP
end Computability
end OAI
