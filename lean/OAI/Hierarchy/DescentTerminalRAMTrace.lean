import OAI.Hierarchy.DescentTerminalRAMDetector
import OAI.Hierarchy.DescentTerminalSortTrace
import OAI.Hierarchy.TaggedSortLiftFour

namespace OAI
/-! # Genuine chronological RAM histories checked by the lifted short sorts -/

namespace Hierarchy.DescentTerminalRAM
open ThreeFlat Routing SortNetwork Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open Tagged Tagged.SortLift TerminalSort DescentTerminalHost.SortBank
open TaggedShorterChronology TaggedShorterHistoryOrder TaggedShorterControlHistory
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {w p r k f S u m n steps : ℕ}

private theorem map_stage {q : ℕ} {A K : Type*} [LinearOrder K] (stage : Stage q) (key : A→K)
    (x : Fin q→A) : key ∘ stage.eval key x=stage.eval id (key ∘ x) := by
  funext i
  obtain ⟨⟨b,j⟩,rfl⟩:=stage.output.surjective i
  simp [Function.comp_apply,Stage.eval_output]

private theorem map_run {q : ℕ} {A K : Type*} [LinearOrder K] (ss : List (Stage q))
    (key : A→K) (x : Fin q→A) : key ∘ run ss key x=run ss id (key ∘ x) := by
  induction ss generalizing x with
  | nil=>rfl
  | cons s ss ih=>
    change key ∘ run ss key (s.eval key x)=run ss id (s.eval id (key ∘ x))
    rw [ih,map_stage]

abbrev Rec (w : ℕ) := Fin (RecordWidth (w+1))→Bool
abbrev Frames (m w steps : ℕ) := Fin (steps+1)→Fin (2^m)→Rec w
abbrev TracePin (m w steps : ℕ) := Fin (steps+1)×Bus m w

def rowPins (i : Fin (steps+1)) : RowRead (2^m) (RecordWidth (w+1)) (TracePin m w steps) :=
  fun j a=>.inl (i,j,a)

def traceBits (r : Frames m w steps) (p : TracePin m w steps) := r p.1 p.2.1 p.2.2

variable (stages : Fin steps→Stage (2^m)) (small : ∀i b,(stages i).length b≤2^n)
    (sorts : Sorts (List.ofFn stages) (Fin (2^RecordWidth (w+1))))

def Pass (record : Frames m w steps) := Accepts id (traceRead (n:=n) stages id rowPins) (traceBits record)

include small in
theorem pass_steps (record : Frames m w steps) :
    Pass (n:=n) stages record ↔ ∀i,record i.succ=(stages i).eval (key id) (record i.castSucc) :=
  trace_iff stages id small rowPins (traceBits record)

include small sorts in
theorem memory_order (record : Frames m w steps) (ok : Pass (n:=n) stages record) :
    Function.uncurry (record (Fin.last steps))=sortedPins id (Function.uncurry (record 0)) := by
  have last:=last_of_steps stages (key id) record ((pass_steps stages small record).mp ok)
  have rel:=map_run (List.ofFn stages) (key (d:=RecordWidth (w+1)) id) (record 0)
  have ordered := rel.trans (sorts (key (d:=RecordWidth (w+1)) id ∘ record 0))
  rw [last]
  apply congrArg Function.uncurry
  funext j
  apply (addressEquiv (RecordWidth (w+1))).injective
  exact congrFun ordered j

variable (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u→Word (w+1))

include small sorts in
/-- The value is an indicator for the real native CPU and the forced
sequence of every intermediate array of every lifted local sort. -/
theorem checked_value (fits : S+(f+u)≤2^m) (header : ℕ→Word (w+1)) (raw : TaggedShorterClock.Pin w r f→Bool)
    (out : Fin u→Word (w+1)) (record : Frames m w steps) :
    TypedWiring.value (detector (F:=F) M hw hp st hs ht addr)
      (Sum.elim (controls header raw out) (Sum.elim (Function.uncurry (record 0))
        (Function.uncurry (record (Fin.last steps)))))*
      (if Pass (n:=n) stages record then 1 else 0)=
      if Valid M hw hp st S addr header raw out ∧
        Function.uncurry (record 0)=chrono hw hp hs ht addr header raw out ∧ Pass (n:=n) stages record then 1 else 0 := by
  by_cases ok : Pass (n:=n) stages record
  · have sorted:=memory_order stages small sorts record ok
    simpa [ok,sorted] using
      authentic (F:=F) M hw hp st hs ht addr fits header raw out
        (Function.uncurry (record 0)) (Function.uncurry (record (Fin.last steps)))
  · simp [ok]

include small in
/-- Starting from an authentic halting native run forces the raw CPU
pins, all output words, and every intermediate physical sort array. -/
theorem true_run (nativeAddr : Fin u→Word w) (base : ℕ→Word w) (memRoom : S≤2^w)
    (terminal : Config w p r) (out : Memory w) (result : Option (Word w)) {t : ℕ} (fuel : t<f)
    (exec : RAM.advance M.program t (M.program.start st) (initialMemory S base)=some (terminal,out))
    (halt : M.program.step terminal=.finish result) :
    ∃ raw0 : TaggedShorterClock.Pin w r f→Bool, ∃ record0 : Frames m w steps, ∀ raw obs record,
      (Valid M hw hp st S (wide ∘ nativeAddr) (wide ∘ base) raw obs ∧
        Function.uncurry (record 0)=chrono hw hp hs ht (wide ∘ nativeAddr) (wide ∘ base) raw obs ∧ Pass (n:=n) stages record) ↔
      raw=raw0 ∧ obs=(fun i=>wide (out (nativeAddr i).val)) ∧ record=record0 := by
  obtain ⟨raw0,runUnique⟩:=unique_native M hw hp st S f nativeAddr base memRoom terminal out result fuel exec halt
  let data:=fun i=>wide (out (nativeAddr i).val)
  let first:=chrono (m:=m) hw hp hs ht (wide ∘ nativeAddr) (wide ∘ base) raw0 data
  obtain ⟨record0,ok,only⟩:=exists_unique_trace stages (key id) (Function.curry first)
  refine ⟨raw0,record0,?_⟩
  intro raw obs record
  constructor
  · rintro ⟨valid,initialBits,accepted⟩
    obtain ⟨rfl,rfl⟩:=(runUnique raw obs).mp valid
    refine ⟨rfl,rfl,only record ⟨?_,(pass_steps stages small record).mp accepted⟩⟩
    exact congrArg Function.curry initialBits
  · rintro ⟨rfl,rfl,rfl⟩
    refine ⟨(runUnique _ _).mpr ⟨rfl,rfl⟩,?_,(pass_steps stages small _).mpr ok.2⟩
    exact congrArg Function.uncurry ok.1

include small sorts in
/-- Summing all words of the physical log multiplies any terminal
readout by exactly one copy of its true field coefficient. -/
theorem sum_native (nativeAddr : Fin u→Word w) (base : ℕ→Word w) (memRoom : S≤2^w)
    (fits : S+(f+u)≤2^m) (terminal : Config w p r) (out : Memory w)
    (result : Option (Word w)) {t : ℕ} (fuel : t<f)
    (exec : RAM.advance M.program t (M.program.start st) (initialMemory S base)=some (terminal,out))
    (halt : M.program.step terminal=.finish result) (finish : (Fin u→Word (w+1))→F) :
    (∑raw : TaggedShorterClock.Pin w r f→Bool,∑obs : Fin u→Word (w+1),∑r : Frames m w steps,
      TypedWiring.value (detector (F:=F) M hw hp st hs ht (wide ∘ nativeAddr))
        (Sum.elim (controls (wide ∘ base) raw obs) (Sum.elim (Function.uncurry (r 0))
          (Function.uncurry (r (Fin.last steps)))))*
      (if Pass (n:=n) stages r then 1 else 0)*finish obs)=finish (fun i=>wide (out (nativeAddr i).val)) := by
  obtain ⟨raw0,r0,unique⟩:=true_run stages small M hw hp st hs ht nativeAddr base memRoom terminal out result fuel exec halt
  simp_rw [checked_value stages small sorts M hw hp st hs ht (wide ∘ nativeAddr) fits
    (wide ∘ base),unique]
  classical
  rw [Finset.sum_eq_single raw0]
  · rw [Finset.sum_eq_single (fun i=>wide (out (nativeAddr i).val))]
    · rw [Finset.sum_eq_single r0]
      · simp
      · intro r _ different
        simp [different]
      · simp
    · intro obs _ different
      simp [different]
    · simp
  · intro raw _ different
    simp [different]
  · simp

end
end Hierarchy.DescentTerminalRAM

end OAI
