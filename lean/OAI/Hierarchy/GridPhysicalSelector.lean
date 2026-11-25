import OAI.Hierarchy.GridPhysicalFactorBudget
import OAI.Hierarchy.PhysicalTraceRun
import OAI.Hierarchy.GridTraceCap
import OAI.Hierarchy.GridSelector
import OAI.Hierarchy.TraceDescriptorScan
import OAI.Hierarchy.TracePhysicalSiteCount
import OAI.Hierarchy.GridPhysicalSelectorOrder

namespace OAI
/-! # Canonical grid selectors for the concrete repeated RAM compressor -/

noncomputable section
namespace Hierarchy.GridPhysicalSelector

open ThreeFlat Diagonal Diagonal.PhysicalStage
open Filter TraceDistribution Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open scoped Classical BigOperators

variable {F : Type} [Field F] {d l : ℕ} {S : State d l}

abbrev Summand (r : Run F S) := (h : r.plan.History) × (r.plan.finish h).Boundary

/-- One table, selected independently of the pin values, specifies the prefix
of every physical history. The suffix is read in physical outgoing wire order. -/
structure Codec (r : Run F S) (K W : ℕ) (counts : List ℕ) (size : ℕ) where
  table : Program.RecordTable r K W counts
  positive : 0 < size
  room : GridSelector.Room r.plan table.codes (bits r) (size-1)

namespace Codec

variable {r : Run F S} {K W size : ℕ} {counts : List ℕ} (c : Codec r K W counts size)

/-- Move the body/head division into the actual public selector width. -/
def asFlagged : (Fin size → Bool) ≃ (Fin (size-1+1) → Bool) :=
  Equiv.arrowCongr (finCongr (by have := c.positive; omega)) (Equiv.refl _)

def Accepted := {x : Fin size → Bool //
  (GridSelector.decode r.plan c.table.codes (bits r) (size-1) (c.asFlagged x)).isSome}

/-- The unique identity word and all simulated words of the fixed grid are in
bijection with the actual terminal assignments used in the RAM trace scalar. -/
def validEquiv : c.Accepted ≃ Option (Summand r) :=
  ((Equiv.subtypeEquivOfSubtype c.asFlagged).trans (GridSelector.validEquiv r.plan
    c.table.codes (bits r) (size-1) c.room)).trans
    (Equiv.optionCongr (Equiv.sigmaCongrRight (fun h : r.plan.History => r.terminalLabels h)))

end Codec

/-- Reordering the product by the physical terminal site numbers gives the
same scalar as the actual installed verifier. -/
theorem native_value [Fintype F] (B : Block F) {k low : ℕ} (hk : 2≤k+1)
    {w pc regs words N base fuel : ℕ} (M : Machine w pc regs words)
    (fit : NativeTrace.Fits M N base ((k+1)+low) fuel) (hF : Fintype.card F≤2^w)
    (st : Word w) (s : ℕ) (passes : B.blockCharge*s≤k+1) (input : ℕ → Bool) :
    let r := Physical.nativeRun B hk M fit hF st s passes
    let L := layout M fit hF st
    let pins := TraceBitHeader.advicePins (S:=N) base (NativeTrace.executable M) input
    RAM.value (RAM.FieldCode.ofCardLe hF) M fuel st (RAM.memoryWithAdvice base
      (NativeTrace.executable M) (Computability.VPVNP.RAMMemory.initialMemory N (fun j => TraceBitHeader.binaryWord w (input j)))) =
      ∑ z : Summand r, ∏ i : Fin (Fintype.card (r.plan.finish z.1).Site),
        let v := (siteOrder r z.1).symm i
        r.plan.cells z.1 (Physical.seed B hk L pins) v ((r.plan.finish z.1).graph.atVertex z.2 v) := by
  intro r L pins
  rw [Physical.repeated_native B hk M fit hF st s passes input,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro b _
  exact ((siteOrder r h).symm.prod_comp (fun v => r.plan.cells h (Physical.seed B hk L pins) v
    ((r.plan.finish h).graph.atVertex b v))).symm

private theorem actual_bits {r : Run F S} (h : r.plan.History) {n : ℕ}
    (e : (r.plan.finish h).Boundary ≃ (Fin n → Bool)) : bits r h=n := by
  have hc := Fintype.card_congr ((r.terminalLabels h).trans e)
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hc
  simpa only [Nat.log2_two_pow] using congrArg Nat.log2 hc

/-- The outgoing-word numbering itself has the saving provided by the
physical energy estimate, uniformly for all branch-dependent terminal states. -/
theorem terminal_budget (B : Block F) :
    ∃ C : ℕ, ∀ {k w u low offsets slots s : ℕ} (hk : 2≤k+1)
      (_dim : k+1=u+1-low) (_room : low≤u+1) (_depth : u+1≤64*w)
      (_off : offsets=1+(u+1+(u+1))) (_cells : slots≤10^26*(64*w+1)^14)
      (passes : B.blockCharge*s≤k+1),
      let r := Physical.run B hk low offsets slots s passes
      ∀ h : r.plan.History, bits r h*2^s ≤ C*2^u*(w+1)^16 := by
  obtain ⟨C,save⟩ := Physical.terminal_bits_volume B
  refine ⟨C,?_⟩
  intro k w u low offsets slots s hk dim room depth off cells passes
  subst offsets
  intro r h
  obtain ⟨n,encoding,bound⟩ := save hk dim room depth cells passes h
  rw [actual_bits h encoding.some]
  exact bound

/-- At the actual grid parameters the physical table, its outgoing-word
suffix and its branch flag all fit. Processor capacities may grow with the age
up to the word length; in particular the padded tick capacities are admitted. -/
theorem native_codec [Fintype F] (B : Block F) {Q : ℕ → ℕ} {D : ℕ → ℝ}
    (env : GridScale.Envelopes Q D) (g A c : ℕ) (q : ℕ → ℕ)
    (range : ∀ᶠ w : ℕ in atTop, 0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop, let a := GridScale.overhead Q D w
      let u := GridScale.evalDepth w g A c a (q w)
      let s := GridScale.traceBlocks g a
      ∀ {pc regs words k : ℕ}, pc≤64*w → regs≤64*w → words≤64*w →
        ∀ (hk : 2≤k+1) (_axes : k+1=u+1-w/2) (M : Machine (64*w) pc regs words) {N base fuel : ℕ}
          (fit : NativeTrace.Fits M N base ((k+1)+w/2) fuel)
          (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (passes : B.blockCharge*s≤k+1),
          Nonempty (Codec (Physical.nativeRun B hk M fit hF st s passes) B.alphabetCap (64*w)
            (TraceAdmission.stageCounts B s (k+1)) (GridScale.selector g w a)) := by
  let u := fun w => GridScale.evalDepth w g A c (GridScale.overhead Q D w) (q w)
  let s := fun w => GridScale.traceBlocks g (GridScale.overhead Q D w)
  have scale : Scale u s := GridScale.trace_scale env g A c q range
  obtain ⟨C,terminal⟩ := terminal_budget B
  filter_upwards [TraceAdmission.native_history_codec B scale,
    native_fits (F:=F) scale 1 0 0 (by decide),GridScale.selector_room env g A c 16 C,
    eventually_ge_atTop (Fintype.card F+1),range] with w records bounds combine age runq
  intro a uw sw pc regs words k hp hr hk' hk axes M N base fuel fit hF st passes
  let r := Physical.nativeRun B hk M fit hF st sw passes
  obtain ⟨table,recordSpace⟩ := records hp hr hk' hk axes M fit hF st passes
  have low : w/2≤uw := bounds.2.2.1
  have high : uw≤2*w := bounds.2.2.2.1
  have sum : k+1+w/2=uw+1 := by omega
  have depth : uw+1≤64*w := by omega
  have cells := native_cells M fit hF st (by omega) hp hr hk' (by omega)
  refine ⟨⟨table,by dsimp [GridScale.selector]; positivity,?_⟩⟩
  intro h
  have wires := terminal hk axes (by omega) depth (by rw [sum]) cells passes h
  have room : 1+(r.plan.write table.codes h).length+bits r h ≤ GridScale.selector g w a :=
    combine _ runq.1 runq.2 _ _ (recordSpace h).1 wires
  apply Nat.le_sub_of_add_le
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using room


end Hierarchy.GridPhysicalSelector

end
end OAI
