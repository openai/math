import OAI.Hierarchy.TaggedWideControlGate
import OAI.Hierarchy.TaggedWideObservedBits

namespace OAI
/-! # Normalization of a physical control gate through native executions -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin.Gate
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory TaggedShorterControlHistory
open scoped Classical BigOperators
variable {F : Type*} [Field F] (G : Gate)

def observed (header : ℕ→Word G.W) (φ : (G.Seen→Bool)→F) : F :=
  observationSum (m:=G.m) 28 G.machine G.word G.labels G.start G.addr header G.headerBound G.clock
    (fun obs=>φ (observationBits G.u (G.W+1) obs))

theorem sum_hidden (header : ℕ→Word G.W) (φ : (G.Seen→Bool)→F) :
    (∑ y : G.Hidden→Bool, G.value (G.headBits header) y * G.sorts y * φ (y ∘ G.seenPin)) =
      G.observed header φ := by
  have eq (y : G.Hidden→Bool) : G.value (F:=F) (G.headBits header) y =
      TypedWiring.value (TaggedShorterControlHistory.network (F:=F) (m:=G.m) (a:=28)
        G.machine G.word G.labels G.start G.high G.clock (wide ∘ G.addr)) (G.input (G.headBits header) y) :=
    BitNetwork.compactHidden_eval _ _
  simp only [eq]
  exact bitWorkspace G.machine G.word G.labels G.start G.addr header G.headerBound G.clock φ

/-- Evidence required for a paid readout. This refers to the machine's native step and memory. -/
structure Ran (header : ℕ→Word G.W) (out : Memory G.W) : Prop where
  execution : ∃ t : ℕ, ∃ done : Config G.W G.p G.r, ∃ result : Option (Word G.W),
    t<G.f ∧ ThreeFlat.RAM.advance G.machine.program t
      (G.machine.program.start G.start) (initialMemory G.S header) = some (done,out) ∧
      G.machine.program.step done = .finish result

def terminal (out : Memory G.W) : G.Seen→Bool :=
  observationBits G.u (G.W+1) (fun j=>wide (out (G.addr j).val))

theorem observed_run (header : ℕ→Word G.W) (out : Memory G.W) (run : G.Ran header out)
    (slots : G.S+(G.f+G.u)≤2^G.m) (room : G.W+1≤4*G.m) (φ : (G.Seen→Bool)→F) :
    G.observed header φ = φ (G.terminal out) := by
  obtain ⟨t,done,result,fuel,ran,halt⟩ := run.execution
  exact observed_weight G.machine G.word G.labels G.start G.addr header G.headerBound G.clock
    slots (by decide : 0<28) (record_fits_width room) done out result fuel ran halt _

theorem zeroFlag_words (flag : Fin G.u) (obs : Fin G.u→Word (G.W+1)) :
    G.zeroFlag (F:=F) flag (observationBits G.u (G.W+1) obs) = if (obs flag).val=0 then 1 else 0 := by
  have iff : (∀ j : Fin (G.W+1), observationBits G.u (G.W+1) obs (flag,j)=false) ↔
      (obs flag).val = 0 := by
    change (∀ j, TraceWords.bits (obs flag) j=false) ↔ _
    constructor
    · intro bits
      have eq : obs flag = 0 := TraceWords.bits_injective (by funext j; simpa [TraceWords.bits] using bits j)
      simp [eq]
    · intro hv j
      simp [TraceWords.bits,hv]
  unfold zeroFlag
  by_cases zero : (obs flag).val=0
  · simp only [ite_eq_left zero,ite_eq_left (iff.mpr zero)]
  · simp only [ite_eq_right zero,ite_eq_right (fun all => zero (iff.mp all))]

end Hierarchy.Tagged.WideControlJoin.Gate

end
end OAI
