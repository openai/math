import OAI.Computability.VPVNP.LiveProgramCompressedPairPaths

/-!
# Compressed path occurrences and the native exponent-stage handoff

The ordinary completion of the pair table is followed by one outer tag
write. The header interval and all dense counter addresses lie beyond the
tag. The output of the simulator can therefore be read at its actual
word addresses by the subsequent exponent check.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.CompressedPaths

open BurstRAM BurstRAM.PrivateRAM LiveStageLink LiveExponent PairSimulation.LocalHistory

variable {G : Group} {m : Memory G.w} {i : Fin (2^(Auxiliary.sizes G).h)}
    {hdr : PrimedInputRAM.Header (Auxiliary.pairLengths G i) → Bool}
    {N : Indexed G Stage.nominations m (Nominations.Nom G)} {μ : Nominations.Nom G}
    (B : Auxiliary.PreparedBranch G m i hdr N μ)

/-- Facts measured on the actual native pair table and its real prepared
input. The path correspondence covers both directions of accepting tapes.
It records the selected descriptor and site streams via `SelectorReindex`.
The output and bounds below concern its unrelocated reports. -/
structure Execution (G : Group) (input : Memory G.w) (X : Type) (inc : X → Fin (labelCount G) → ℕ) (S H : ℕ) where
  /-- The trace encoding that records the selector and traversal choices of each mathematical
  occurrence. -/
  encoding : TraceEncoding X
  /-- The reindexing that emits and decodes the encoded selector choices for the physical
  execution. -/
  emission : SelectorReindex encoding
  /-- The equivalence between emitted selector traces and accepted native pair paths on the
  prepared input memory. -/
  paths : Set.range emission.emit ≃ Raw G input
  tag : PreservesTag G input
  work : ∀ p : Set.range emission.emit, ∀ r ∈ reports (paths p), r.events.length+4 ≤ fuel G
  header : ∀ p : Set.range emission.emit, ∀ a, Auxiliary.headerBase G ≤ a → a < Auxiliary.tableBase G →
    after input (eventLog (reports (paths p))) a = input a
  counters : ∀ p : Set.range emission.emit, ∀ a : Fin (labelCount G),
    (after input (eventLog (reports (paths p))) (Auxiliary.counterBase G+a)).val = inc (emission.decode p) a
  total : ∀ p : Set.range emission.emit, 4*RAMBuckets.cost Report.probes (reports (paths p)) ≤ S*H
  calls : ∀ p : Set.range emission.emit, ∀ r ∈ reports (paths p), 3+r.probes ≤ H

variable {X : Type} {inc : X → Fin (labelCount G) → ℕ} {S H : ℕ}
    (E : Execution G (B.copy.memory ()) X inc S H)

include E in
private theorem enough (p : Raw G (B.copy.memory ())) : ∀ r ∈ reports p, room G.nextStage G.addr Stage.pair (fuel G) r := by
  obtain ⟨p,rfl⟩ := E.paths.surjective p
  exact fun r hr => room_of_work (E.work p r hr)

/-- Each physical array read by the exponent stage names the corresponding
dense counter cell in the native simulator's final memory. -/
theorem counter_address (G : Group) (fit : Auxiliary.shadowBase G < 2^G.w) (a : Fin (labelCount G)) :
    (counterAddr G.exponentPub a).val = Auxiliary.counterBase G+a := by
  have base := (Auxiliary.address_values G fit).2.2.1
  change (G.exponentPub 2).val = Auxiliary.counterBase G at base
  have h := Auxiliary.counter_end_le_shadow G
  rw [counterAddr_val _ _ (by rw [base]; exact h.trans fit.le),base]

/-- Construct the single compressed component of the first-half chronology
from its native execution, preserving the accepting tape and all counters. -/
noncomputable def Execution.pairCall (fit : Auxiliary.shadowBase G < 2^G.w) : PairCall B X inc where
  indexed := indexed E.emission E.paths (B.copy.tagged_memory rfl ()) E.tag (enough B E)
  header q a lo hi := by
    obtain ⟨p,rfl⟩ := E.emission.decode.surjective q
    rw [indexed_memory]
    have htag := (Auxiliary.address_values G fit).1
    have horder := (Auxiliary.geometry_order G).1
    change (if a = G.addr.val then _ else _) = _
    rw [ite_eq_right (by omega)]
    exact E.header p a lo hi
  count q a := by
    obtain ⟨p,rfl⟩ := E.emission.decode.surjective q
    rw [indexed_memory,counter_address G fit a]
    have htag := (Auxiliary.address_values G fit).1
    obtain ⟨h₀,h₁,h₂,_⟩ := Auxiliary.geometry_order G
    change ((if Auxiliary.counterBase G+a.val = G.addr.val then _ else _ : Word G.w)).val = _
    rw [ite_eq_right (by omega)]
    exact E.counters p a

theorem Execution.pairCall_budget (fit : Auxiliary.shadowBase G < 2^G.w) (hH : 4 ≤ H) (q : X) :
    let rs := (E.pairCall B fit).indexed.logs q
    RAMBuckets.cost Report.probes rs ≤ S*(H-1) ∧ ∀ r ∈ rs, 1+r.probes ≤ H := by
  obtain ⟨p,rfl⟩ := E.emission.decode.surjective q
  exact indexed_budget E.emission E.paths (B.copy.tagged_memory rfl ()) E.tag (enough B E) p S H hH (E.total p) (E.calls p)

end LiveProgram.PairStages.Group.CompressedPaths

namespace LiveProgram.LocalCount

open BurstRAM LiveHeaderProgram LiveHeader PairStages PairStages.Group ChainAssignments CutSchedule ExponentTrace
open scoped Classical

variable {G : Group} {S H : ℕ} {Nom : Type}
    {Path : Exterior (profile G).h (profile G).delta → Fin (2^(profile G).h) → Nom → Type}

theorem compressedCalls_of_execution (W : Conditions G S H) (P : PairStageConditions G S H)
    (order : Nominations.Nom G ≃ Nom) (adv : Bits (profile G).advice)
    (fit : 1+labelCount G*expWidth G ≤ (profile G).delta) (inc : ∀ ξ i μ, Path ξ i μ → Fin (labelCount G) → ℕ)
    (native : ∀ (cuts : AllCuts (profile G).h (profile G).delta) (i : Fin (2^(profile G).h)),
      let j := halves (profile G).h (.inl i)
      physicalTag cuts j = some .pair → (∀ side, Fields.ValidPadding (profile G) cuts j .pair side) →
      ∀ tr : Prepared W adv cuts j .pair, Output (profile G) (Header.base G.g) G.g.d W.word adv cuts j .pair (memory tr) →
        let ξ := exteriorOf fit (fst cuts)
        let F := Auxiliary.nominationFits G i (P.room i) P.width.le P.nominations
        let N := Nominations.indexed G F (memory tr) tr.tag
        ∀ μ, ∀ B : Auxiliary.PreparedBranch G (memory tr) i (PairedChain.headers adv ξ i) N μ,
          Nonempty (CompressedPaths.Execution G (B.copy.memory ()) (Path ξ i (order μ)) (inc ξ i (order μ)) S H)) :
    CompressedCalls W P order adv fit inc := by
  intro cuts i j mode pad tr out ξ F N μ B
  obtain ⟨E⟩ := native cuts i mode pad tr out μ B
  have spanPos : 0 < LiveAuxiliaryHeaders.span (Auxiliary.pairLengths G i) (Auxiliary.histLength G) := by
    simp [LiveAuxiliaryHeaders.span,PrimedInputRAM.Header.count]
  have below : Auxiliary.shadowBase G < 2^G.w := by have := P.room i; omega
  exact ⟨E.pairCall B below, E.pairCall_budget B below ((by decide : 4 ≤ 26).trans P.bucket)⟩

end LiveProgram.LocalCount

end VPVNP
end Computability
end OAI
