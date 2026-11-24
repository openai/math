import OAI.Computability.VPVNP.LivePairStageConditions
import OAI.Computability.VPVNP.LiveOutsidePreparedPair
import OAI.Computability.VPVNP.LiveProgramPairNominationOrder
import OAI.Computability.VPVNP.LiveLocalGroupCount

/-!
# From a native compressed pair call to the physical first-half continuation

The prefix in the cap already contains the mode-router report. We add the
actual nomination, initialization, copy and exponent reports exactly once.
Reindexing the nomination sum puts the resulting local count in the order of
the formal productions. The remaining native call obligation concerns only
the compressed computation at its actual input and output addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.LocalCount

open BurstRAM BurstRAM.PrivateRAM LiveStageLink LiveExponent LiveHeaderProgram PairStages PairStages.Group
open ChainAssignments CutSchedule ExponentTrace LiveHeader
open scoped Classical

variable {G : Group} {S H : ℕ}

private theorem joinedCap {m : Memory G.w} {i : Fin (2^(profile G).h)}
    {hdr : PrimedInputRAM.Header (Auxiliary.pairLengths G i) → Bool} (fit : PairStageConditions G S H)
    (pre : List (Report G.w)) (preCost : RAMBuckets.cost Report.probes pre ≤ LiveHeaderSchedule.costBound (profile G)+4)
    (preCalls : ∀ r ∈ pre, r.probes ≤ 10) (tag : G.tagged Stage.nominations m)
    (μ : Nominations.Nom G) (F : Nominations.Fits G)
    (B : Auxiliary.PreparedBranch G m i hdr (Nominations.indexed G F m tag) μ)
    {X : Type*} (A : Indexed G Stage.pair (B.copy.memory ()) X) (q : X)
    (hcost : RAMBuckets.cost Report.probes (A.logs q) ≤ S*(H-1)) (hcalls : ∀ r ∈ A.logs q, 1+r.probes ≤ H) :
    withinCaps S H (pre ++ ((Nominations.indexed G F m tag).logs μ ++
      (B.init.logs () ++ (B.copy.logs () ++ A.logs q))) ++
      (stageReports G.exponentPub (labelCount G) (expWidth G) (A.memory q)).map
        (linkedReport G.nextStage G.addr Stage.exponents)) := by
  obtain ⟨nom,init,copy⟩ := OutsideBudget.prepared_resources G i F m tag μ B (fit.room i) (by have := fit.copy; omega)
  have exp := OutsideBudget.exponent_resources G (labelCount G) (expWidth G) (A.memory q)
  have rout := fit.cost
  have bucket := fit.bucket
  constructor
  · simp only [RAMBuckets.cost_append]
    have hc : LiveHeaderSchedule.costBound (profile G)+4 + (4*(labelCount G+1) +
        (100 + 16*(OutsideBudget.auxWords (profile G) (labelCount G)+1))) + 7*(labelCount G*expWidth G+1) ≤ S := by
      unfold OutsideBudget.actualBound at rout
      change LiveHeaderSchedule.costBound (profile G) + 8 + 4*(labelCount G+1) + 100 +
        16*(OutsideBudget.auxWords (profile G) (labelCount G)+1) + 7*(labelCount G*expWidth G+1) + _ ≤ S at rout
      omega
    have heq : S+S*(H-1) = S*H := by rw [Nat.add_comm S,← Nat.mul_succ,show (H-1).succ=H by omega]
    have hn := nom.cost
    have hi := init.cost
    have hp := copy.cost
    have he := exp.cost
    change _ ≤ 4*(labelCount G+1) at hn
    change _ ≤ 16*(OutsideBudget.auxWords (profile G) (labelCount G)+1) at hp
    rw [← heq]
    omega
  · intro r h
    simp only [List.mem_append] at h
    rcases h with h | h
    · rcases h with h | h
      · have := preCalls r h; omega
      · rcases h with h | h | h | h
        · exact (nom.calls r h).trans (by omega)
        · exact (init.calls r h).trans bucket
        · exact (copy.calls r h).trans (by omega)
        · exact hcalls r h
    · exact (exp.calls r h).trans (by omega)

variable {Nom : Type*} [Fintype Nom]
    {Path : Exterior (profile G).h (profile G).delta → Fin (2^(profile G).h) → Nom → Type*}
    [finitePaths : ∀ ξ i μ, Fintype (Path ξ i μ)]

/-- Reindex the exact count of local paths by an equivalence of the two
nomination formats, carrying each nomination's dependent path space with it. -/
private theorem pairCount_equiv (order : Nominations.Nom G ≃ Nom)
    (fit : 1+labelCount G*expWidth G ≤ (profile G).delta)
    (inc : ∀ ξ i μ, Path ξ i μ → Fin (labelCount G) → ℕ)
    (first : LiveBits (profile G).h (profile G).delta) (i : Fin (2^(profile G).h)) :
    pairCount fit (fun ξ j μ => inc ξ j (order μ)) first i = pairCount fit inc first i := by
  unfold pairCount
  let ξ := exteriorOf fit first
  exact order.sum_comp (fun μ : Nom => ∑ q : Path ξ i μ, if firstCheck fit first ξ i (inc ξ i μ q) then 1 else 0)

/-- Native compressed calls at the physical inputs built for this prefix.
Each accepted local stream corresponds to one path of the formal witness.
The `PairCall` reads back the counters in dense order and preserves the
header buffers. Its two budget conditions account for the linked reports
of the compressed call alone. -/
def CompressedCalls (W : Conditions G S H) (P : PairStageConditions G S H) (order : Nominations.Nom G ≃ Nom)
    (adv : Bits (profile G).advice) (fit : 1+labelCount G*expWidth G ≤ (profile G).delta)
    (inc : ∀ ξ i μ, Path ξ i μ → Fin (labelCount G) → ℕ) : Prop :=
  ∀ (cuts : AllCuts (profile G).h (profile G).delta) (i : Fin (2^(profile G).h)),
    let j := halves (profile G).h (.inl i)
    physicalTag cuts j = some .pair → (∀ side, Fields.ValidPadding (profile G) cuts j .pair side) →
    ∀ tr : Prepared W adv cuts j .pair, Output (profile G) (Header.base G.g) G.g.d W.word adv cuts j .pair (memory tr) →
      let ξ := exteriorOf fit (fst cuts)
      let F := Auxiliary.nominationFits G i (P.room i) P.width.le P.nominations
      let N := Nominations.indexed G F (memory tr) tr.tag
      ∀ μ, ∀ B : Auxiliary.PreparedBranch G (memory tr) i (PairedChain.headers adv ξ i) N μ,
        ∃ C : PairCall B (Path ξ i (order μ)) (inc ξ i (order μ)), ∀ q,
          RAMBuckets.cost Report.probes (C.indexed.logs q) ≤ S*(H-1) ∧ ∀ r ∈ C.indexed.logs q, 1+r.probes ≤ H

/-- The physical post-header first-half count from local compressed-call
semantics, the public scalar fits, and the witness's counter bound. -/
theorem pairContinuation_of_compressed (W : Conditions G S H) (P : PairStageConditions G S H)
    (order : Nominations.Nom G ≃ Nom) (adv : Bits (profile G).advice)
    (fit : 1+labelCount G*expWidth G ≤ (profile G).delta) (inc : ∀ ξ i μ, Path ξ i μ → Fin (labelCount G) → ℕ)
    (small : ∀ ξ i μ q a, inc ξ i μ q a < 2^(2*G.g.d)) (native : CompressedCalls W P order adv fit inc) :
    PairContinuation W adv fit inc := by
  intro cuts i j mode pad tr out
  have smallWord (μ) (q : Path (exteriorOf fit (fst cuts)) i (order μ)) (a) :
      inc (exteriorOf fit (fst cuts)) i (order μ) q a + 1 < 2^G.w :=
    (Nat.succ_le_of_lt (small _ _ _ q a)).trans_lt (Nat.pow_lt_pow_right (by decide) P.width)
  apply Eq.trans _ (pairCount_equiv order fit inc (fst cuts) i)
  apply @post_header_count G _ i cuts fit (fun ξ j μ => Path ξ j (order μ)) (fun ξ j μ => finitePaths ξ j (order μ)) (fun ξ j μ => inc ξ j (order μ)) _ adv out mode (pad .right) tr.tag (P.room i) P.width.le
    P.nominations P.initializer P.copy P.exponents P.labels P.row smallWord S H tr.logs
  intro ξ F N μ B
  obtain ⟨C,hC⟩ := native cuts i mode pad tr out μ B
  refine ⟨C,fun q => ?_⟩
  obtain ⟨cost,calls⟩ := hC q
  exact joinedCap P tr.logs tr.cost tr.probes tr.tag μ F B C.indexed q cost calls

end LiveProgram.LocalCount

end VPVNP
end Computability
end OAI
