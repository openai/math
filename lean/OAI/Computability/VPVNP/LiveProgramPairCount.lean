import OAI.Computability.VPVNP.LiveProgramPair
import OAI.Computability.VPVNP.LiveProgramPairExponent
import OAI.Computability.VPVNP.RAMFinite

/-! # The contribution of the native first-half stage sequence

Once the header has accepted its fields, the four completed stages expose
the histogram and compressed computation. The terminal native test compares
the physical counters and both incident exponent fields. Resource bounds
apply to the joined reports, including the earlier header and router.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Chronology

open BurstRAM BurstRAM.PrivateRAM LiveStageLink LiveExponent ChainAssignments ExponentTrace
open scoped Classical

variable {G : Group} {m : Memory G.w} {h Δ t Z : ℕ}
  {Nom : Type*} [Fintype Nom]
  {Path : ExponentTrace.Exterior h Δ → Fin (2^h) → Nom → Type*} [∀ ξ i μ, Fintype (Path ξ i μ)]

/-- The native branch following the header contributes the paper's local
`pairCount` on the outgoing mode and padding test. Each stage is classified
by its own traces, preserving coincident branches as distinct paths. -/
theorem count (fit : 1+t*Z ≤ Δ) (fst : LiveBits h Δ) (i : Fin (2^h))
    (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
    (A : Chronology G m Nom (Path (exteriorOf fit fst) i))
    (L : BufferLayout G.exponentPub t Z) (hZ : 0 < Z) (hw : 2 ≤ G.w)
    (hf : 31 ≤ G.clockAt Stage.exponents) (fresh : ∀ a : Fin t, counterAddr G.exponentPub a ≠ G.addr)
    (data : ∀ μ q, BufferValues G.exponentPub (counters fit fst i.castSucc) (counters fit fst i.succ)
      ((A.pair μ).memory q))
    (read : ∀ μ q a, (((A.pair μ).memory q) (counterAddr G.exponentPub a).val).val = inc (exteriorOf fit fst) i μ q a)
    (small : ∀ μ q a, inc (exteriorOf fit fst) i μ q a+1 < 2^G.w)
    (cap : List (Report G.w) → Prop) (maxCalls : ℕ)
    (hbound : ∀ rs, cap rs → RAMBuckets.cost Report.probes rs ≤ maxCalls)
    (enough : ∀ μ q, cap (A.prefixLogs μ q ++
      (stageReports G.exponentPub t Z ((A.pair μ).memory q)).map
        (linkedReport G.nextStage G.addr Stage.exponents))) :
    (if pairFormat fit fst i then Nat.card (ActualPaths G.P G.clock 0 m cap) else 0) =
      pairCount fit inc fst i := by
  let Tail (μ : Nom) (q : Path (exteriorOf fit fst) i μ) :=
    ActualPaths G.P G.clock 0 ((A.pair μ).memory q) (fun rs => cap (A.prefixLogs μ q ++ rs))
  have (μ : Nom) (q : Path (exteriorOf fit fst) i μ) : Finite (Tail μ q) := by
    apply finite_actualPaths (maxCalls := maxCalls)
    intro rs hr
    have h := hbound _ hr
    rw [RAMBuckets.cost_append] at h
    omega
  unfold pairCount
  dsimp only
  by_cases good : pairFormat fit fst i
  · rw [ite_eq_left good, ← Nat.card_congr (A.paths cap), Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro μ _
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro q _
    let last := (A.pair μ).memory q
    let v := fun a : Fin t => last (counterAddr G.exponentPub a).val
    have htag : G.tagged Stage.exponents last := (A.pair μ).tagged_memory rfl q
    have h := G.exponent_count L hZ hw hf fresh last htag _ _ (data μ q) v (fun _ => rfl)
      (fun a => (read μ q a) ▸ small μ q a) (fun rs => cap (A.prefixLogs μ q ++ rs))
    rw [h]
    simp only [enough, and_true,v,last,read,firstCheck_iff,good,true_and]
  · simp [good,firstCheck_iff]

end LiveProgram.PairStages.Group.Chronology

end VPVNP
end Computability
end OAI
