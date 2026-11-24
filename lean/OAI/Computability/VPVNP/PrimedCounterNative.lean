import OAI.Computability.VPVNP.PrimedCounterInputPrefix
import OAI.Computability.VPVNP.PrimedCounterLength
import OAI.Computability.VPVNP.PrimedCounterPostHistory

/-!
# The exact native path count of the auxiliary RAM

Section 11 realizes the coefficient of the primed pair polynomial on one
fixed private-RAM instruction table. Each accepting path consists of the
actual binary choices made at the designated internal endpoints and at the
ordered parser visits. The full native history satisfies the probe caps
and ends in an accepting halt.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Data

open BurstRAM PrimedInputRAM PrimedStackRAM

variable {L : Lengths} {n r H s w : ℕ} {Q : Layout L n r H w}

/-- The native run on one complete chronological tape accepts precisely
when the assembled input bits and the joint production counts pass (9.4).
The transcript caps admit every such path. -/
theorem accepts_iff (D : Data Q s) (hf : D.Fits) (S K : ℕ) (hK : 15 ≤ K)
    (hbudget : 15*D.total ≤ S*K) (raw : Chronology.PairTape n r D.labels) :
    (∃ rs, runSegment D.machine.program D.fuel (some 0) D.initial (List.ofFn raw) = some rs ∧
      withinCaps S K rs) ↔ Chronology.Accepts Q D.header D.degree D.root D.nomination raw := by
  rw [Fold.chronology_iff Q D.header D.degree D.root hf.degree_eq (labelIndex n n s)]
  change _ ↔ ∃ shared, Chronology.inputPart raw = Chronology.inputCalls Q shared ∧ (D.postLogical shared raw).isSome
  constructor
  · rintro ⟨rs,hr,_⟩
    obtain ⟨shared,he⟩ := InputPrefix.full_recover D hf raw rs hr
    obtain ⟨front,hsplice,_,_⟩ := InputPrefix.full_splice D hf raw shared he
    rw [hsplice] at hr
    obtain ⟨tail,ht,_⟩ := Option.map_eq_some_iff.mp hr
    exact ⟨shared,he,(D.postRun_isSome hf shared raw).2 (by rw [ht]; rfl)⟩
  · rintro ⟨shared,he,hok⟩
    obtain ⟨tail,ht⟩ := Option.isSome_iff_exists.mp ((D.postRun_isSome hf shared raw).1 hok)
    obtain ⟨front,hsplice,hlen,hfront⟩ := InputPrefix.full_splice D hf raw shared he
    obtain ⟨_,_,htlen,_,_,htail⟩ := D.postRun_reports hf shared raw tail ht
    refine ⟨front++tail, by rw [hsplice,ht]; rfl, History.within (bound := 14) ?_ hK ?_⟩
    · intro rep hrep
      exact (List.mem_append.mp hrep).elim (hfront rep) (htail rep)
    · rw [List.length_append, hlen, htlen, D.postItems_length]
      exact hbudget

/-- Parsimony from complete accepted native paths to the chronological
tapes recognized by the coefficient counter. -/
noncomputable def pathEquiv (D : Data Q s) (hf : D.Fits) (S K : ℕ) (hK : 15 ≤ K)
    (hbudget : 15*D.total ≤ S*K) :
    ActualPaths D.machine.program D.fuel 0 D.initial (withinCaps S K) ≃
      {raw : Chronology.PairTape n r D.labels // Chronology.Accepts Q D.header D.degree D.root D.nomination raw} :=
  (D.historyEquiv hf S K).trans (Equiv.subtypeEquivRight (D.accepts_iff hf S K hK hbudget))

/-- The actual native machine realizes the integer coefficient `f` of
the primed pair in equation (9.4), with no restrictions on internal bits. -/
theorem native_count (D : Data Q s) (hf : D.Fits) (S K : ℕ) (hK : 15 ≤ K)
    (hbudget : 15*D.total ≤ S*K) :
    (Nat.card (ActualPaths D.machine.program D.fuel 0 D.initial (withinCaps S K)) : ℤ) =
      (PairCoefficient.jointPolynomial D.degree D.root (PrimedInputRAM.input Q.program Q.fits D.header)).coeff D.nomination := by
  rw [Nat.card_congr (D.pathEquiv hf S K hK hbudget)]
  have hn : n ≤ 2^w := (capacity_fit D.base hf.scratch).le
  exact Chronology.count Q D.header D.degree D.root hf.degree_eq hn hf.states.le D.nomination

end PrimedCounter.Data

end VPVNP
end Computability
end OAI
