import OAI.Computability.BorderVNP.PackedBankEpochFactors
import OAI.Computability.BorderVNP.PackedBankInnerPublicCaps
import OAI.Computability.BorderVNP.PackedBankPublicHistory

/-! # A single tile budget for all attained inner nodes of the outer history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited InheritedBank PhysicalEpochs
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2200000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

namespace EnrichedOuter.Machine

universe u

variable {S} {P : Type} [Fintype P] {bits : P → ℕ} {start T : ℕ} {shape : ℕ → PublicCapacity.Shape}
    {W : ℕ → Type} [∀ j, Fintype (W j)] {good : ∀ t, State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V w) (rows : ∀ n hn, (M n hn).F.SiteRows) (number : e.Entry → ℕ)
    (bottom : Admissible good 0) (base : Site.Programs bottom.val.pack.layout)
    (t : ℕ) (ht : t<T) (ord : Fin (fan S) → (packHistory bottom M.epoch t).Index)

local notation3 "children" => fun j => (packHistory bottom M.epoch t).term (ord j)
local notation3 "old" => fun j => M.historyPrivatePrograms rows number bottom base t ht.le (ord j)

/-- The complete outer horizon bounds every genuine stored node on any of its
intermediate histograms, including the original subdivisions at inner depth zero. -/
theorem partialPrivatePrograms_bankWithin_outer (ex : Bool) (B : ℕ) (hbase : SiteCap bottom.val.route base.bankFields ex B)
    (n : ℕ) (hn : n≤S.rounds) (pick : Fin (S.fanIn^n) → Fin (fan S))
    (q : (M t ht).F.FlatHist n hn (((M t ht).run children).flat ∘ pick)) :
    let E := M t ht
    let pr := E.partialPrivatePrograms (rows t ht) number children old n hn pick q
    RecordsWithin (E.F.flatPack n hn ((E.run children).flat ∘ pick) q) pr.bankFields ex (S.publicProgramFactor^T*B) := by
  intro E pr tile
  let childB := S.publicProgramFactor^t*B
  have caps (i : Fin (fan S)) : SiteCap (children i).val.route (old i).bankFields ex childB :=
    M.historyPrivatePrograms_bankCap rows number bottom base ex B hbase t ht.le (ord i)
  have actual := E.partialPrivatePrograms_bankWithin (rows t ht) number children old ex childB caps n hn pick q tile
  have pos : 0 < S.publicProgramFactor := by unfold SiteSchedule.publicProgramFactor SiteSchedule.bankRecordFactor epochRecordFactor; positivity
  apply (actual.trans (S.partialProgramFactor_le n hn childB)).trans
  change S.publicProgramFactor*(S.publicProgramFactor^t*B) ≤ S.publicProgramFactor^T*B
  rw [←Nat.mul_assoc,←pow_succ']
  exact Nat.mul_le_mul_right B (Nat.pow_le_pow_right pos (Nat.succ_le_of_lt ht))

end EnrichedOuter.Machine
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
