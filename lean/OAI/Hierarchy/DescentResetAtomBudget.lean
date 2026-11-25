import OAI.Hierarchy.DescentAtomSchedule
import OAI.Hierarchy.DescentReentryCommonBlocks

namespace OAI
/-! # Pricing each installed reset-table descriptor in its physical address -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentCompiler DescentColonies
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {bits : P→ℕ} {d h C Ht : ℕ}
variable {A : MarkedWorld F d P bits} {price ε : ℝ} (Z : ResetInput A price ε h C Ht)
variable (T : Terminals Z) (S : AtomSchedule)

/-- Inject actual bank sites into the new common directory and block, via the concrete
installed-site names. This is also valid for a router with no active tables. -/
theorem bank_common_slots : Fintype.card Z.bank.Site≤Fintype.card ↥(commonNames Z T)*2^T.commonDepth := by
  let put (u : Z.bank.Site) := (resetNames Z T).symm (Sum.inr u)
  have one : Function.Injective put := (resetNames Z T).symm.injective.comp Sum.inr_injective
  exact (Fintype.card_le_of_injective put one).trans (common_site_count Z T)

/-- The bank site count in the true reset history uses one installed table per
actual bank slot. The increase in the size of the common host comes from the
terminal names of the old placement. -/
theorem reset_births {i r : ℕ} (age : i<S.length) (positions : Fintype.card Z.V≤S.hostSize i)
    (range : Z.k-T.commonDepth≤r) (gain : resetHostGain h (2^Z.n) Ht≤S.hostGain)
    (radix : 2^r≤S.radix) (blocks : 2^T.commonDepth≤S.groupCount (i+1)*S.radix) :
    Fintype.card Z.bank.Site≤S.batch := by
  have rooms : 2^(resetHostGain h (2^Z.n) Ht)*2^r≤2^S.hostGain*S.radix :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) gain) radix
  have next : Fintype.card ↥(commonNames Z T)≤S.hostSize (i+1) :=
    S.host_step positions ((placed_growth Z T range).trans (Nat.mul_le_mul_left _ rooms))
  exact S.reset_reserve age next blocks (bank_common_slots Z T)

/-- The exact retained inequality consumed when reentering the physical common-host stage. -/
theorem reset_atom_ledger {Old : Type} (rec : A.graph.Site→List Old)
    {i r hist : ℕ} (positive : 0<S.height) (hh : 0<hist) (age : i<S.length)
    (positions : Fintype.card Z.V≤S.hostSize i) (range : Z.k-T.commonDepth≤r)
    (gain : resetHostGain h (2^Z.n) Ht≤S.hostGain) (radix : 2^r≤S.radix)
    (blocks : 2^T.commonDepth≤S.groupCount (i+1)*S.radix)
    (past : S.Within i (∑u,(rec u).length)) :
    let total := (∑u,(rec u).length)+Fintype.card Z.bank.Site
    (1/((hist:ℝ)*(S.epochPower:ℝ)^S.priceExponent))*hist*(total:ℝ)≤
      ((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower ∧ S.Within (i+1) total := by
  let hit := S.advance past (reset_births Z T S age positions range gain radix blocks)
  exact ⟨S.paid positive hh age hit,hit⟩

/-- A real radix layout proves the population count of the reset source addresses. -/
theorem reset_digit_population {J : Type} [Fintype J] {k i : ℕ}
    (digits : Block T.commonDepth ≃ J×Block k) (groups : Fintype.card J≤S.groupCount i)
    (blockSize : 2^k≤S.radix) : 2^T.commonDepth≤S.groupCount i*S.radix := by
  have eqn : 2^T.commonDepth=Fintype.card J*2^k := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_congr digits
  exact eqn.le.trans (Nat.mul_le_mul groups blockSize)

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
