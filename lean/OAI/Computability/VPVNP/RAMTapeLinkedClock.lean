import OAI.Computability.VPVNP.RAMTapeSiteCore
import OAI.Computability.VPVNP.RAMTapeOwnPrefixOperands
import OAI.Computability.VPVNP.RAMProcessorPhysicalClock

/-!
# Clock and input capacity of the linked live coefficient program

Startup computes the public operands, reads the cuts and nominates the
private choice string. The fixed per-choice program then runs the site graph
and checks the sorting fields. Its exact budget includes initialization of
the architectural registers, the site's first record, and the terminal test.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts

open BurstRAM SiteProcessor Filter

/-- The complete clock for a raw site, including its public input stage. -/
def linkedTicks {d e w : ℕ} (regs cstart : ℕ) (x : SiteCutBank.Input d e w) : ℕ :=
  cstart*(x.n+1)^max 7 (x.u+1) + coreSteps regs x

/-- Absorb the actual entry, register reset and first-record costs in the
startup term of the physical two-tape estimate. -/
theorem linkedTicks_le {d e w : ℕ} (regs cstart : ℕ) (x : SiteCutBank.Input d e w)
    (hu : 1 ≤ x.u) (hH : 2^e ≤ 2*x.n) (hw : w ≤ x.n) :
    linkedTicks regs cstart x ≤ totalStackCutoff d e w regs (x.n^x.u)
      ((cstart+500+11*regs)*(x.n+1)^max 7 (x.u+1)) := by
  let N := (x.n+1)^max 7 (x.u+1)
  have hn : x.n+1 ≤ N := Nat.le_self_pow (by dsimp [N]; omega) _
  have hp : (x.n+1)^(x.u+1) ≤ N := Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right ..)
  have hentry := (entrySteps_le x hu hH hw).trans (Nat.mul_le_mul_left 400 hp)
  have hr : regs*(8*w+3) ≤ (11*regs)*N := by
    rw [show 11*regs*N = regs*(11*N) by ring]
    exact Nat.mul_le_mul_left _ (by omega)
  change cstart*N + (perChoiceBudget d e w regs (x.n^x.u) + entrySteps x) ≤
    totalStackCutoff d e w regs (x.n^x.u) ((cstart+500+11*regs)*N)
  simp only [perChoiceBudget, SiteCutBank.graphBudget, totalStackCutoff, Nat.add_mul]
  omega

set_option exponentiation.threshold 100031 in
/-- Live integer exponents give the same bucket capacity as the paper's real
formula. A single threshold handles all site addresses, all incident choices,
the literal table prefix, and both the tighter site clock and `K_*`. -/
theorem eventually_live_clock (prog : UniversalMachine.Program) (regs cstart ports B a b : ℕ)
    (hB : 1 ≤ B) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop,
      let d := addressWidth B n
      let e := roundedUp a b n
      let w := CursorBounds.wordBits B n
      ProcessorInput.Fits prog n d (2^e) w ∧ (UniversalMachine.programPrefix prog).length ≤ w ∧
      ∀ x : SiteCutBank.Input d e w, x.n = n → x.u = 10000 →
        let T := linkedTicks regs cstart x
        T*(6*(n+(ports+1)+T)+4) ≤ n^100030 ∧ T*(6*(n+(ports+1)+T)+4) ≤ n^clockExponent := by
  let δ := 1-(a:ℝ)/b
  have hb : 0 < (b:ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hδ : 0 < δ := sub_pos.mpr ((div_lt_one hb).mpr (by exact_mod_cast hab))
  have hδ' : δ ≤ 1 := sub_le_self _ (by positivity)
  have eqe (n : ℕ) : Compression.bucketExponent (1-δ) n = roundedUp a b n := by
    rw [roundedUp_eq, show 1-δ = (a:ℝ)/b by dsimp [δ]; ring]
  filter_upwards [eventually_both_application_clocks hB hδ.le hδ' regs (cstart+500+11*regs)
    ports 0 0 0, eventually_bothProcessorBudgets hB hδ.le hδ', eventually_liveInputFits prog B hδ hδ',
    OwnPrefix.Physical.eventually_prefix_fits prog hB] with n clock budget fit pre
  have hc := clock.1
  have hbound := budget.1
  rw [eqe] at hc hbound
  change ProcessorInput.Fits prog n _ (2^(Compression.bucketExponent (1-δ) n)) _ at fit
  rw [eqe] at fit
  refine ⟨fit, pre, ?_⟩
  intro x hxn hxu
  have hH := hbound.bucket_le.trans_eq (congrArg (2*·) hxn.symm)
  have hw := hbound.word_le.trans_eq hxn.symm
  have ht := linkedTicks_le regs cstart x (by omega) hH hw
  rw [hxn, hxu] at ht
  exact hc (n^10000) ((cstart+500+11*regs)*(n+1)^max 7 (10000+1)) (linkedTicks regs cstart x)
    le_rfl le_rfl ht

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
