import OAI.Computability.VPVNP.LiveEvaluatorNativeGroup
import OAI.Computability.VPVNP.LiveEvaluatorRawCells
import OAI.Computability.VPVNP.LiveEvaluatorRawPrepare
import OAI.Computability.VPVNP.LiveEvaluatorRAMSegmentCost

/-!
# Native evaluator-group counts on arbitrary configuration words

If a complete native path accepts, the preparing call checks both state
words and the two scans check every symbol. Thus malformed words admit no
accepting path. The cost-capped path count agrees with the decoded local
tail factor even when a configuration fails to decode.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorGroup

open BurstRAM (Word Memory ActualPaths withinCaps)
open LiveEvaluatorRAM (PrepLayout ConfigAt)
open LiveEvaluatorRAM.Schedule (Pub calls nativeProgram callFuel actualPathEquiv capPathEquiv)
open LiveEvaluatorEncoding (Code)
open UniversalMachine (Program)
open scoped Classical Fin.CommRing

variable {M w : ℕ} {p : Program} {pub : Pub → Word w} {m : Memory w}

/-- Native success forces the original raw memory of each boundary to
represent an evaluator configuration, including canonical halt padding. -/
theorem native_forces_configAt (hl : PrepLayout p pub M)
    (run : ActualPaths (nativeProgram p pub) (callFuel p) 0 m (fun _ => True)) :
    (∃ c : Code p.extra M, ConfigAt m (pub 1) c) ∧ (∃ c : Code p.extra M, ConfigAt m (pub 2) c) := by
  obtain ⟨_, mem, hprep, hall⟩ := actualPathEquiv p pub m hl.radius (calls_fit hl).le run
  obtain ⟨hpos, hlt, he₁, he₂, a, hapos, htarget, hact⟩ := hprep.raw_facts hl
  have hst₁ : mem (pub 1).val = m (pub 1).val := by simpa using he₁ 0 (by simp [calls])
  have hst₂ : mem (pub 2).val = m (pub 2).val := by simpa using he₂ 0 (by simp [calls])
  obtain ⟨⟨c, hc⟩, z, hz⟩ := rawCells_force_images p pub mem a hl hall hact
    (hst₁ ▸ ⟨hpos, hlt⟩) hapos (hst₂ ▸ htarget)
  exact ⟨⟨c, configAt_congr_block hc he₁⟩, ⟨z, configAt_congr_block hz he₂⟩⟩

theorem native_empty_of_malformed (hl : PrepLayout p pub M)
    (hbad : (¬ ∃ c : Code p.extra M, ConfigAt m (pub 1) c) ∨
      (¬ ∃ z : Code p.extra M, ConfigAt m (pub 2) z)) :
    IsEmpty (ActualPaths (nativeProgram p pub) (callFuel p) 0 m (fun _ => True)) :=
  ⟨fun run => by obtain ⟨h₁, h₂⟩ := native_forces_configAt hl run; exact hbad.elim (· h₁) (· h₂)⟩

/-- The native count under the actual global and per-call transcript caps
equals the local tail factor for every cut field. The endpoint memory
hypotheses identify the gathered words with their checked decoder, so the
two invalid-decoder cases give zero on both sides. -/
theorem tailCount_eq_capped {h Δ S H : ℕ} (layout : LiveEvaluatorTail.Layout p.extra M w Δ)
    (init : Code p.extra M) (bits : LiveChain.TailBits h Δ) (i : Fin (2 ^ h))
    (hl : PrepLayout p pub M)
    (ho : ∀ c, LiveEvaluatorTail.boundary layout init bits i.castSucc = some c ↔ ConfigAt m (pub 1) c)
    (hz : ∀ z, LiveEvaluatorTail.boundary layout init bits i.succ = some z ↔ ConfigAt m (pub 2) z)
    (hcost : 10 + 7 * (2 * (2 * M + 1)) ≤ S * H) (hcap : 10 ≤ H) :
    ChainAssignments.tailCount p layout init bits i =
      Nat.card (ActualPaths (nativeProgram p pub) (callFuel p) 0 m (withinCaps S H)) := by
  rw [Nat.card_congr (capPathEquiv p pub m hl.radius (calls_fit hl).le hl.width hl.states hcost hcap)]
  cases ha : LiveEvaluatorTail.boundary layout init bits i.castSucc with
  | none =>
    have := native_empty_of_malformed (m := m) hl (.inl (fun ⟨c, hc⟩ => by simpa [ha] using (ho c).mpr hc))
    simp [ChainAssignments.tailCount, ha]
  | some a =>
    cases hb : LiveEvaluatorTail.boundary layout init bits i.succ with
    | none =>
      have := native_empty_of_malformed (m := m) hl (.inr (fun ⟨z, hh⟩ => by simpa [hb] using (hz z).mpr hh))
      simp [ChainAssignments.tailCount, hb]
    | some b => exact tailCount_eq_native layout init bits i ha hb hl ((ho a).mp ha) ((hz b).mp hb)

end LiveEvaluatorGroup

end VPVNP
end Computability
end OAI
