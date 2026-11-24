import OAI.Computability.VPVNP.LiveEvaluatorRAMMalformed
import OAI.Computability.VPVNP.LiveConfigGatherImage

/-!
# Tail-group path count after gathering both cut fields

Gathering the outgoing field preserves the disjoint incoming configuration
bank. On these two memory images the literal native group accepts precisely
the semantic branch choices, for arbitrary field bits including malformed
encodings.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorGroup

open BurstRAM (Word Memory ActualPaths withinCaps)
open LiveEvaluatorEncoding (Code format fieldWords)
open LiveEvaluatorRAM (ConfigAt PrepLayout)
open LiveEvaluatorRAM.Schedule (Pub nativeProgram callFuel calls capPathEquiv)
open LiveConfigGather (gathered gathered_outside gathered_configAt_iff)
open UniversalMachine (Program)
open scoped Fin.CommRing Classical

variable {w M k extra : ℕ}

theorem configAt_gathered_disjoint_iff {base dst : Word w} (m : Memory w)
    (hbase : base.val + calls M ≤ 2 ^ w) (hdst : dst.val + k ≤ 2 ^ w)
    (hdis : base.val + calls M ≤ dst.val ∨ dst.val + k ≤ base.val)
    (bits : Fin (k*w) → Bool) (c : Code extra M) :
    ConfigAt (gathered dst hdst bits m) base c ↔ ConfigAt m base c := by
  have he (i : ℕ) (hi : i < calls M) :
      gathered dst hdst bits m (base + (i : Word w)).val = m (base + (i : Word w)).val := by
    apply gathered_outside
    rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  exact ⟨fun hc => configAt_congr_block hc he, fun hc => configAt_congr_block hc fun i hi => (he i hi).symm⟩

theorem fieldWords_eq_calls (M : ℕ) : fieldWords M = calls M := by unfold fieldWords calls; omega

/-- Both gathered banks represent exactly their decoded cut codes.
`PrepLayout` separately reserves the five-word instruction scratch area. -/
theorem gathered_boundary_images {p : Program} {pub : Pub → Word w} (hl : PrepLayout p pub M)
    (hdis : (pub 1).val + calls M ≤ (pub 2).val ∨ (pub 2).val + calls M ≤ (pub 1).val)
    (incoming outgoing : Fin (fieldWords M*w) → Bool) (m : Memory w) :
    let m₁ := gathered (k := fieldWords M) (pub 1) (by simpa only [fieldWords_eq_calls] using hl.oldFit) incoming m
    let m₂ := gathered (k := fieldWords M) (pub 2) (by simpa only [fieldWords_eq_calls] using hl.outFit) outgoing m₁
    (∀ c : Code p.extra M, ConfigAt m₂ (pub 1) c ↔ (format hl.width hl.states).decode incoming = some c) ∧
    (∀ c : Code p.extra M, ConfigAt m₂ (pub 2) c ↔ (format hl.width hl.states).decode outgoing = some c) := by
  exact ⟨fun c => (configAt_gathered_disjoint_iff _ hl.oldFit (by simpa only [fieldWords_eq_calls] using hl.outFit) (by simpa [fieldWords_eq_calls] using hdis) outgoing c).trans
    (gathered_configAt_iff ..), fun c => gathered_configAt_iff ..⟩

/-- The capped native count on both gathers, written directly as a function
of the adjacent raw cut fields. A malformed field contributes zero. -/
theorem card_two_gathers {p : Program} {pub : Pub → Word w} (hl : PrepLayout p pub M)
    (hdis : (pub 1).val + calls M ≤ (pub 2).val ∨ (pub 2).val + calls M ≤ (pub 1).val)
    (incoming outgoing : Fin (fieldWords M*w) → Bool) (m : Memory w) {S H : ℕ}
    (hcost : 10 + 7 * (2 * (2 * M + 1)) ≤ S * H) (hcap : 10 ≤ H) :
    let m₁ := gathered (k := fieldWords M) (pub 1) (by simpa only [fieldWords_eq_calls] using hl.oldFit) incoming m
    let m₂ := gathered (k := fieldWords M) (pub 2) (by simpa only [fieldWords_eq_calls] using hl.outFit) outgoing m₁
    Nat.card (ActualPaths (nativeProgram p pub) (callFuel p) 0 m₂ (withinCaps S H)) =
      ∑ bit : Bool, if ∃ c z : Code p.extra M,
        (format hl.width hl.states).decode incoming = some c ∧
        (format hl.width hl.states).decode outgoing = some z ∧
        LiveEvaluatorStep.nextCode p c bit = some z ∧ z ≠ .rejected then 1 else 0 := by
  let m₂ := gathered (k := fieldWords M) (pub 2) (by simpa only [fieldWords_eq_calls] using hl.outFit) outgoing
    (gathered (k := fieldWords M) (pub 1) (by simpa only [fieldWords_eq_calls] using hl.oldFit) incoming m)
  obtain ⟨ho, hz⟩ := gathered_boundary_images hl hdis incoming outgoing m
  dsimp only
  rw [Nat.card_congr (capPathEquiv p pub m₂ hl.radius (calls_fit hl).le hl.width hl.states hcost hcap)]
  cases ha : (format hl.width hl.states).decode incoming with
  | none =>
    have := native_empty_of_malformed (m := m₂) hl (.inl fun ⟨c, hc⟩ => by simpa [ha] using (ho c).mp hc)
    simp
  | some c =>
    cases hb : (format hl.width hl.states).decode outgoing with
    | none =>
      have := native_empty_of_malformed (m := m₂) hl (.inr fun ⟨z, h⟩ => by simpa [hb] using (hz z).mp h)
      simp
    | some z =>
      rw [card_nativeGroup hl ((ho c).mpr ha) ((hz z).mpr hb)]
      simp

end LiveEvaluatorGroup

end VPVNP
end Computability
end OAI
