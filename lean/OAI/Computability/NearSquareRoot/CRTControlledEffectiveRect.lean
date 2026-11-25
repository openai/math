import OAI.Computability.NearSquareRoot.CRTControlledEffectiveRectPrep
import OAI.Computability.NearSquareRoot.CRTControlledEffectiveRectRate

/-! # Calling a named physical rectangle from a packed swap

Only the header program is chosen from the represented geometry. The subsequent
matrix of calls accepts any emitted rectangle implementation and acts on every
record type, packed stream, and admissible payload.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Effective

open IntegerMultiplication Code Strip Strip.Dims Loom Adic NamedPacked InterchangeROMBinary
open CommonRegisters GeneratorSyntax Filter

abbrev Stock {X : Type} (P G B : X → Tape) (n : X → ℕ) (x : X) := stock 2 (P x) (G x) (B x) (n x)

def BeadSwap {X : Type} (r : Regime X) (P G B : X → Tape) (n : X → ℕ) (c : Cmd) (ρ : ℝ) : Prop :=
  ∀ (l : X → ℕ) {T : X → Type} (u : (x : X) → Series (T x)), (∀ x, (u x).count ≤ l x) →
    ∀ v : (x : X) → SpanKey (P x) (G x) (B x) (Block 2 (n x)) → T x → Bead,
    let s := Stock P G B n
    BreezeAt c (Spindle.modes n (τ := ρ)) r (fun x => (s x).count) l
      (together r.header (cloth s u v)) (cloth s u fun x a => v x (swapper _ _ _ a))

/-- The chosen prelude is independent of the rate, the selected native
command and all physical records. -/
theorem rectEmitter {X : Type} {r : Regime X} (P G B : X → Tape) (n : X → ℕ)
    (hn : r.Has (tally ∘ n)) (hp : Told r P) (hg : Told r G) (hb : Told r B)
    (guard : ∀ x j, j ∈ P x ++ G x ++ B x → j ≤ Net.Shuttle.base) :
    ∃ pre : Cmd, ∀ (ρ : ℝ) (c : Cmd) (D : ℕ), 0 ≤ ρ → RectPhysical c ρ D →
      BeadSwap r P G B n (pre.join c) ρ := by
  obtain ⟨pre,prep⟩ := prepareRect P G B n hn hp hg hb
  exact ⟨pre,fun ρ c D pos rect l _ u len v =>
    (prep l u len v ρ pos).next (native_beads rect pos P G B n hn hp hg hb guard l u len v)⟩

/-- A computable whole family of native backends produces the same shape
of executable for good and unchecked indices. The per-index rate appears
only as an assumption when estimating a particular member, and can be
changed without selecting a different command. -/
theorem rectFamily {X J : Type} [Primcodable J] {r : Regime X} (P G B : X → Tape) (n : X → ℕ)
    (hn : r.Has (tally ∘ n)) (hp : Told r P) (hg : Told r G) (hb : Told r B)
    (guard : ∀ x j, j ∈ P x ++ G x ++ B x → j ≤ Net.Shuttle.base)
    (native : J → Cmd) (effective : GeneratorSyntax.Effective ltr native)
    (R : ℕ) (registers : ∀ j, Within R (native j)) :
    ∃ (cmd : J → Cmd) (S : ℕ), GeneratorSyntax.Effective ltr cmd ∧ 0 < S ∧
      (∀ j, Within S (cmd j)) ∧ ∀ j ρ D, 0 ≤ ρ → RectPhysical (native j) ρ D →
        BeadSwap r P G B n (cmd j) ρ := by
  obtain ⟨pre,execute⟩ := rectEmitter P G B n hn hp hg hb guard
  obtain ⟨S,rs,pos,pr⟩ := ((eventually_ge_atTop R).and
    ((eventually_gt_atTop (0:ℕ)).and (RegisterSelect.within_eventually pre))).exists
  exact ⟨fun j => pre.join (native j),S,(effective_const ltr pre).join effective,pos,
    fun j => ⟨pr,RegisterSelect.within_mono rs _ (registers j)⟩,fun j ρ D => execute ρ (native j) D⟩

end Controlled.Effective

end NearSquareRoot
end Computability
end OAI
