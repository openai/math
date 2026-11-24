import OAI.Computability.VPVNP.LiveExponentPaths
import OAI.Computability.VPVNP.LiveGroupContraction

/-!
# Native exponent paths in the first-half group count

The physical format supplies the exterior cut and both adjacent exponent
vectors. Once the mode and zero padding have passed, a nominated histogram
and a chosen compressor occurrence contribute one native completion exactly
when all outgoing exponents match. This includes the zero incoming vector
at the first group and the empty exterior field at the midpoint.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveExponent

open BurstRAM CutSchedule ExponentTrace ChainAssignments
open scoped Classical

variable {w t Z h Δ S H : ℕ}

/-- Decode the first-half cut's exterior and exponent fields for the selected group using the
fitted pair layout. -/
def pairFields (fit : 1 + t*Z ≤ Δ) (fst : LiveBits h Δ) (i : Fin (2^h)) :=
  firstHalfLayout h Δ (i.val+1) t Z (by omega) i.isLt fit (fst i)

/-- The outgoing format tests outside the exponent stage. -/
def pairFormat (fit : 1 + t*Z ≤ Δ) (fst : LiveBits h Δ) (i : Fin (2^h)) : Prop :=
  (pairFields fit fst i).1 = true ∧ (pairFields fit fst i).2.2.2 = fun _ => false

theorem firstCheck_iff (fit : 1 + t*Z ≤ Δ) (fst : LiveBits h Δ) (i : Fin (2^h)) (inc : Fin t → ℕ) :
    firstCheck fit fst (exteriorOf fit fst) i inc ↔ pairFormat fit fst i ∧
      ∀ a, (counters fit fst i.succ a).val = (counters fit fst i.castSucc a).val + inc a := by
  unfold firstCheck pairFormat
  change (pairFields fit fst i = (true, (pairFields fit fst i).2.1,
    (pairFields fit fst i).2.2.1, fun _ => false) ∧ _) ↔ _
  cases pairFields fit fst i with
  | mk mode rest =>
    obtain ⟨ext, counts, pad⟩ := rest
    simp

variable {Nom : Type*} [Fintype Nom]
variable {Path : Exterior h Δ → Fin (2^h) → Nom → Type*} [∀ ξ i μ, Fintype (Path ξ i μ)]

/-- Sum of the actual capped exponent-stage path counts after each nomination
and compressor path. The adjacent field test selects the local integer
factor in the contraction of the live chain. -/
theorem native_pairCount (fit : 1 + t*Z ≤ Δ) (fst : LiveBits h Δ) (i : Fin (2^h))
    (inc : ∀ ξ j μ, Path ξ j μ → Fin t → ℕ)
    (pub : Fin 5 → BurstRAM.Word w) (L : BufferLayout pub t Z) (hZ : 0 < Z) (hw : 2 ≤ w)
    (mem : ∀ μ, Path (exteriorOf fit fst) i μ → Memory w)
    (data : ∀ μ q, BufferValues pub (counters fit fst i.castSucc) (counters fit fst i.succ) (mem μ q))
    (read : ∀ μ q a, ((mem μ q) (counterAddr pub a).val).val = inc (exteriorOf fit fst) i μ q a)
    (small : ∀ μ q a, inc (exteriorOf fit fst) i μ q a + 1 < 2^w)
    (f : ℕ) (hcost : 5*(t*Z)+1 ≤ S*H) (hb : 5 ≤ H) :
    (if pairFormat fit fst i then ∑ μ, ∑ q : Path (exteriorOf fit fst) i μ,
      Nat.card (ActualPaths (digitTemplate.instantiate w pub).program (f+31) 0 (mem μ q) (withinCaps S H))
     else 0) = pairCount fit inc fst i := by
  unfold pairCount
  dsimp only
  by_cases good : pairFormat fit fst i
  · rw [ite_eq_left good]
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro q _
    let start (a : Fin t) : BurstRAM.Word w := mem μ q (counterAddr pub a).val
    have h := pathCount L hZ hw (data μ q) start (fun _ => rfl)
      (fun a => (read μ q a) ▸ small μ q a) f (withinCaps S H)
    rw [h]
    simp only [stageCaps pub (mem μ q) hcost hb, and_true, start, read, firstCheck_iff, good, true_and]
  · simp [good, firstCheck_iff]

end LiveExponent

end VPVNP
end Computability
end OAI
