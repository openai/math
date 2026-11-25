import OAI.Computability.NearSquareRoot.CRTPositionWindowRow
import OAI.Computability.NearSquareRoot.CRTPositionRawRows

/-! # A linear-space middle-field permutation from its physical table -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionRows

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Adic IntegerMultiplication.Loom PositionProgram NearSquareRoot.Space
noncomputable section

private def cells (x : Window) (z : Block 2 x.k) : Tree :=
  strip (Series.natural x.w) (x.record z)

/-- The selection happens after the universal physical program has fixed its
overhead degree, so neither the low nor the high reserve enters that choice. -/
theorem rawTableRows {ρ : ℝ} (hρ : 1/2 < ρ) : ∃ D : ℕ, ∀ {I : Type} (pick : I → Window),
    (∀ i, payloadBits D (pick i).k ≤ (pick i).lo) →
    (∀ i, payloadBits D (pick i).k ≤ (pick i).hi) →
    (∀ i, positionFactor ρ (pick i).k ≤ 2^(pick i).hi) →
    let V i := 2^(pick i).k*(pick i).w
    BoundedTask (fun i => V i*(positionFactor ρ (pick i).k+1)) V
      (fun i => .fork (send (Window.header (pick i))) (stripe (line 2 (pick i).k) (cells (pick i))))
      (fun i => stripe (line 2 (pick i).k) (cells (pick i) ∘ (pick i).routed)) := by
  have hRaw : Window.regime.Has (fun x => tally (x.mid+x.lo)) :=
    (show IntegerMultiplication.Staff.Realizes Window.regime Window.mid from Window.hasMid).plus
      (show IntegerMultiplication.Staff.Realizes Window.regime Window.lo from Window.hasLo)
  have fit (x : Window) : x.hi+(x.mid+x.lo) = x.k := by
    have := x.fit; unfold Window.mid; omega
  have bound (x : Window) (z : Block 2 x.k) : (cells x z).count ≤ 2*x.w+1 := by
    simpa only [cells,Series.count_natural] using bulk (Series.natural x.w) (x.record z)
  obtain ⟨D,run⟩ := rawRowsOn Window.hi Window.mid Window.lo Window.k Window.w fit Window.hasHi hRaw
    Window.outer cells (fun x => cells x ∘ x.routed) bound (fun x z => bound x _) (fun x => positionRate ρ x.mid)
    (Window.rawBreeze hρ)
  refine ⟨D,fun pick low high factor => ?_⟩
  apply run pick (fun i => (pick i).k) (fun i => positionFactor ρ (pick i).k) (fun _ => le_rfl)
    (fun i => by have := (pick i).fit; omega) (fun i => (pick i).pos) low high _ factor
  intro i
  exact positionFactor_pays (by linarith) (by unfold Window.mid; omega)

/-- A middle-field table on the actual coded header permutes the interior
of complete native addresses, for an arbitrary ordered series of payload
bits. The bound is in the physical, unpadded record volume. -/
theorem tableMiddle {ρ : ℝ} (hρ : 1/2 < ρ) : ∃ D : ℕ, ∀ {I : Type}
    (k lo hi : I → ℕ) (fit : ∀ i, lo i+hi i ≤ k i)
    {U : I → Type} (u : (i : I) → Series (U i)) (_pos : ∀ i, 0 < (u i).count)
    (q : (i : I) → Equiv.Perm (Fin (k i-lo i-hi i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead),
    (∀ i, payloadBits D (k i) ≤ lo i) → (∀ i, payloadBits D (k i) ≤ hi i) →
    (∀ i, positionFactor ρ (k i) ≤ 2^(hi i)) →
    let V i := 2^(k i)*(u i).count
    BoundedTask (fun i => V i*(positionFactor ρ (k i)+1)) V
      (fun i => .fork (send (tally (hi i),tally (k i-lo i-hi i),tally (lo i),Reflections.table (q i)))
        (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i a => f i (ReserveTile.lift (fit i) (flatBitPullback (q i)) a))) := by
  obtain ⟨D,run⟩ := rawTableRows hρ
  refine ⟨D,fun k lo hi fit U u pos q f low high factor => ?_⟩
  let pick i : Window := ⟨k i,lo i,hi i,(u i).count,pos i,fit i,q i,
    fun z j => f i z ((u i).follow j)⟩
  have h := run pick low high factor
  have cell (i) (a : Block 2 (k i)) : cells (pick i) a = strip (u i) (f i a) :=
    stripe_natural_follow (u i) (fun j => send (f i a j))
  apply h.conform (fun _ => rfl) (fun _ => rfl)
  · intro i
    exact congrArg (Tree.fork _) (congrArg (stripe _) (funext (cell i)))
  · intro i
    exact congrArg (stripe _) (funext fun a => cell i ((pick i).routed a))

end
end Controlled.PositionRows

end NearSquareRoot
end Computability
end OAI
