import OAI.Computability.NearSquareRoot.CRTControlledReserveBranch
import OAI.Computability.NearSquareRoot.CRTControlledReserveSmallRun
import OAI.Computability.NearSquareRoot.CRTPositionClock

/-! # A single position-routing command across the finite width cutoff -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveSmall

open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code
open IntegerMultiplication.Strip IntegerMultiplication.Loom NearSquareRoot.Space

noncomputable section

/-- Read and retain the original table and records while testing whether to enter
the large-width branch. -/
theorem prepareCutoff {I : Type} (K : ℕ) (k V : I → ℕ) (p : ∀ i, Equiv.Perm (Fin (k i)))
    (data : I → Tree) (area : ∀ i, 2^(k i) ≤ V i) (vol : Volume (fun i => (V i : ℝ)) data) :
    let input i := Tree.fork (send (Reflections.table (p i))) (data i)
    BoundedTask V V input (fun i => .fork (.atom (decide (K < k i))) (input i)) := by
  intro input
  let r : Regime I := ⟨k, fun i => send (Reflections.table (p i)), 2, 2,
    fun i => Reflections.table_size (p i)⟩
  have ripe := ReserveStage.ripeOfWidth (r := r) (k := k) (fun _ => le_rfl) area
  have tab : r.Has (fun i => Reflections.table (p i)) := r.self
  have program : Easy (fun t : Reflections.Table => Iter.small (tally K,t)) :=
    ((Easy.const (tally K)).pair Easy.identity).compose Iter.small_easy
  have flag : r.Has (fun i => decide (K < k i)) := by
    simpa only [Iter.small, tally_length, Reflections.table, List.length_ofFn] using tab.ez program
  have headvol := (tab.cooked ripe).small
  have sourcevol := headvol.fork vol ripe.1
  have header := Carries.dropRight ripe.1 headvol vol
  exact boundedOfCarries ((header.chain (flag.cooked ripe)).twice (Carries.idles ripe.1 sourcevol))

/-- A large-width algorithm on the indicated subtype extends to all widths.
Its real table header selects the finite fallback on the complementary inputs. -/
theorem dispatchCloth {I X : Type} [Codec X] {U : I → Type} (K C : ℕ) (k V T : I → ℕ)
    (u : (i : I) → Series (U i)) (p : ∀ i, Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → X)
    (room : ∀ i, V i ≤ T i) (area : ∀ i, 2^(k i) ≤ V i)
    (volume : ∀ i, (cloth (fun i => line 2 (k i)) u f i).count ≤ C*V i)
    (large : BoundedTask (fun i : {i // K < k i} => T i) (fun i => V i)
      (fun i => .fork (send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f i))
      (fun i => cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z)) i)) :
    BoundedTask T V
      (fun i => .fork (send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) := by
  apply boundedWidthBranch K k V T _ _ room _ _ large
  · apply prepareCutoff K k V p _ area
    refine ⟨C,fun i => ?_⟩
    change ((cloth (fun i => line 2 (k i)) u f i).count : ℝ) ≤ (C : ℝ)*(V i : ℝ)
    exact_mod_cast volume i
  · let idx := {i // k i ≤ K}
    have run := boundedRun K (fun i : idx => k i) (fun i => C*V i) (fun i => p i)
      (fun i => i.property) (fun i z => strip (u i) (f i z)) (fun i => volume i)
    apply run.bound (C+1) (C+1)
    · intro i
      have h := Nat.mul_le_mul_left C (room i)
      simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
      omega
    · intro i
      simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
      omega

/-- For positive bead records the encoded cloth fits in a fixed multiple of the
bit volume, uniformly over all address widths. -/
theorem beadClothCap {I : Type} {U : I → Type} (k w : I → ℕ) (u : (i : I) → Series (U i))
    (f : (i : I) → Block 2 (k i) → U i → Bead)
    (pos : ∀ i, 0 < w i) (width : ∀ i, (u i).count ≤ w i) (i : I) :
    (cloth (fun i => line 2 (k i)) u f i).count ≤ 5*(2^(k i)*w i) := by
  have low (z) : (strip (u i) (f i z)).count ≤ 2*w i+1 :=
    (bulk (u i) (f i z)).trans (by have := width i; omega)
  have cap := stripe_size (line 2 (k i)) (fun z => strip (u i) (f i z)) _ low
  rw [lineSize] at cap
  change (stripe _ _).count ≤ _
  refine cap.trans ?_
  have hp : 1 ≤ 2^(k i) := Nat.two_pow_pos _
  have vol : 2^(k i) ≤ 2^(k i)*w i := Nat.le_mul_of_pos_right _ (pos i)
  nlinarith only [hp, vol]

/-- The fixed cutoff contributes only a constant to the physical routing clock.
The large-width algorithm can be supplied with its positive record width and its own cutoff. -/
theorem dispatchPositionCloth {I : Type} {U : I → Type} (K : ℕ) (ρ : ℝ) (k w : I → ℕ)
    (u : (i : I) → Series (U i)) (p : ∀ i, Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead)
    (pos : ∀ i, 0 < w i) (width : ∀ i, (u i).count ≤ w i)
    (large : BoundedTask (fun i : {i // K < k i} => 2^(k i)*w i*(PositionProgram.positionFactor ρ (k i)+1))
      (fun i => 2^(k i)*w i)
      (fun i => .fork (send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f i))
      (fun i => cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z)) i)) :
    BoundedTask (fun i => 2^(k i)*w i*(PositionProgram.positionFactor ρ (k i)+1)) (fun i => 2^(k i)*w i)
      (fun i => .fork (send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) :=
  dispatchCloth K 5 k _ _ u p f (fun _ => Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
    (fun i => Nat.le_mul_of_pos_right _ (pos i)) (beadClothCap k w u f pos width) large

end
end Controlled.ReserveSmall

end NearSquareRoot
end Computability
end OAI
