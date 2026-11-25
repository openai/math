import OAI.Computability.NearSquareRoot.CRTControlledReservePack
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomDeck

/-! # Unrestricted and reserve-priced runs of the same native mask frames -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReservePack

open IntegerMultiplication Code Adic Strip Packed Loom Dims Space EffectiveBoundedTask

/-- The original preparation clock covers every row, regardless of whether
the trailing reserve is wide enough to absorb the compact-header work. -/
def envelopeClock {X : Type} (r : Regime X) (n B m : X → ℕ) (d : ℕ) (x : X) :=
  records n x * (packed B m x + (r.scale x+1)^d)

/-- A named bounded execution terminates from any outer environment and deck. -/
theorem rawEnvelopeFits {X : Type} {c : Cmd} {t s : X → ℕ} {p q : X → Tree}
    (h : Runs c t s p q) (x : X) : ∃ T : ℕ, ∀ env, Fits.value env c 0 (p x) (q x) T := by
  obtain ⟨D,run⟩ := h
  exact ⟨_,LoomRegisters.fits_of_bounded_decks c (p x) (q x) (D*(t x+1))
    (fun env park b hb => (run x env park b hb).fits)⟩

/-- Select the physical preparation and restoration commands on all inputs.
When the low reserve pays the descriptor overhead, the same preparation runs
in linear time and workspace. Both commands retain unconditional correctness. -/
theorem nativeEnvelope {X Z : Type} [Codec Z] {r : Regime X} {U : X → Type}
    (u : (x : X) → Series (U x)) (n B m : X → ℕ)
    (f g : (x : X) → Block 2 (n x+B x) → U x → Z)
    (hm : ∀ x, 0 < m x) (hu : ∀ x, (u x).count ≤ m x)
    (hn : r.Has (tally ∘ n)) (hB : r.Has (tally ∘ B))
    {head : X → Tree} (hh : r.Small head) (C : ℕ)
    (symbolF : ∀ x a j, (send (f x a j)).count ≤ C)
    (symbolG : ∀ x a j, (send (g x a j)).count ≤ C) :
    ∃ (d : ℕ) (pre post : Cmd),
      Runs pre (envelopeClock r n B m d) (envelopeClock r n B m d)
        (together r.header (raw u n B f)) (together (restoreRulers u n B) (together head (grouped u n B f))) ∧
      Runs post (volume n B m) (volume n B m)
        (together (restoreRulers u n B) (grouped u n B g)) (raw u n B g) ∧
      ∀ {Y : Type} (select : Y → X) (Q : Y → ℕ), (∀ y, r.scale (select y) ≤ Q y) →
        (∀ y, payloadBits d (Q y) ≤ B (select y)) →
      Runs pre (volume n B m ∘ select) (volume n B m ∘ select)
        (together r.header (raw u n B f) ∘ select)
        (together (restoreRulers u n B) (together head (grouped u n B f)) ∘ select) := by
  have live := raw_alive (r:=r) u n B f m hm hu C symbolF
  obtain ⟨d,forward⟩ := prepare u n B f m hm hn hB hh live
  have all : BoundedTask (envelopeClock r n B m d) (envelopeClock r n B m d)
      (together r.header (raw u n B f)) (together (restoreRulers u n B) (together head (grouped u n B f))) := by
    apply boundedOfCarries
    have price : (fun x => (envelopeClock r n B m d x : ℝ)) = mass r (records n) (packed B m) d := by
      funext x
      simp only [envelopeClock,mass,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one]
    rw [price]
    exact forward
  obtain ⟨pre,runPre⟩ := all
  obtain ⟨post,runPost⟩ := restoreBounded u n B g m hm hu C symbolG
  refine ⟨d,pre,post,runPre,runPost,?_⟩
  intro Y select Q scale low
  have cap (y : Y) : (r.scale (select y)+1)^d ≤ packed B m (select y) :=
    (Nat.pow_le_pow_left (Nat.succ_le_succ (scale y)) d).trans
      ((payload_capacity d (Q y) (m (select y)) (hm _)).trans
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (low y))))
  have bound (y : Y) : envelopeClock r n B m d (select y)+1 ≤ 2*(volume n B m (select y)+1) := by
    unfold envelopeClock volume
    rw [Nat.mul_add,Nat.mul_add,Nat.mul_one]
    have := Nat.mul_le_mul_left (records n (select y)) (cap y)
    omega
  exact ((show Runs pre _ _ _ _ from runPre).on select).bound 2 2 bound bound

end Controlled.ReservePack

end NearSquareRoot
end Computability
end OAI
