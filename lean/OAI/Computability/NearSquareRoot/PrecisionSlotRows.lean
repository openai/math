import OAI.Computability.NearSquareRoot.PrecisionSlotTable
import OAI.Computability.NearSquareRoot.PrecisionPreparedGrid

/-! # Complete opcode-indexed phase rows on the guarded convolution grid -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Strip Staff Carry Dusk ShortFourier AxisWord FixedPoint

/-- A linear position in the doubled padded fiber, in the tape order used by
the local transform, with the active half first. -/
def SlotQuery.atPosition (q : SlotQuery) (bits : ℕ) (i : Fin (2 * 2^q.width)) : SlotQuery :=
  { q with
    bits := bits
    half := decide (2^q.width < i.val+1)
    rank := ⟨i.val % 2^q.width,Nat.mod_lt _ (Nat.two_pow_pos _)⟩ }

noncomputable def SlotQuery.coefficient (q : SlotQuery) : ℂ :=
  adjointValue q.adj (slotPhase q.axis q.width q.tag q.arg q.address)

theorem SlotQuery.coefficient_unit (q : SlotQuery) : ‖q.coefficient‖ = 1 := by
  unfold SlotQuery.coefficient adjointValue
  cases h : q.adj <;> simpa using slotPhase_unit q.axis q.width q.tag q.arg q.address

private theorem figureAcross {J : Type} {s : Regime J} {n f : J → ℕ}
    (N : Realizes s n) (F : Figure s f) :
    Figure (signal n N) (fun t : Across n ↦ f t.1) := by
  obtain ⟨w,h,e⟩ := F
  exact ⟨w ∘ at_ n,sendRoof n N _ h,fun t ↦ e t.1⟩

theorem classifiedBool {J : Type} {s : Regime J} {p : J → Prop}
    [DecidablePred p] (C : Classified s p) : s.Has (fun j ↦ decide (p j)) := by
  obtain ⟨f,h,e⟩ := C
  convert h using 2
  rename_i j
  cases hf : f j <;> simp [e j,hf]

attribute [local irreducible] componentBits fractionBits guardedK Prepared

/-- Every coefficient of a physical phase slot is emitted from the same
setup program. The resulting list already has the tape layout, precision
and error bound required by the global tensor-prefix scan. -/
theorem prepareSlotGuardedRow {J : Type} {s : Regime J} {q : J → SlotQuery} {k : J → ℕ}
    (K : Realizes s k) (H : SlotQuery.Available s q)
    (R : Realizes s (fun j ↦ 2 ^ (q j).width)) :
    ∃ v : (j : J) → Fin (2 * 2^(q j).width) → Record (guardedK (k j)),
      s.Has (fun j ↦ List.ofFn fun i ↦ mark (k := componentBits (guardedK (k j))) (v j i)) ∧
      ∀ (j : J) (i : Fin (2 * 2^(q j).width)),
        ‖FixedPoint.value (guardedK (k j)) (v j i) - ((q j).atPosition (70*guardedK (k j)+3) i).coefficient‖
          ≤ 1/(2:ℝ)^(70*guardedK (k j)) := by
  let n j := 2 * 2^(q j).width
  have N : Realizes s n := (Realizes.fix 2).times R
  let b j := 70 * guardedK (k j) + 3
  have G : Realizes s (fun j ↦ guardedK (k j)) := by
    unfold guardedK
    exact ((Realizes.fix 2).times K).plus (.fix 1)
  have B : Realizes s b := ((Realizes.fix 70).times G).plus (.fix 3)
  let a (t : Across n) := (q t.1).atPosition (b t.1) t.2
  let S := signal n N
  have U : Figure S (fun t : Across n ↦ t.2.val) := Figure.of_spoken (floor_ n N)
  have D := Figure.of_spoken (landing n N _ R)
  have hq : SlotQuery.Available S a := {
    axis := landing n N _ H.axis
    width := landing n N _ H.width
    bits := landing n N _ B
    arg := landing n N _ H.arg
    tag := figureAcross N H.tag
    rank := U.modded D
    half := classifiedBool (D.compare_ (U.added (.natural 1)))
    adj := sendRoof n N _ H.adj }
  exact Prepared.guardedRow K N (fun j i ↦ ((q j).atPosition (b j) i).coefficient)
    (fun j i ↦ SlotQuery.coefficient_unit _) (prepareSlot hq)

end PhaseTable

end NearSquareRoot
end Computability
end OAI
