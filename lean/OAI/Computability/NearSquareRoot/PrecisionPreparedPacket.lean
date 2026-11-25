import OAI.Computability.NearSquareRoot.PrecisionPreparedGrid
import OAI.Computability.NearSquareRoot.PrecisionGridTableInput
import OAI.Computability.NearSquareRoot.PrecisionGridAddressLookup

/-! # Preparing every local phase row and both unary rulers for a synchronized pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Strip Staff Dusk FixedPoint PhaseStream

attribute [local irreducible] componentBits fractionBits guardedK Prepared

/-- The setup language enumerates every row of a phase slot on its polynomial
local domains, then puts the rows in decreasing place value. The returned tree
is the input format read directly by the physical prefix generator's adapter. -/
theorem prepareGuardedPacket {J : Type} {s : Regime J} {d k : J → ℕ}
    (D : Realizes s d) (K : Realizes s k) (n : Across d → ℕ) (N : Realizes (signal d D) n)
    (phase : (t : Across d) → Fin (n t) → ℂ) (unit : ∀ t i, ‖phase t i‖ = 1)
    (h : Prepared (signal n N) (fun i : Across n ↦ 70*guardedK (k i.1.1)+3)
      (fun i ↦ phase i.1 i.2)) :
    ∃ v : (j : J) → (i : Fin (d j)) → Fin (n ⟨j,i⟩) → Record (guardedK (k j)),
      s.Small (fun j ↦ phaseTablePacket (guardedK (k j)) (radixRows (v j))) ∧
      ∀ (j : J) (i : Fin (d j)) (x : Fin (n ⟨j,i⟩)),
        ‖FixedPoint.value (guardedK (k j)) (v j i x) - phase ⟨j,i⟩ x‖
          ≤ 1/(2:ℝ)^(70*guardedK (k j)) := by
  have K' := landing d D _ K
  obtain ⟨v, hv, err⟩ := Prepared.guardedRow (k := fun t : Across d ↦ k t.1) K' N phase unit h
  let v' (j : J) (i : Fin (d j)) := v ⟨j,i⟩
  have packed := harvest d D (fun j i ↦ List.ofFn fun x ↦
    mark (k := componentBits (guardedK (k j))) (v' j i x)) hv
  have G : Realizes s (fun j ↦ guardedK (k j)) := by
    unfold guardedK
    exact ((Realizes.fix 2).times K).plus (.fix 1)
  have F : Realizes s (fun j ↦ fractionBits (guardedK (k j))) := by
    unfold fractionBits
    exact ((Realizes.fix 70).times G).plus (.fix 1)
  have W : Realizes s (fun j ↦ componentBits (guardedK (k j))+1) := by
    unfold componentBits
    exact (((Realizes.fix 96).times G).plus (.fix 4)).plus (.fix 1)
  refine ⟨v', ?_, fun j i x ↦ err ⟨j,i⟩ x⟩
  have ready := (Regime.Has.pair F W).pair (packed.ez Easy.reverse)
  change s.Has (fun j ↦ rawPhasePacket (w := componentBits (guardedK (k j))) (fractionBits (guardedK (k j)))
    (radixRows (d := d j) (r := fun i ↦ n ⟨j,i⟩) (v' j)))
  simpa only [rawPhasePacket, radixRows, List.map_reverse, List.map_ofFn, Function.comp_def,
    Realizes, box] using ready

end PhaseTable

end NearSquareRoot
end Computability
end OAI
