import OAI.ThreeFlat.Diagonal.FixedMotifTile

namespace OAI
/-! # Nonempty selectors and a uniform bit bound for a fixed base tile -/

namespace ThreeFlat.Diagonal
open LinearAlgebra.SpectralBooks
open scoped Classical BigOperators
namespace FixedMotifTile

variable {J E S F : Type} [Fintype J] [Fintype E] [Fintype S] [Field F]
    {D : PortGraph J E} {P : PortGraph J S} {w : E → ℕ} (T : FixedMotifTile D P w F)

/-- The zero boundary on a base tile has unit wiring, which forces an actual
selector in its restriction. This covers zero copy counts as well. -/
theorem hasLetter : Nonempty T.Alphabet := by
  by_contra absent
  let : IsEmpty T.Alphabet := ⟨fun a => absent ⟨a⟩⟩
  have h := T.identity (fun _ _ => 0)
  simp [PortGraph.wiring] at h

/-- A bound on a base piece, depending on that fixed library entry alone. -/
def bitCap : ℕ := ∑ a : T.Alphabet, ∑ e : S, T.output a e

theorem output_le_cap (a : T.Alphabet) (e : S) : T.output a e ≤ T.bitCap :=
  (Finset.single_le_sum (f:=T.output a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)).trans
    (Finset.single_le_sum (f:=fun b : T.Alphabet => ∑ s : S, T.output b s)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))

end FixedMotifTile
end ThreeFlat.Diagonal

end OAI
