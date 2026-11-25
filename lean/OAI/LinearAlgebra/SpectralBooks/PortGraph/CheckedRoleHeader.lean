import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementUniform
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementChoices
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PatchRoleHeader

/-! # Encoding roles from the checked record catalogue -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace PortGraph.ReplacementChoices

open UniformDecorations ReplacementTemplate
open scoped Classical

/-- A fixed exponent bounds all old record shapes and the full certificates
on their vertices. It depends only on the maximum patch size. -/
def recordExponent (K : ℕ) := Nat.clog 2 (Fintype.card (PatchShape K)) +
    80 * 5^(2*K+2) * K

theorem card_checked_le {n : ℕ} (hn : 0 < n) (K : ℕ) (ε : ℝ) :
    Fintype.card (Checked n K ε) ≤ (2*n)^recordExponent K :=
  (Fintype.card_subtype_le _).trans (PatchRecord.full_card_le hn K)

/-- The same header alphabet accommodates every checked record, list entry,
and numbered tree vertex in a round, with one copy of the width `w`. -/
theorem checked_role_card {n K w c b : ℕ} {ε : ℝ} (hn : 0 < n) (L : Checked n K ε → ℕ)
    (hL : ∀ r, L r ≤ 2^(w+c)) (T : ((r : Checked n K ε) × Fin (L r)) → ReplacementTemplate.{0,0,0})
    [∀ j, Fintype (T j).Role] (hroles : ∀ j, Fintype.card (T j).Role ≤ b) :
    Fintype.card (RoleLabel T) ≤ 2^(w + (recordExponent K+c+b)*Nat.clog 2 (2*n)) :=
  card_replacement_roles hn (card_checked_le hn K ε) L hL _ hroles

end PortGraph.ReplacementChoices

end

end SpectralBooks
end LinearAlgebra
end OAI
