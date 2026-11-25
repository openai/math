import OAI.Hierarchy.DescentFallbackShapeTable

namespace OAI
/-! # Numbering the shape and neighbor fields of a shared rank book -/
namespace Hierarchy.DescentSharedBookScan
open DescentFallbackShapeTable
variable {a Y Δ H : ℕ}

abbrev Fields (a Y Δ : ℕ) := Fin (rows a Y) × Fin (Δ+1) × Fin (rows a Y)
def width (a Y Δ : ℕ) := rows a Y*((Δ+1)*rows a Y)
def fieldId (p : Fields a Y Δ) : Fin (width a Y Δ) := finProdFinEquiv (p.1,finProdFinEquiv p.2)
def absolute (v : Fin H) (p : Fields a Y Δ) : Fin (H*width a Y Δ) := finProdFinEquiv (v,fieldId p)

end Hierarchy.DescentSharedBookScan

end OAI
