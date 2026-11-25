import OAI.Hierarchy.DescentNodeLocalEnumeration

namespace OAI
/-! # The finite bounds of the original local node order -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

def maxNodes (B : BitDescription W) := Finset.univ.sup (fun v=>Fintype.card (B.recipe v).Node)

def bounded (B : BitDescription W) (o : Local B) (v : W.graph.Site) :
    (B.recipe v).Node ↪ Fin (maxNodes B) :=
  (o v).toEmbedding.trans (Fin.castLEEmb
    (Finset.le_sup (f := fun u => Fintype.card (B.recipe u).Node) (Finset.mem_univ v)))

theorem maxNodes_le (B : BitDescription W) {K : ℕ} (upper : ∀v,Fintype.card (B.recipe v).Node≤K) :
    maxNodes B≤K := Finset.sup_le (fun v _=>upper v)

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
