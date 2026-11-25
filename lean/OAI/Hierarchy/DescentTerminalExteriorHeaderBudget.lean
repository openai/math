import OAI.Hierarchy.DescentTerminalExteriorHeaders

namespace OAI
/-! # The active exterior header rows fit the same purchased array as the private headers -/
namespace Hierarchy.DescentTerminalExteriorHeaders
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts DescentTerminalCableOrder
open DescentTerminalHeaderGroups DescentTerminalRecipeRows Computability.VPVNP.RAMSerialization
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
variable {D S p q : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits) (home : N.Site→Fin S)
    (native : N.Edge ↪ Fin (Fintype.card N.Edge)) (external : P ↪ ℕ)
    (nodes : N.Site ↪ ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
local notation "L" => order N home native p external nodes ops

theorem site_port_rows (i : Fin S) :
    (siteRows (p:=p) (q:=q) N home native external nodes ops i).length ≤ ((L).site i).portRows q := by
  classical
  by_cases h:Live (p:=p) N home native external nodes ops i
  · let g : Order.Group L i:=⟨none,h⟩
    have single : poolBatchCount (Fintype.card (Order.At L i g)) q≤
        ∑a:Order.Group L i,poolBatchCount (Fintype.card (Order.At L i a)) q :=
      Finset.single_le_sum
        (f := fun a : Order.Group L i => poolBatchCount (Fintype.card (Order.At L i a)) q)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
    have allRows : ((L).site i).portRows q=∑a:Order.Group L i,poolBatchCount (Fintype.card (Order.At L i a)) q :=
      (Order.groups L i).symm.sum_comp (fun a=>poolBatchCount (Fintype.card (Order.At L i a)) q)
    simpa only [siteRows,dite_eq_left h,block,chunkRows_length,allRows] using single
  · simp [siteRows,h]

theorem paid_length {W:ℕ} (wp:0<W) :
    (stream (p:=p) (q:=q) N home native external nodes ops S).length≤
      DescentTerminalBinPack.purchased W (counts (q:=q) (L).site) := by
  classical
  let count (i:ℕ):=if h:i<S then (siteRows (p:=p) (q:=q) N home native external nodes ops ⟨i,h⟩).length else 0
  have «prefix» (k:ℕ) : (stream (p:=p) (q:=q) N home native external nodes ops k).length=∑i∈Finset.range k,count i := by
    induction k with
    | zero=>simp [stream]
    | succ k ih=>
      by_cases h:k<S <;> simp [stream,ih,count,h,Finset.sum_range_succ]
  have paid:=Fintype.card_le_of_injective _ (DescentTerminalBinPack.rowIndex wp
    (counts (q:=q) (L).site)).injective
  simp only [Fintype.card_sigma,Fintype.card_fin] at paid
  rw [«prefix»,←Fin.sum_univ_eq_sum_range count S]
  apply le_trans _ paid
  apply Finset.sum_le_sum
  intro i _
  have h₁ := site_port_rows (p:=p) (q:=q) N home native external nodes ops i
  have h₂ : ((L).site i).portRows q≤((L).site i).rows q := by unfold Site.rows;omega
  simpa only [count,dite_eq_left i.isLt] using h₁.trans h₂


end
end Hierarchy.DescentTerminalExteriorHeaders

end OAI
