import OAI.Computability.BorderVNP.PackedCellAddressPhysical

/-! # Public prefix words are the compact absolute bank addresses -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddressPhysical

open Crossing CellAddresses CellAddressCircuit ParseBatchSort Function
open private row_key_width from OAI.Computability.BorderVNP.PackedCellAddressPhysical
open scoped Classical

variable {D s m n C d k w : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ) (c : Fin C)

omit [Fintype P] in
private theorem guessOrd (e : N.InsideEdge cell c) :
    (order s m n C (localRow N cell siteID edgeID portID c (.inl (.inl e)))).val = (edgeID e.val).val := rfl

omit [Fintype P] in
private theorem siteOrd (v : {v : N.Site // cell v = c}) :
    (order s m n C (localRow N cell siteID edgeID portID c (.inl (.inr v)))).val =
      (m+C)+(siteID v.val).val := rfl

omit [Fintype P] in
private theorem suppliedOrd (u : Supplied N cell c) :
    (order s m n C (localRow N cell siteID edgeID portID c (.inr u))).val =
      ((m+C)+(s+C)) + suppliedRow N cell c edgeID portID u := by cases u <;> rfl

/-- Canonical address of a private wire, site staging slab, or supplied word. -/
noncomputable def absolute : Local N cell c → ℕ :=
  Sum.elim (Sum.elim (CellSlabs.start (guessedRow N cell c edgeID) (fun e => N.width e.val))
    (siteBase N cell c siteID aux))
    (fun u => externalBase N cell c aux + CellSlabs.start (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) u)

private theorem prefix_eq (r : Row s m n C) :
    (∑ u : Local N cell c, if order s m n C (localRow N cell siteID edgeID portID c u) < order s m n C r
      then localWidth N cell aux c u else 0) =
      (∑ e : N.InsideEdge cell c, if (edgeID e.val).val < (order s m n C r).val then N.width e.val else 0) +
      (∑ v : {v : N.Site // cell v = c}, if (m+C)+(siteID v.val).val < (order s m n C r).val then aux v.val else 0) +
      (∑ u : Supplied N cell c, if ((m+C)+(s+C))+suppliedRow N cell c edgeID portID u < (order s m n C r).val
        then suppliedWidth N cell c u else 0) := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [Fin.lt_def,guessOrd,siteOrd,suppliedOrd,localWidth,Sum.elim_inl,Sum.elim_inr]

private theorem prior (r : Row s m n C) {x : σ → Bool} (h : Represents N cell aux siteID edgeID portID F x)
    (fit : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)
    (hr : (data F x).address (fun v => (F.cells v).val) r = (F.cells c).val) :
    value (fun j => (frame F).eval x (r,j)) =
      (∑ e : N.InsideEdge cell c, if (edgeID e.val).val < (order s m n C r).val then N.width e.val else 0) +
      (∑ v : {v : N.Site // cell v = c}, if (m+C)+(siteID v.val).val < (order s m n C r).val then aux v.val else 0) +
      (∑ u : Supplied N cell c, if ((m+C)+(s+C))+suppliedRow N cell c edgeID portID u < (order s m n C r).val
        then suppliedWidth N cell c u else 0) :=
  (physical_prefix N cell aux siteID edgeID portID F c h fit r hr).trans (prefix_eq N cell aux siteID edgeID portID c r)

omit [Fintype P] in
private theorem supplyBound (u : Supplied N cell c) : suppliedRow N cell c edgeID portID u < (m+m)+n := by
  unfold suppliedRow
  exact Fin.isLt _

variable {x : σ → Bool} (h : Represents N cell aux siteID edgeID portID F x)
variable (fit : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)

include h fit in
/-- Every live physical wire, site and port receives its exact absolute bank start. -/
theorem frame_absolute (u : Local N cell c) :
    value (fun j => (frame F).eval x (localRow N cell siteID edgeID portID c u,j)) =
      absolute N cell aux siteID edgeID portID c u := by
  rw [prior N cell aux siteID edgeID portID F c _ h fit (row_key_width N cell aux siteID edgeID portID F c h u).1]
  rcases u with (e|v)|p
  · rw [guessOrd]
    have noSite (v : {v : N.Site // cell v = c}) : ¬(m+C)+(siteID v.val).val < (edgeID e.val).val := by
      have := (edgeID e.val).isLt; omega
    have noSup (u : Supplied N cell c) : ¬((m+C)+(s+C))+suppliedRow N cell c edgeID portID u < (edgeID e.val).val := by
      have := (edgeID e.val).isLt; omega
    simp only [noSite,noSup,ite_false,Finset.sum_const_zero,add_zero]
    rfl
  · rw [siteOrd]
    have old (e : N.InsideEdge cell c) : (edgeID e.val).val < (m+C)+(siteID v.val).val := by have := (edgeID e.val).isLt; omega
    have noSup (u : Supplied N cell c) : ¬((m+C)+(s+C))+suppliedRow N cell c edgeID portID u < (m+C)+(siteID v.val).val := by
      have := (siteID v.val).isLt; omega
    simp only [old,ite_true,noSup,ite_false,Finset.sum_const_zero,add_zero,Nat.add_lt_add_iff_left]
    change _ = guessedSize N cell c + _
    congr 1
    · exact congrArg (fun t => Finset.sum t _) (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
    · unfold CellSlabs.start
      apply Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
      intro t _
      rfl
  · rw [suppliedOrd]
    have old (e : N.InsideEdge cell c) : (edgeID e.val).val < ((m+C)+(s+C))+suppliedRow N cell c edgeID portID p := by
      have := (edgeID e.val).isLt; omega
    have vs (v : {v : N.Site // cell v = c}) : (m+C)+(siteID v.val).val < ((m+C)+(s+C))+suppliedRow N cell c edgeID portID p := by
      have := (siteID v.val).isLt; omega
    simp only [old,vs,ite_true,Nat.add_lt_add_iff_left,absolute,Sum.elim_inr,externalBase,CellSlabs.start,siteSize,guessedSize]
    congr 3 <;> exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

/-- Marker rows after the internal wires, after the private staging words, and after the supplied ports. -/
def marker : Fin 3 → Fin C → Row s m n C
  | 0, c => .inl (.inl (.inr c))
  | 1, c => .inl (.inr (.inr c))
  | 2, c => .inr (.inr c)

include h fit in
/-- The three returned region ends count actual live bits with no unused padding in the cell. -/
theorem frame_marker (j : Fin 3) :
    value (fun b => (frame F).eval x (marker j c,b)) =
      guessedSize N cell c + (if j = 0 then 0 else siteSize N cell c aux) +
        (if j = 2 then suppliedSize N cell c else 0) := by
  have hm : (data F x).address (fun v => (F.cells v).val) (marker (s := s) (m := m) (n := n) j c) = (F.cells c).val := by
    fin_cases j <;> rfl
  rw [prior N cell aux siteID edgeID portID F c _ h fit hm]
  fin_cases j
  · change (∑ e : N.InsideEdge cell c, if (edgeID e.val).val < m+c.val then N.width e.val else 0) +
      (∑ v : {v : N.Site // cell v = c}, if (m+C)+(siteID v.val).val < m+c.val then aux v.val else 0) +
      (∑ u : Supplied N cell c, if ((m+C)+(s+C))+suppliedRow N cell c edgeID portID u < m+c.val
        then suppliedWidth N cell c u else 0) = _
    have old (e : N.InsideEdge cell c) : (edgeID e.val).val < m+c.val := by have := (edgeID e.val).isLt; omega
    have vs (v : {v : N.Site // cell v = c}) : ¬(m+C)+(siteID v.val).val < m+c.val := by have := c.isLt; omega
    have us (u : Supplied N cell c) : ¬((m+C)+(s+C))+suppliedRow N cell c edgeID portID u < m+c.val := by have := c.isLt; omega
    simp [old,vs,us,guessedSize]
    congr 6; exact Subsingleton.elim _ _
  · let lim := (m+C)+(s+c.val)
    change (∑ e : N.InsideEdge cell c, if (edgeID e.val).val < lim then N.width e.val else 0) +
      (∑ v : {v : N.Site // cell v = c}, if (m+C)+(siteID v.val).val < lim then aux v.val else 0) +
      (∑ u : Supplied N cell c, if ((m+C)+(s+C))+suppliedRow N cell c edgeID portID u < lim
        then suppliedWidth N cell c u else 0) = _
    have old (e : N.InsideEdge cell c) : (edgeID e.val).val < lim := by dsimp [lim]; have := (edgeID e.val).isLt; omega
    have vs (v : {v : N.Site // cell v = c}) : (m+C)+(siteID v.val).val < lim := by dsimp [lim]; have := (siteID v.val).isLt; omega
    have us (u : Supplied N cell c) : ¬((m+C)+(s+C))+suppliedRow N cell c edgeID portID u < lim := by dsimp [lim]; have := c.isLt; omega
    simp [old,vs,us,guessedSize,siteSize]
    congr 6 <;> exact Subsingleton.elim _ _
  · let lim := ((m+C)+(s+C))+(((m+m)+n)+c.val)
    change (∑ e : N.InsideEdge cell c, if (edgeID e.val).val < lim then N.width e.val else 0) +
      (∑ v : {v : N.Site // cell v = c}, if (m+C)+(siteID v.val).val < lim then aux v.val else 0) +
      (∑ u : Supplied N cell c, if ((m+C)+(s+C))+suppliedRow N cell c edgeID portID u < lim
        then suppliedWidth N cell c u else 0) = _
    have old (e : N.InsideEdge cell c) : (edgeID e.val).val < lim := by dsimp [lim]; have := (edgeID e.val).isLt; omega
    have vs (v : {v : N.Site // cell v = c}) : (m+C)+(siteID v.val).val < lim := by dsimp [lim]; have := (siteID v.val).isLt; omega
    have us (u : Supplied N cell c) : ((m+C)+(s+C))+suppliedRow N cell c edgeID portID u < lim := by
      dsimp [lim]; have := supplyBound N cell edgeID portID c u; omega
    simp [old,vs,us,guessedSize,siteSize,suppliedSize]
    congr 6 <;> exact Subsingleton.elim _ _

end Packing.CellAddressPhysical

end BorderVNP
end Computability
end OAI
