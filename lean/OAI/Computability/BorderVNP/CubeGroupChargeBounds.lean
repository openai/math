import Mathlib.Data.Sym.Sym2.Order
import OAI.Computability.BorderVNP.CubeGroupRawExact
import OAI.Computability.BorderVNP.CubePhysicalGroupLoad
import OAI.Computability.BorderVNP.CubePhysicalScheduleBudget
import OAI.Computability.BorderVNP.CubeCableChoice

/-! # Total and per-group communication costs of the physical schedule

The two groups incident to a shared list each pay its full length. The incoming
data use the balanced-label counts. The original padded wires can contribute
to at most two groups.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Finset VPVNP VPVNP.MotifBase

variable {n d blocks K h : ℕ}

private theorem sum_sorted (v : Sym2 (Fin d) → ℕ) :
    (∑ s : Fin d, ∑ t : Fin d, if s ≤ t then v (Sym2.mk s t) else 0) = ∑ r, v r := by
  let sorted := fun p : Fin d × Fin d => p.1 ≤ p.2
  let value := fun p : Fin d × Fin d => v (Sym2.mk p.1 p.2)
  rw [← Fintype.sum_prod_type (fun p : Fin d × Fin d => if sorted p then value p else 0)]
  rw [← sum_filter, sum_subtype (p := sorted) (univ.filter sorted) (fun _ => by simp) value]
  exact Fintype.sum_equiv Sym2.sortEquiv.symm _ v fun _ => rfl

/-- Each reserved shared list is charged to its two distinct endpoint groups. -/
theorem sum_incidentWidth (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (D : LengthDeclaration n d) (hp : passesLengths b s select D) :
    (∑ u, incidentWidth blocks K h D u) =
      2*(cutWidth b s select (chosen b s select) +
        Fintype.card (Packet n d blocks)*MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h) := by
  let v (r : Sym2 (Fin d)) := D.2 r D.1 + rowSelectorBits n d blocks K h D.1 r
  let part (u t : Fin d) := if u ≤ t then v (Sym2.mk u t) else 0
  have split (u t : Fin d) : (if u = t then 0 else v (Sym2.mk u t)) = part u t + part t u := by
    rcases lt_trichotomy u t with hlt | rfl | hgt
    · simp [part,hlt.le,hlt.not_ge,hlt.ne]
    · have diag : (Sym2.mk u u).IsDiag := Sym2.mk_isDiag_iff.mpr rfl
      have hv : v (Sym2.mk u u) = 0 := by
        dsimp only [v]
        rw [hp.1,diagonal_row_width b s select D.1 _ diag,
          diagonal_row_selectors n d blocks K h D.1 _ diag,Nat.zero_add]
      simp [part,hv]
    · simp [part,hgt.le,hgt.not_ge,hgt.ne',show Sym2.mk t u = Sym2.mk u t from Sym2.eq_swap]
  have eq : (∑ u, ∑ t, part u t) = ∑ r, v r := sum_sorted v
  change (∑ u : Fin d, ∑ t, if u = t then 0 else v (Sym2.mk u t)) = _
  simp_rw [split, sum_add_distrib]
  rw [sum_comm (f := fun u t => part t u),eq,← two_mul]
  exact congrArg (2*·) (reserved_sum b s select D hp)

private theorem row_fiber_le {T : Type*} [Fintype T] (s : Fin d)
    (row : T → Sym2 (Fin d)) (w : T → ℕ) :
    (∑ t, ∑ a, if row a = Sym2.mk s t then w a else 0) ≤
      ∑ a, if s ∈ row a then w a else 0 := by
  rw [sum_comm]
  apply sum_le_sum
  intro a _
  by_cases found : ∃ t, row a = Sym2.mk s t
  · obtain ⟨u,hu⟩ := found
    have eq (t : Fin d) : Sym2.mk s u = Sym2.mk s t ↔ u = t :=
      (Sym2.mkEmbedding s).injective.eq_iff
    simp [hu,eq]
  · have miss (t : Fin d) : row a ≠ Sym2.mk s t := fun h => found ⟨t,h⟩
    simp [miss]

/-- The fixed packet format bounds the incident lists of each group by its raw
load times the largest local expansion factor. Singletons require one bit. -/
theorem incidentWidth_le_raw (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (D : LengthDeclaration n d) (pass : passesLengths b s select D) (u : Fin d)
    (M : ℕ) (hM : 1 ≤ M)
    (packet : h*s + MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h ≤ M*(2^n*(h*b))) :
    incidentWidth blocks K h D u ≤ M * groupRaw (blocks*(h*b)) D.1 u := by
  let sel := MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h
  let pr := fun p : Packet n d blocks => itemRow D.1 (.inl p : Item n d blocks (h*b))
  let sr := fun z : SingleSlot n d blocks (h*b) => itemRow D.1 (.inr z)
  let pw := fun p : Packet n d blocks => crossCount b s select (.inl p) D.1 + sel
  let sw := fun z : SingleSlot n d blocks (h*b) => crossCount b s select (.inr z) D.1
  have row (r : Sym2 (Fin d)) : D.2 r D.1 + rowSelectorBits n d blocks K h D.1 r =
      (∑ p, if pr p = r then pw p else 0) + (∑ z, if sr z = r then sw z else 0) := by
    rw [pass.1,subtotals,Fintype.sum_sum_type,rowSelectorBits,add_right_comm]
    apply congrArg (· + ∑ z, if sr z = r then sw z else 0)
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hrow : pr p = r
    · change (if pr p = r then _ else 0) + (if pr p = r then _ else 0) = _
      simp [hrow,pw,sel]
    · change (if pr p = r then _ else 0) + (if pr p = r then _ else 0) = _
      simp [hrow]
  have packetBound (p : Packet n d blocks) : pw p ≤ M*(2^n*(h*b)) := by
    have bound : crossCount b s select (.inl p) D.1 ≤ h*s := by
      rw [packet_crossCount]
      calc
        _ ≤ ∑ e, payload (onEdge s) (select p).2 e :=
          sum_le_sum fun _ _ => by split <;> omega
        _ = h*s := by unfold payload; rw [sum_comm]; simp [onEdge]
    exact (Nat.add_le_add_right bound sel).trans packet
  have singleBound (z : SingleSlot n d blocks (h*b)) : sw z ≤ M := (Bool.toNat_le _).trans hM
  calc
    incidentWidth blocks K h D u ≤ ∑ t, ((∑ p, if pr p = Sym2.mk u t then pw p else 0) +
        ∑ z, if sr z = Sym2.mk u t then sw z else 0) := by
      apply sum_le_sum
      intro t _
      by_cases hut : u = t
      · rw [ite_eq_left hut]; exact Nat.zero_le _
      · rw [ite_eq_right hut,row]
    _ ≤ (∑ p, if u ∈ pr p then pw p else 0) + (∑ z, if u ∈ sr z then sw z else 0) := by
      rw [sum_add_distrib]
      exact Nat.add_le_add (row_fiber_le u pr pw) (row_fiber_le u sr sw)
    _ ≤ M*((∑ p, if u ∈ pr p then 2^n*(h*b) else 0) + (∑ z, if u ∈ sr z then 1 else 0)) := by
      rw [Nat.mul_add,Finset.mul_sum,Finset.mul_sum]
      apply Nat.add_le_add
      · apply sum_le_sum
        intro p _
        by_cases hu : u ∈ pr p <;> simp [hu,packetBound]
      · apply sum_le_sum
        intro z _
        by_cases hu : u ∈ sr z <;> simp [hu,singleBound]
    _ = _ := congrArg (M*·) (item_raw_eq_groupRaw D.1 u)

variable {Cell A : Type*} [Fintype A]

/-- Each incoming datum is charged once, to its own receiving group. -/
theorem sum_incomingWidth (label : Cell → Label (n+1) d) (recv : A → Cell)
    (w : A → ℕ) (i : Fin (n+1)) : (∑ s, incomingWidth label recv w i s) = ∑ a, w a := by
  unfold incomingWidth
  rw [sum_comm]
  simp

/-- Balancing each complete label bounds all data in a symbol group by `4W/d`. -/
theorem incomingWidth_le [Fintype Cell] [DecidableEq Cell] (label : Cell → Label (n+1) d) (recv : A → Cell)
    (w : A → ℕ) (i : Fin (n+1)) (s : Fin d) (W : ℝ)
    (balanced : ∀ u, Balancing.load (Balancing.datum (fun b : Balancing.Bits w => recv b.1) u) label ≤
      4*W/(d^(n+1) : ℕ)) : (incomingWidth label recv w i s : ℝ) ≤ 4*W/d := by
  let labels := univ.filter fun u : Label (n+1) d => u i = s
  let bits := fun u : Label (n+1) d =>
    Balancing.load (Balancing.datum (fun b : Balancing.Bits w => recv b.1) u) label
  have bits_eq u : bits u = ∑ a, if label (recv a) = u then (w a : ℝ) else 0 :=
    datum_load_eq_widths label recv w u
  have eq : (incomingWidth label recv w i s : ℝ) = ∑ u ∈ labels, bits u := by
    simp only [bits_eq,incomingWidth,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    by_cases h : label (recv a) i = s <;> simp [labels,h]
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt s.isLt
  calc
    _ = ∑ u ∈ labels, bits u := eq
    _ ≤ ∑ _u ∈ labels, 4*W/(d^(n+1) : ℕ) := sum_le_sum fun u _ => balanced u
    _ = 4*W/d := by
      have card : labels.card = d^n := card_fixed_symbol i s
      simp only [sum_const,nsmul_eq_mul,card,Nat.cast_pow,pow_succ]
      field_simp
      push_cast
      ring

end Cube.Physical

end BorderVNP
end Computability
end OAI
