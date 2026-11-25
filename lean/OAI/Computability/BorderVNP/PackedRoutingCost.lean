import OAI.Computability.BorderVNP.PackedRoutingPrivateViews

/-! # Sparse public cost of all routing, placement, and owned-cell output wires

The three batched table operations and their sorts use the sparse physical row
capacities. The extra cost is linear in that capacity, times a cubic polynomial
in the pointer and word lengths. No bit-expanded cable directory is scanned.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open CellAddressCircuit CellAddressViews GeometryFrameEncoding VPVNP.VerifierNetwork
open scoped Classical

variable {s m n C d k w J A o L R : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

private theorem lookup_poly {x y z : ℕ} (hx : x ≤ L) (hy : y ≤ L) (hz : z ≤ L) :
    ((x+1+y)+((y+z)+1+x)+z^2*(24*((y+z)+1+x)+1)+y*(60*x+16*y+33)+z^2*(24*(y+z)+1)) ≤
      500*(L+1)^3 := by
  calc
    _ ≤ ((L+1+L)+((L+L)+1+L)+L^2*(24*((L+L)+1+L)+1)+L*(60*L+16*L+33)+L^2*(24*(L+L)+1)) := by gcongr
    _ ≤ _ := by nlinarith only [Nat.zero_le (L^3),Nat.zero_le (L^2),Nat.zero_le L]

private theorem sort_poly {x y z : ℕ} (hx : x ≤ L) (hy : y ≤ L) (hz : z ≤ L) :
    ((x+y)*(30*x+8)+((y+z)+1+x)+z^2*(24*((y+z)+1+x)+1)+y*(60*x+40*y+63)+z^2*(24*(y+z)+1)) ≤
      500*(L+1)^3 := by
  calc
    _ ≤ ((L+L)*(30*L+8)+((L+L)+1+L)+L^2*(24*((L+L)+1+L)+1)+L*(60*L+40*L+63)+L^2*(24*(L+L)+1)) := by gcongr
    _ ≤ _ := by nlinarith only [Nat.zero_le (L^3),Nat.zero_le (L^2),Nat.zero_le L]

private theorem padded {x : ℕ} (h : x ≤ R) (pos : 0 < R) : 2^(Nat.clog 2 x) ≤ 2*R := by
  by_cases hx : x=0
  · subst x; simp; omega
  · exact (TeamSorting.padding_lt_twice (Nat.pos_of_ne_zero hx)).le.trans (by omega)

set_option maxHeartbeats 500000 in
/-- Explicit joint bound for the real output frame, including extra original-box
and cell marker rows. R bounds the sum of static site, edge, cell, port and original
row capacities; L bounds the largest word width and the binary sorting logarithm. -/
theorem full_size_le (hk : k ≤ w) (old : Fin J → Fin s) (ports : Fin A → Fin n)
    (rest : Frame σ (Outputs o w)) (rows : 1+CellAddressCircuit.count s m n C+J+A ≤ R)
    (widths : d ≤ L ∧ k ≤ L ∧ w ≤ L ∧ Nat.clog 2 R ≤ L) :
    (full F hk old ports (withPrivateViews F old rest)).size ≤ rest.size + 15000*R*(L+1)^3 := by
  obtain ⟨hd,hk',hw,log⟩ := widths
  let unit := R*(L+1)^3
  have baseRows : 1+(((m+C)+(s+C))+(((m+m)+n)+C))+J+A ≤ R := rows
  have p : 0 < R := by omega
  have lrows : s+(m+m+n) ≤ R := by omega
  have arows : CellAddressCircuit.count s m n C ≤ R := by omega
  have qrows : C+(m+m+n) ≤ R := by omega
  have logBound (x : ℕ) (hx : x ≤ R) := (Nat.clog_mono_right 2 hx).trans log
  have label : labelBound s m n d k ≤ 1000*unit := by
    unfold labelBound
    exact (Nat.mul_le_mul (padded lrows p) (lookup_poly hd hk' (logBound _ lrows))).trans (by dsimp [unit]; ring_nf; rfl)
  have address : gateBound s m n C d k w ≤ 2001*unit := by
    have part := Nat.mul_le_mul (padded arows p) (sort_poly hk' hw (logBound _ arows))
    have part' : 2*R*(500*(L+1)^3) = 1000*unit := by unfold unit; ring
    have up : 1 ≤ unit := Nat.mul_pos p (by positivity : 0 < (L+1)^3)
    dsimp only [gateBound]
    rw [part'] at part
    omega
  have source := CellAddressViews.frame_size F
  simp only [View,End,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at source
  have viewRows : m+m+n+(s+3*C) ≤ R := by omega
  have poly₁ : w*(60*k+16) ≤ 100*(L+1)^3 :=
    (Nat.mul_le_mul hw (by omega : 60*k+16 ≤ 60*L+16)).trans (by nlinarith only [Nat.zero_le (L^3),Nat.zero_le (L^2),Nat.zero_le L])
  have viewCost := Nat.mul_le_mul viewRows poly₁
  have scale (c : ℕ) : R*(c*(L+1)^3) = c*unit := by unfold unit; ring
  rw [scale] at viewCost
  have src : (CellAddressViews.frame F).size ≤ 3101*unit := by
    rw [Nat.mul_assoc (m+m+n+(s+3*C))] at source
    omega
  have lab := (labels_size F).trans label
  have off := SuppliedOffsets.frame_size F
  have qt := Nat.mul_le_mul (padded qrows p) (lookup_poly hk' hw (logBound _ qrows))
  have qr : 2*R*(500*(L+1)^3) = 1000*unit := by unfold unit; ring
  rw [qr] at qt
  have sub : w*(100*(w+1)) ≤ 100*(L+1)^3 :=
    (Nat.mul_le_mul hw (by omega : 100*(w+1) ≤ 100*(L+1))).trans (by nlinarith only [Nat.zero_le (L^3),Nat.zero_le (L^2),Nat.zero_le L])
  have qc := Nat.mul_le_mul (show m+m+n+C ≤ R by omega) sub
  rw [scale] at qc
  have offsets : (SuppliedOffsets.frame F).size ≤ 5201*unit := by
    dsimp only at off
    rw [Nat.mul_assoc (m+m+n+C)] at off
    omega
  have ft := tail_size F hk old ports
  have tw : count m C J A ≤ 2*R := by unfold count; omega
  have oneWord : w ≤ (L+1)^3 := by nlinarith only [hw,Nat.zero_le (L^2),Nat.zero_le (L^3)]
  have bits := Nat.mul_le_mul tw oneWord
  have two : 2*R*(L+1)^3 = 2*unit := by unfold unit; ring
  rw [two] at bits
  have cb := CableTriples.frame_size F hk (le_refl w)
  have cm : m*3 ≤ R := by omega
  have per : w*(30*k+30*w+11) ≤ 100*(L+1)^3 :=
    (Nat.mul_le_mul hw (by omega : 30*k+30*w+11 ≤ 60*L+11)).trans (by nlinarith only [Nat.zero_le (L^3),Nat.zero_le (L^2),Nat.zero_le L])
  have cc := Nat.mul_le_mul cm per
  rw [scale] at cc
  rw [Nat.mul_assoc (m*3)] at cb
  simp only [full,withPrivateViews,GeometryOutput.prepend_size,privateViews_size]
  rw [show 15000*R*(L+1)^3 = 15000*unit by unfold unit; ring]
  omega

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
