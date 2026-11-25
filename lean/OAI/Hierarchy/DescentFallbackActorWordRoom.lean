import OAI.Hierarchy.DescentFallbackShapeTable

namespace OAI
/-! # Word width for the sparse dyadic endpoint names used by the actor classifier -/
namespace Hierarchy.DescentFallbackShapeTable
open DescentContacts DescentBaseProfile DescentFallbackLeafScan
open scoped Classical
noncomputable section

private theorem touching_id {d e i k s j : ℕ} (id : i < 2^k) (gap : e-d ≤ s)
    (member : j∈touching d e i) : j < 2^(k+s) := by
  unfold touching at member
  split at member
  · obtain ⟨v,inside,rfl⟩:=Finset.mem_image.mp member
    have hi:=Finset.mem_range.mp inside
    calc
      i*2^(e-d)+v < (i+1)*2^(e-d) := by rw [Nat.succ_mul];omega
      _ ≤ 2^k*2^s := Nat.mul_le_mul id (Nat.pow_le_pow_right (by decide) gap)
      _ = _ := (pow_add ..).symm
  · have eqn:=Finset.mem_singleton.mp member
    rw [eqn]
    exact ((Nat.div_le_self ..).trans_lt id).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right k s))

private theorem possible_id {d i up down k : ℕ} {j : ℕ×ℕ} (dFit : d ≤ k) (iFit : i < 2^k)
    (member : j∈possible d i up down) : j.1 ≤ k+down ∧ j.2 < 2^(k+down) := by
  rcases Finset.mem_union.mp member with primary|child
  · obtain ⟨s,_,rfl⟩:=Finset.mem_image.mp primary
    exact ⟨(Nat.sub_le ..).trans (dFit.trans (Nat.le_add_right ..)),
      ((Nat.div_le_self ..).trans_lt iFit).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))⟩
  · obtain ⟨s,hr,cell⟩:=Finset.mem_biUnion.mp child
    have span : s ≤ down:=Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    obtain ⟨j,inside,rfl⟩:=Finset.mem_image.mp cell
    exact ⟨Nat.add_le_add dFit span,touching_id iFit (by omega : d+s-d ≤ down) inside⟩

private theorem directory_id {Y k D g f : ℕ} {src z : Endpoint Y} {side : Bool}
    (srcId : src.1.2 < 2^src.1.1) (depth : src.1.1 ≤ k)
    (inside : z∈localShape k D g f src side) :
    z.1.1 ≤ k+max D g ∧ z.1.2 < 2^(k+max D g) := by
  have lo:=srcId.trans_le (Nat.pow_le_pow_right (by decide) depth)
  have weaken {w : ℕ} (span : w ≤ max D g) (x : ℕ×ℕ)
      (h : x.1 ≤ k+w ∧ x.2 < 2^(k+w)) : x.1 ≤ k+max D g ∧ x.2 < 2^(k+max D g) :=
    ⟨h.1.trans (Nat.add_le_add_left span k),h.2.trans_le (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left span k))⟩
  unfold localShape at inside
  split at inside
  · cases side with
    | false =>
      change z∈terminals Y (possible src.1.1 src.1.2 D D) at inside
      obtain ⟨⟨r,j⟩,occ,rfl⟩:=Finset.mem_image.mp inside
      exact weaken (Nat.le_max_left ..) r (possible_id depth lo (Finset.mem_product.mp occ).1)
    | true =>
      change z∈(if k-g ≤ src.1.1+D then
        (touching src.1.1 (k-g) src.1.2).image (fun j=>((k-g,j),none)) else ∅) at inside
      split at inside
      · rename_i h
        obtain ⟨j,occ,rfl⟩:=Finset.mem_image.mp inside
        exact ⟨by dsimp;omega,touching_id lo (by omega : k-g-src.1.1 ≤ max D g) occ⟩
      · exact (Finset.notMem_empty _ inside).elim
  · obtain ⟨⟨r,j⟩,occ,rfl⟩:=Finset.mem_image.mp inside
    exact weaken ((Nat.sub_le g f).trans (Nat.le_max_right ..)) r
      (possible_id (Nat.sub_le k g) lo (Finset.mem_product.mp occ).1)

private theorem pair_bits {a b s : ℕ} (x : a < 2^s) (y : b < 2^s) :
    Nat.pair a b < 2^(s+s) :=
  (Nat.pair_lt_max_add_one_sq _ _).trans_le (by
    rw [pow_two,pow_add]
    exact Nat.mul_le_mul (by omega) (by omega))


theorem actor_shape_rows (k n : ℕ) : 2*rows k (2^n) ≤ 2^(2*k+n+2) := by
  have hr : k+1 ≤ 2^k := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hn : 2^n+1 ≤ 2*2^n := by have h:=Nat.two_pow_pos n; omega
  calc
    2*rows k (2^n) ≤ 2*((2^k*2^k)*(2*2^n)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul_right _ hr) hn)
    _ = 2^(2*k+n+2) := by rw [show 2*k=k+k by omega];simp only [pow_add];ring

def actorWordBits (k D g n : ℕ) := 4*(k+max D g+n+1)+1

theorem actor_shape_fits {n k D g f w : ℕ} (budget : actorWordBits k D g n ≤ w)
    (src : Endpoint (2^n)) (srcId : src.1.2 < 2^src.1.1) (depth : src.1.1 ≤ k)
    (side : Bool) (z : Endpoint (2^n)) (inside : z∈localShape k D g f src side) :
    shapeNumber z+1 < 2^w := by
  let s:=k+max D g+n+1
  obtain ⟨row,col⟩:=directory_id srcId depth inside
  have dr : z.1.1 < 2^s := (show z.1.1 ≤ s by dsimp [s];omega).trans_lt Nat.lt_two_pow_self
  have dc : z.1.2 < 2^s := col.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [s];omega))
  have opt : DescentRosterOrder.optionDigit z.2 < 2^(s+s) := by
    have kr : 2^n < 2^(s+s) := Nat.pow_lt_pow_right (by decide : 1<2) (by dsimp [s];omega)
    exact (option_fit z.2).trans_le kr
  have id := pair_bits (pair_bits dr dc) opt
  change shapeNumber z < 2^((s+s)+(s+s)) at id
  have extra : 2^((s+s)+(s+s)) < 2^w := Nat.pow_lt_pow_right (by decide : 1<2) (by
    change 4*s+1 ≤ w at budget;omega)
  exact (Nat.succ_le_of_lt id).trans_lt extra

/-- The encoded endpoint itself fits the same word that holds its neighbor entries. -/
theorem actor_endpoint_fits {n k D g w : ℕ} (budget : actorWordBits k D g n ≤ w)
    (src : Endpoint (2^n)) (row : src.1.1 ≤ k) (col : src.1.2 < 2^src.1.1) :
    shapeNumber src < 2^w := by
  let s:=k+max D g+n+1
  have dr : src.1.1 < 2^s := (show src.1.1 ≤ s by dsimp [s];omega).trans_lt Nat.lt_two_pow_self
  have dc : src.1.2 < 2^s := col.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [s];omega))
  have opt : DescentRosterOrder.optionDigit src.2 < 2^(s+s) := (option_fit src.2).trans_le
    (Nat.pow_lt_pow_right (by decide : 1<2) (show n < s+s by dsimp [s];omega))
  have id:=pair_bits (pair_bits dr dc) opt
  change shapeNumber src < 2^((s+s)+(s+s)) at id
  exact id.trans_le (Nat.pow_le_pow_right (by decide) (by change 4*s+1 ≤ w at budget;omega))

end
end Hierarchy.DescentFallbackShapeTable

end OAI
