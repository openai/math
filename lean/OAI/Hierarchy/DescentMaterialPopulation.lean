import OAI.Hierarchy.DescentMaterialTariffNumbers
import Mathlib.Algebra.Order.Floor.Div

namespace OAI
/-! # Physical row counts across the old, signed and regrouped pitches -/
namespace Hierarchy.DescentDatedAddressBook.MaterialProgram
open DescentSIMDLookup

private theorem wider {g m b : ℕ} (pos : 0< m) (block : 0<b) :
    chunks g (m*b)≤chunks g m := by
  have cover : g≤ m*chunks g m := ThreeFlat.Routing.CallPool.count_le_batches_mul g m pos
  exact (ceilDiv_le_iff_le_mul (Nat.mul_pos pos block)).2
    (cover.trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right m block)))

def population (H K G G' h oldUnit newUnit : ℕ) :=
  (1+2^(h/2)+2*(H+K))*h+4*(H+K)*(G+G')*(oldUnit+newUnit)

theorem scan_volume_paid (H K G G' h oldUnit newUnit blocks : ℕ)
    (p : 0<oldUnit) (q : 0<newUnit) (wide : 2*oldUnit≤h) (wide' : 2*newUnit≤h) (block : 0<blocks) :
    scanVolume H K G G' (lanes h oldUnit) (lanes h newUnit) blocks h*h≤
      11*population H K G G' h oldUnit newUnit := by
  let R:=population H K G G' h oldUnit newUnit
  let terms:=4*(H+K)*(G+G')*(oldUnit+newUnit)
  have base : (1+2^(h/2)+2*(H+K))*h≤R:=Nat.le_add_right ..
  have work : terms≤R:=Nat.le_add_left ..
  have unit : h≤R:=(Nat.le_mul_of_pos_left h (by positivity : 0<1+2^(h/2)+2*(H+K))).trans base
  have tab : 2^(h/2)*h≤R:=(Nat.mul_le_mul_right h (by omega : 2^(h/2)≤1+2^(h/2)+2*(H+K))).trans base
  have hostCount : H+K≤2*(H+K) := Nat.le_mul_of_pos_left _ (by decide)
  have host : (H+K)*h≤R :=
    (Nat.mul_le_mul_right h (hostCount.trans (Nat.le_add_left _ (1+2^(h/2))))).trans base
  have hs : H*h≤R:=(Nat.mul_le_mul_right h (Nat.le_add_right H K)).trans host
  have ks : K*h≤R:=(Nat.mul_le_mul_right h (Nat.le_add_left K H)).trans host
  have fill (h' g' u : ℕ) (ha : h'≤H+K) (ga : g'≤G+G') (ua : u≤oldUnit+newUnit)
      (pos : 0<u) (enough : 2*u≤h) : (h'*chunks g' (lanes h u))*h≤2*R := by
    have first: h'*h≤R:=(Nat.mul_le_mul_right h ha).trans host
    have second : 4*h'*g'*u≤R:=(Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 4 ha) ga) ua).trans work
    exact (volume h' g' h u pos enough).trans (by omega)
  have a:=fill H G oldUnit (by omega) (by omega) (by omega) p wide
  have b:=fill H G' newUnit (by omega) (by omega) (by omega) q wide'
  have c:=fill K G' newUnit (by omega) (by omega) (by omega) q wide'
  have d:=fill H G newUnit (by omega) (by omega) (by omega) q wide'
  have delta:=wider (g:=G) (m:=lanes h newUnit) (occupancy h newUnit q wide').1 block
  have last: (H*chunks G (lanes h newUnit*blocks))*h≤2*R:=
    (Nat.mul_le_mul_right h (Nat.mul_le_mul_left H delta)).trans d
  have half : h/2<2^(h/2):=Nat.lt_two_pow_self
  have budget : h≤2*2^(h/2):=by omega
  have hh : h*h≤2*R:=(Nat.mul_le_mul_right h budget).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 tab)
  have small : (1+2^(h/2)+H+K)*h≤R := by
    rw [Nat.add_assoc (1+2^(h/2)) H K]
    exact (Nat.mul_le_mul_right h (Nat.add_le_add_left hostCount (1+2^(h/2)))).trans base
  unfold scanVolume
  change _≤11*R
  simp only [Nat.add_mul,Nat.one_mul] at small ⊢
  omega


end Hierarchy.DescentDatedAddressBook.MaterialProgram

end OAI
