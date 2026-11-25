import OAI.Hierarchy.DescentResetStencilGather
import OAI.Hierarchy.DescentGLPackedBlocks
import OAI.Hierarchy.DescentGLPackedScale

namespace OAI
/-! # A single dyadic lane pitch for the basis shuffle and reset stencil -/
namespace Hierarchy.DescentPlainTerminal.Suffix.Stencil
open DescentSIMDLookup DescentPackedZip DescentGLPacked
open scoped Classical
noncomputable section

def laneExponent (c shared h : ℕ) := lowBits c shared h

theorem pitch (c r shared h : ℕ) :
    let e:=laneExponent c shared h
    (c-e)+(e+r)=c+r ∧ 2^e*2^r=2^(e+r) ∧ chunks (2^c) (2^e)=2^(c-e) := by
  dsimp only
  let e:=laneExponent c shared h
  have below : e≤c:=Nat.min_le_left ..
  have same : c-e+e=c:=Nat.sub_add_cancel below
  refine ⟨by omega,(pow_add ..).symm,?_⟩
  simpa only [same] using chunk_count (c-e) e

theorem rom_bits {c r fieldBits record shared h : ℕ} (pos : 0<shared) (wide : 4*shared≤h)
    (word : fieldBits*2^r≤ shared) (block : record≤ shared) :
    (fieldBits+fieldBits)*2^(laneExponent c shared h+r)≤h/2 ∧
    record*2^laneExponent c shared h≤h/2 := by
  have base:=lane_fit c shared h pos wide
  rw [pow_add]
  dsimp only [laneExponent]
  constructor
  · calc _ = (fieldBits*2^r+fieldBits*2^r)*2^lowBits c shared h := by ring
         _ ≤ _ := (Nat.mul_le_mul_right _ (Nat.add_le_add word word)).trans base
  · exact (Nat.mul_le_mul_right _ (block.trans (Nat.le_add_right ..))).trans base

/-- One shared per-group width covers the register update (old stencil plus one
input field), all index planes, and the raw and emitted suffix arrays. -/
def stencilUnit (r m Δ n t : ℕ) :=
  max (n*count r (Δ+Δ)+n) (max ((m+1)*2^r) (max ((t+n)*2^r) (1+r*2^r)))

theorem unit_bound {r m Δ n t A : ℕ} (hw : 2^r≤A) (hm : m≤A) (hΔ : Δ≤A)
    (hn : n≤A) (ht : t≤A) :
    stencilUnit r m Δ n t≤15*A^3 := by
  have pos : 0<A:=(Nat.two_pow_pos _).trans_le hw
  have lr : r≤A:=(Nat.lt_two_pow_self.le : r≤2^r).trans hw
  have nonzero : 1≤A:=pos
  have square : A≤A*A:=Nat.le_mul_of_pos_left A pos
  have cubic : A*A≤A^3:=by simpa [pow_succ,pow_two] using (Nat.le_mul_of_pos_right (A*A) pos)
  have c : count r (Δ+Δ)≤12*(A*A):=by
    rw [count_eq]
    have scaled : (Δ+Δ)*(2+2^r)≤(A+A)*(2+A) :=
      Nat.mul_le_mul (Nat.add_le_add hΔ hΔ) (Nat.add_le_add_left hw 2)
    nlinarith only [scaled,Nat.mul_le_mul lr hw,Nat.mul_le_mul hw hw,hw,square,nonzero]
  unfold stencilUnit
  apply max_le
  · nlinarith only [Nat.mul_le_mul hn c,hn,Nat.mul_le_mul_left A square,square,cubic]
  · apply max_le
    · nlinarith only [Nat.mul_le_mul (Nat.add_le_add_right hm 1) hw,square,cubic]
    · apply max_le
      · nlinarith only [Nat.mul_le_mul (Nat.add_le_add ht hn) hw,cubic]
      · nlinarith only [Nat.mul_le_mul lr hw,square,cubic,nonzero]

theorem shape_width (r n : ℕ) : 2*DescentFallbackShapeTable.rows r (2^n)≤2^(2*r+n+2) := by
  have lr : r+1≤2^r:=Nat.lt_two_pow_self
  have ln : 2^n+1≤2*(2^n):=by have:=Nat.two_pow_pos n;omega
  unfold DescentFallbackShapeTable.rows
  have cost:=Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul_right (2^r) lr) ln)
  calc _ ≤ _ := cost
       _ = _ := by rw [show 2*r+n+2=r+r+n+2 by omega,pow_add,pow_add,pow_add];ring

theorem amount_width {r b K : ℕ} (fit : K<2^b) : 2^r*K<2^(r+b) := by
  rw [pow_add]
  exact Nat.mul_lt_mul_of_pos_left fit (Nat.two_pow_pos _)

theorem dyadic_bit_price {r q : ℕ} (T : Fin (count r q)→Tables) (field : Slot r q→Hierarchy.ProtocolRAM.Expr)
    (h w K H c shared L : ℕ) (positive : 0<shared) (wide : 4*shared≤h) (hardware : w≤K*h)
    (bound : ∀s,(field s).work≤L) :
    cost T field H (2^c) (2^laneExponent c shared h)*w≤
      K*((60+2*count r q*(L+11))*(h+H*h+8*H*2^c*shared)) := by
  let e:=laneExponent c shared h
  let N:=H*chunks (2^c) (2^e)
  have erased : chunks (2^c) (2^e)=2^(c-e):=(pitch c r shared h).2.2
  have bill : N*w≤K*(H*h+8*H*2^c*shared) := by
    dsimp only [N]
    rw [erased]
    exact charged H c shared h w K positive wide hardware
  let factor := 60+2*count r q*(L+11)
  have setup : 8 ≤ factor := by dsimp only [factor]; omega
  have perChunk : 48+2*(assembly T field).work ≤ factor := by
    have localWork := assembly_work T field L bound
    dsimp only [factor]
    rw [Nat.mul_assoc]
    omega
  change (4+N*(2*(assembly T field).work+4)+(4+44*N))*w≤_
  calc
    _ = 8*w+(48+2*(assembly T field).work)*(N*w) := by ring
    _ ≤ factor*(K*h)+factor*(K*(H*h+8*H*2^c*shared)) :=
      Nat.add_le_add (Nat.mul_le_mul setup hardware) (Nat.mul_le_mul perChunk bill)
    _ = _ := by dsimp only [factor]; ring


end
end Hierarchy.DescentPlainTerminal.Suffix.Stencil

end OAI
