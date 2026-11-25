import OAI.Computability.IntegerMultiplication.Phase.Coast

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Shuttle Net.Tensor Net.Walsh Strip Strip.Dims Strip.Optic Code Packed Loom Dusk
open Finset

noncomputable section
variable {I J W U : Type} [Fintype J] [DecidableEq J] [Fintype W] {σ : ℝ} (d : Guild J W U σ)
variable (k : I→ℕ) (X : (i:I)→ Prairie (dim J) W (k i+1)) {r : Regime I}
abbrev α (i:I) : QuestP (W:=W) (dim J) := ⟨k i+1,X i⟩
variable (H : r.Small (roof (α k X)))
abbrev sun_ i := (X i).plot.sunrise
abbrev moon_ i := (X i).plot.sunset
abbrev foot_ i := (X i).plot.foot
abbrev tops_ i := (X i).plot.tops
abbrev gArea i := (dim J)^(k i)
abbrev rate_ (R : Series W) i := skein W R (X i).radio (k i)
abbrev ahead := white (tops_ k X) (foot_ k X) (gArea (J:=J) k)
abbrev lSize := timeMark ∘ α k X

def rising_ (j : J) i := beach (k:=k i) (X i).plot d.order j
abbrev ground i := (X i).plot.terrain

include d H
omit [DecidableEq J] [Fintype W] d in
private theorem lands :
    r.Has (tally ∘ gArea (J:=J) k) ∧ r.Small (beacon (dim J) ∘ k) := by
  obtain ⟨_,_,h⟩ := children (α k X) H
  refine ⟨Where.descendants k (r:=r) ?_,?_⟩ <;> exact h
omit [DecidableEq J] [Fintype W] d in
private theorem credit :
    r.Has (tally ∘ dect (tops_ k X) (foot_ k X) (gArea (J:=J) k)) ∧
    r.Has fun i=> signs (tops_ k X i) (foot_ k X i) (gArea (J:=J) k i -1) := by
  obtain ⟨_,_,v,u⟩ := profiles (α k X) H
  exact controlFiber _ _ _ v u (lands k X H).1

include d
omit H in
private theorem powers {b : ℕ} (w : Prairie (dim J) W (b+1)) (j:J) :
    (beach w.plot d.order j).terrain.count=w.plot.terrain.count := by
  let M := (dim J)^b
  let h := w.plot.tops
  let g := w.plot.foot
  let P := w.plot.sunrise
  let T := w.plot.sunset
  have t : 1 ≤ M := one_le_pow₀ (d.large.trans' (by decide : 1≤3))
  obtain ⟨n,o⟩ : ∃ n : ℕ,n+1=M := ⟨M-1,by omega⟩
  let C := beach w.plot d.order j
  let V := land (I:=Unit) (fun _=>h) (fun _=>g) () M
  let I0 := P ++ leftF d.order V j
  let U0 := rightF d.order V j ++ T
  change (plain I0 U0 h g ((dim J)^b)).count=(plain P T h g ((dim J)^(b+1))).count
  rw [pow_succ]
  have v : Seal (Track (chunks h g) M) V := wound 2 (width h g) _ (chord ..) M
  obtain ⟨q,e⟩ := monoRay _ d.order v j
  have b0 := bright h g M P T d.order
  exact (((q.exit (Adopt.same (layout T))).enter (Adopt.same (layout P))).view.cost.symm).trans b0.cost

variable (R : Series W)
private theorem production : subroutine (sun_ k X) (moon_ k X)
    (tops_ k X) (foot_ k X) (gArea (J:=J) k) (fun i => (X i).plot.shade)
    (rate_ k X R) (lSize k X) d (z:=oracle (dim J) R) (Y:=fun i t=> Range (α k X i) t) (r:=r) := by
  obtain ⟨s,t,z,v⟩ := profiles (α k X) H
  obtain ⟨x,hm⟩ := credit k X H
  intro j y
  let B (i:I) : Prairie (dim J) W (k i) := ⟨rising_ d k X j i,(X i).radio, y i⟩
  let γ (i:I) : QuestP (W:=W) (dim J) := ⟨k i,B i⟩
  have P0 (i:I) : Range (α k X i) (γ i) :=
    ⟨rfl,rfl,rfl,powers d (X i) j,rfl,rfl⟩
  let A := night (north (sun_ k X) (tops_ k X) (foot_ k X) (gArea (J:=J) k) d j) (south (moon_ k X) (tops_ k X) (foot_ k X) (gArea (J:=J) k) d j)
    (tops_ k X) (foot_ k X) (gArea (J:=J) k)
  let N i := (A i).count
  have V0 : r.Small (roof γ) := by
    have e : Told r (fun i=> Adic.field 2 (dect (tops_ k X) (foot_ k X) (gArea (J:=J) k) i)) := Told.carrier (by decide) _ x
    exact (lands k X H).2.pair ((z.pair (v.pair
      ((s.append (e.stacked _)).shape.pair ((e.stacked _).append t).shape))))
  have G₀ : Station r A :=
    climate (J:=J) γ V0 (by have := d.large; omega)
  let V := (goodsP (dim J) R ∘ γ)
  let τ := ahead k X
  have q₁ : ∀ i,1≤ τ i := Spindle.belly _ Motif.sigma_range.1.le
  have ans := Year.call (j:=oracle (dim J) R) (y:=fun i x=>Range (α k X i) x) (r:=r) (l:=lSize k X) q₁ γ P0 G₀.1
  -- issue needs fresh roof t
  let N' := climate (J:=J) (α k X) H (by have := d.large; omega)
  have v₀ : Alive r N (lSize k X) V := by
    refine shelter A (rate_ k X R) (fun i=> (γ i).2.plot.shade) (fun i=> (γ i).2.silo) G₀ ?_
    intro i
    change (skein W R (X i).radio (k i)).count*_≤users (α k X i)*(2*(_+1))
    rw [strands]
    unfold users
    dsimp only [α,rising_,γ,B,beach]
    apply Nat.mul_le_mul
    · refine Nat.mul_le_mul_left _ ?_
      rw [pow_succ]; exact Nat.le_mul_of_pos_right _ d.rank
    omega
  have h' := Drive.started (l:=lSize k X) G₀.1 |>.chain (Rip.header G₀.1 V0)
  exact ans.openFirst (h'.left v₀)

theorem devote :
    let j := oracle (dim J) R
    let Y := α k X
    Quarterback j (ahead k X) r
      (fun i=>(ground k X i).count) (lSize k X)
      (fun i t=>Range (Y i) t)
      (charges d) (fun i=>goodsP (dim J) R (Y i)) (j.reply ∘ Y) := by
  let b := α k X
  have N₀ := climate (J:=J) b H (by have := d.large; omega)
  let W0 := (fun i=>(X i).plot.shade)
  let P := sun_ k X
  let V := moon_ k X
  let T := tops_ k X
  let L := foot_ k X
  let e := gArea (J:=J) k
  have ha : ∀i,1≤ e i := fun _=> one_le_pow₀ (by have := d.large; omega)
  obtain ⟨p,v,_,_⟩ := profiles b H
  obtain ⟨x,h⟩ := credit k X H
  have G (i) (a:ℕ) (f : a∈ P i++V i) : a≤base := ((X i).plot.radix _ f).2
  have u (i:I) : safe (e i) (width (T i) (L i)) := safe_r
    (show _ ≤ (dim J)^(k i+1) by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by have := d.large; omega)) (X i).plot.okay
  let E := taller P V T L e d.order
  -- defeq n * m = pow_succ? power instance via semiring Nat.instPow no rfl?
  have q (i:I) : e i*dim J = (dim J)^(k i+1) := (pow_succ ..).symm
  let e' i := (dim J)^(k i+1)
  let i0 := fun i:I=>(b i).2.silo
  let K := lSize k X
  let R0 := rate_ k X R
  have m₁ (i:I) : ((cargo (dim J) R (α k X i)).count)*(W0 i+1)≤K i := by
    rw [cargo,strands]
    dsimp only [α,K,W0,lSize,timeMark,users,Function.comp_apply]
    gcongr; omega
  have m₂ (i) : (R0 i).count*(2*(W0 i+1))≤K i := by
    rw [show (R0 i).count=_ from strands W R (X i).radio (k i)]
    change _ ≤ (X i).radio*dim W^(k i+1)*(2*(W0 i+1))
    refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)
    rw [pow_succ]; exact Nat.le_mul_of_pos_right _ d.rank
  have S₀ : subroutine P V T L e W0 R0 K d (z:=oracle (dim J) R) (Y:=fun i t=> Range (b i) t) :=
    production d k X H R
  have i1 : Alive r (fun i => (E i).count) K (orchid E (double_ R0 R) W0 i0) :=
    shelter _ (fun i=>cargo (dim J) R (b i)) W0 _ N₀ m₁
  exact start_r P V T L e W0 R0 K p v ha x h m₂ d G u S₀ R i0 i1

end
end Phase

end IntegerMultiplication
end Computability
end OAI
