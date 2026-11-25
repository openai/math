import OAI.Hierarchy.DescentNativeBases
import OAI.Hierarchy.DescentSelectedBaseLoad
import OAI.Hierarchy.DescentGroupingFactor

namespace OAI
/-! # The native dyadic bases and one common invertible block placement -/

namespace Hierarchy.DescentColonies
open DescentBaseProfile DescentBaseVariance DescentGL
open scoped Classical BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

omit [Fintype V] [DecidableEq V] in
private theorem density_from_mean (weight : V → Block k → ℕ) (v : V) {b f B : ℕ}
    (hk : b≤k) (hB : 0<B)
    (fit : (2:ℝ)^(k-b)*blockMean k (fun i => (weight v i:ℝ))≤(2:ℝ)^f*B) :
    (∑i,normalized weight ((2:ℕ)^f*B) v i)≤(2:ℝ)^b := by
  have combine : (2:ℝ)^k=2^(k-b)*2^b := by rw [←pow_add,Nat.sub_add_cancel hk]
  have one : (0:ℝ)<2^(k-b) := by positivity
  have room : (0:ℝ)<(2:ℝ)^f*B := by positivity
  unfold blockMean at fit
  rw [combine] at fit
  have cleaned : (∑i,(weight v i:ℝ))/(2:ℝ)^b≤(2:ℝ)^f*B := by
    convert fit using 1; field_simp
  have sumBound := (div_le_iff₀ (by positivity : (0:ℝ)<2^b)).mp cleaned
  simp only [normalized,Nat.cast_ofNat,←Finset.sum_div]
  exact (div_le_iff₀ room).mpr (by linarith)

/-- Concrete ordered endpoint pairs. A fixed public incidence list with a
specified orientation can be obtained by assigning zero traffic on the reverse
orientation. -/
abbrev Contacts (near : V → Finset V) := Σ v,near v

theorem reset_placement (near : V → Finset V) (sym : ∀ v w,w∈near v ↔ v∈near w)
    {Δ r f K B : ℕ} (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (hB : 0<B)
    (quota : Δ*2^decayExponent Δ≤K) (hK : 0<K) (fr : f≤r) (rk : r≤k)
    (weight : V → Block k → ℕ) (room : ∀v i,weight v i≤B)
    (traffic : V → V → Block k → ℝ) (pos : ∀ v w i,0≤traffic v w i)
    (inc : ∀ v i,∑ w∈near v,traffic v w i≤weight v i)
    (ε : ℝ) (eps : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε) :
    let D := 32*Nat.clog 2 (2*Δ)
    let scale := (2:ℕ)^f*B
    let src (e : Contacts near) := e.1
    let dst (e : Contacts near) := e.2.val
    let core (e : Contacts near) (i : Block k) := traffic (src e) (dst e) i/scale
    let X := ∑ e : Contacts near,∑ i,traffic (src e) (dst e) i
    let rr := (2:ℝ)^(1/8:ℝ)
    ∃ (b : V → ℕ) (hk : ∀v,b v≤k) (L : Layout k),
      (∀v,k-r≤b v ∧ b v≤k-f) ∧
      (∀ v w,w∈near v → b w≤b v+decayExponent Δ) ∧
      ((scale:ℝ)*∑ v,(2:ℝ)^b v≤4*(ε+∑v,∑i,(weight v i:ℝ))) ∧
      (∀ v id,(∑ w∈near v,∑ _j∈touching (b v) (b w) id,
        pairCapacity k (b v) (b w) (blockMean k (traffic v w)) scale K)≤2*(scale:ℝ)) ∧
      (∀v,(∀i,weight v i=B) → b v=k-f) ∧
      (let j := fun e => max (b (src e)) (b (dst e))
       let hj := fun e => max_le (hk (src e)) (hk (dst e))
       let keys := forced (rearrangedLoad weight L) (fun v w => w∈near v) D (2*scale) b∪
         capacityEnds j hj L core K (reservationEndpoints b src dst)
       (scale:ℝ)*(∑p∈validBases b keys,baseValue b hk (normalized weight scale) L p)≤
         4*((scale:ℝ)*(∑v,(2:ℝ)^b v)*(8*((2:ℝ)^f)^(-(7/8):ℝ)*(1/(rr-1)+1/(1-rr/2)))+
           (K:ℝ)^2*X/2^f)) := by
  dsimp only
  let scale := 2^f*B
  have sr : (scale:ℝ)=(2:ℝ)^f*B := by simp [scale]
  have positive : (0:ℝ)<scale := by rw [sr];positivity
  let x (v : V) (i : Block k) : ℝ := weight v i
  obtain ⟨b,fit,smooth,span,capacity,hubs⟩ := reset_bases near sym degree quota hK fr rk
    (by exact_mod_cast hB) x traffic (fun _ _ => Nat.cast_nonneg _) (fun v i => by
      dsimp [x]
      exact_mod_cast room v i) inc eps
  let hk := fun v => (fit v).2.1.trans (Nat.sub_le k f)
  have lp := decay_parameters (by omega : 0<Δ)
  let g := Nat.clog 2 (2*Δ)
  have lg : Δ≤2^g := (Nat.le_mul_of_pos_left _ (by decide : 0<2)).trans (Nat.le_pow_clog (by decide) _)
  have deg (v : V) : (next (fun u z => z∈near u) v).card≤Δ := by simpa [next] using degree v
  let src (e : Contacts near) := e.1
  let dst (e : Contacts near) := e.2.val
  let X := ∑e : Contacts near,∑i,traffic (src e) (dst e) i
  let core (e : Contacts near) (i : Block k) := traffic (src e) (dst e) i/(scale:ℝ)
  have small (e : Contacts near) (i : Block k) : core e i≤1/(2:ℝ)^f := by
    have part := Finset.single_le_sum (f:=fun w => traffic e.1 w i) (fun w _ => pos _ w i) e.2.property
    have lim : traffic (src e) (dst e) i≤B := part.trans ((inc e.1 i).trans (by exact_mod_cast room e.1 i))
    apply (div_le_iff₀ positive).2
    rw [sr]
    convert lim using 1; field_simp
  have total : (∑ e,∑ i,core e i)≤X/((2:ℝ)^f*B) := by
    simp only [core,X,←Finset.sum_div,sr,le_refl]
  obtain ⟨L,paid⟩ := exists_cheap_bad_bases deg branch lg (D:=32*g) le_rfl
    (by dsimp [g]; have := Nat.clog_pos (by decide : 1<2) (by omega : 1<2*Δ);omega)
    b hk (fun v w h => by have := smooth w v ((sym v w).mp h);dsimp [g];omega)
    f B hB weight room (fun v => by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        density_from_mean weight v (hk v) hB (fit v).2.2)
    K X (by exact_mod_cast hK) src dst core (fun e i => div_nonneg (pos _ _ _) positive.le) small total
  refine ⟨b,hk,L,fun v => ⟨(fit v).1,(fit v).2.1⟩,smooth,?_,?_,?_,?_⟩
  · simpa [x] using span
  · simpa using capacity
  · intro v full
    apply hubs v
    intro i
    dsimp [x]
    exact_mod_cast full i
  · simpa only [g, src, dst, core, X, scale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using paid

end
end Hierarchy.DescentColonies

end OAI
