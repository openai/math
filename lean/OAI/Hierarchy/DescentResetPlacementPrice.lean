import OAI.Hierarchy.DescentResetGroupingBounds
import OAI.Hierarchy.DescentResetRateNumbers
import OAI.Hierarchy.DescentResetPlacement

namespace OAI
/-! # Paying for all exceptional relay hops in one actual dyadic placement -/

namespace Hierarchy.DescentColonies
open DescentBaseProfile DescentBaseVariance DescentGL
open scoped Classical BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

theorem resetTail_nonneg (f : ℕ) : 0≤resetTail f := by
  let r := (2:ℝ)^(1/8:ℝ)
  have below : r<2 := by
    dsimp [r]
    conv_rhs => rw [←Real.rpow_one (2:ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have above : 1<r := Real.one_lt_rpow (by norm_num) (by norm_num)
  change 0≤((2:ℝ)^f)^(-(7/8):ℝ) * (1/(r-1)+1/(1-r/2))
  have lo : 0<r-1 := by linarith
  have hi : 0<1-r/2 := by linarith
  positivity

/-- The actual union of split and overflow endpoint keys used by reset_placement. -/
def resetKeys (near : V→Finset V) (Δ f B K : ℕ)
    (weight : V → Block k → ℕ) (traffic : V → V → Block k → ℝ)
    (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k) : Finset (V×ℕ) :=
  let scale := (2:ℕ)^f*B
  let src (e : Contacts near) := e.1
  let dst (e : Contacts near) := e.2.val
  let j (e : Contacts near) := max (b (src e)) (b (dst e))
  let hj (e : Contacts near) := max_le (hk (src e)) (hk (dst e))
  let core (e : Contacts near) (i : Block k) := traffic (src e) (dst e) i/scale
  forced (rearrangedLoad weight L) (fun v w => w∈near v) (32*Nat.clog 2 (2*Δ)) (2*scale) b ∪
    capacityEnds j hj L core K (reservationEndpoints b src dst)

theorem scale_base_values (weight : V → Block k → ℕ) {a : ℝ}
    (ha : 0<a) (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k) (keys : Finset (V×ℕ)) :
    a*(∑ p∈validBases b keys,baseValue b hk (normalized weight a) L p) =
      ∑p∈validBases b keys,baseValue b hk (fun v i=>(weight v i:ℝ)) L p := by
  have one (p : BaseId b) :
      baseValue b hk (normalized weight a) L p =
        baseValue b hk (fun v i=>(weight v i:ℝ)) L p / a := by
    unfold baseValue load normalized
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hit : p.2=dyadicLayout (hk p.1) L i <;> simp [hit]
  simp_rw [one]
  rw [←Finset.sum_div]
  field_simp [ha.ne']

omit [DecidableEq V] in
theorem contact_mass (near : V→Finset V) (weight : V → Block k → ℕ)
    (traffic : V → V → Block k → ℝ) (inc : ∀v i,∑w∈near v,traffic v w i≤weight v i) :
    (∑ e : Contacts near,∑i,traffic e.1 e.2.val i) ≤ ∑v,∑i,(weight v i:ℝ) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ = ∑ w ∈ near v, traffic v w i := Finset.sum_coe_sort (near v) (fun w => traffic v w i)
    _ ≤ _ := inc v i

/-- The capacities, exceptional load, and retained hubs all use this same
invertible block layout. The hop bound applies to unnormalized physical loads. -/
theorem priced_reset_placement (near : V→Finset V) (sym : ∀ v w,w∈near v ↔ v∈near w)
    {Δ r f K B hops : ℕ} (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (hB : 0<B)
    (quota : Δ*2^decayExponent Δ≤K) (hK : 0<K) (fr : f≤r) (rk : r≤k)
    (weight : V → Block k → ℕ) (room : ∀v i,weight v i≤B)
    (traffic : V→V→Block k→ℝ) (pos : ∀ v w i,0≤traffic v w i)
    (inc : ∀v i,∑w∈near v,traffic v w i≤weight v i) {ε : ℝ}
    (eps : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε)
    (hh : 0<hops) (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ)) :
    let scale := (2:ℕ)^f*B
    ∃ (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k),
      (∀v,k-r≤b v ∧ b v≤k-f) ∧
      (∀v w,w∈near v → b w≤b v+decayExponent Δ) ∧
      ((scale:ℝ)*∑v,(2:ℝ)^b v≤4*(ε+∑v,∑i,(weight v i:ℝ))) ∧
      (∀v id,(∑w∈near v,∑ _j∈touching (b v) (b w) id,
        pairCapacity k (b v) (b w) (blockMean k (traffic v w)) scale K)≤2*(scale:ℝ)) ∧
      (∀v,(∀i,weight v i=B) → b v=k-f) ∧
      ((hops:ℝ)*∑p∈validBases b (resetKeys near Δ f B K weight traffic b hk L),
        baseValue b hk (fun v i=>(weight v i:ℝ)) L p)≤ε+∑v,∑i,(weight v i:ℝ) := by
  dsimp only
  let scale := 2^f*B
  obtain ⟨b,hk,L,fit,smooth,span,capacity,hubs,paid⟩ :=
    reset_placement near sym branch degree hB quota hK fr rk weight room traffic pos inc ε eps
  refine ⟨b,hk,L,fit,smooth,span,capacity,hubs,?_⟩
  let keys := resetKeys near Δ f B K weight traffic b hk L
  let mass := ∑v,∑i,(weight v i:ℝ)
  let total := ∑e : Contacts near,∑i,traffic e.1 e.2.val i
  have hp : 0<(scale:ℝ) := by dsimp [scale]; positivity
  have he : 0≤ε := (by positivity : 0≤(Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)).trans eps
  have hm : 0≤mass := by dsimp [mass]; positivity
  have ht : total≤ε+mass := by
    exact (contact_mass near weight traffic inc).trans (le_add_of_nonneg_left he)
  have estimate : (scale:ℝ)*(∑p∈validBases b keys,baseValue b hk (normalized weight (scale:ℝ)) L p) ≤
      4*((scale:ℝ)*(∑v,(2:ℝ)^b v)*(8*resetTail f)+(K:ℝ)^2*total/2^f) := by
    simpa only [keys,resetKeys,scale,total,resetTail,mul_assoc] using paid
  rw [scale_base_values weight hp] at estimate
  have absCost := bad_fraction (add_nonneg he hm) span ht (resetTail_nonneg f) estimate small
  have hopsPos : (0:ℝ)<hops := by exact_mod_cast hh
  calc
    _ ≤ (hops:ℝ)*((1/(hops:ℝ))*(ε+mass)) := mul_le_mul_of_nonneg_left absCost hopsPos.le
    _ = _ := by dsimp [mass]; field_simp [hopsPos.ne']

end
end Hierarchy.DescentColonies

end OAI
