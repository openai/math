import OAI.Hierarchy.DescentPaidResetLayout
import OAI.Hierarchy.DescentNativeProfileScan

namespace OAI
/-! # Base reservations for the actual finite integer profile -/

noncomputable section
namespace Hierarchy.DescentColonies
open DescentBaseProfile
open scoped BigOperators Classical

variable {H k : ℕ}

def measuredNear (ns : Native.Neighbors H) (v : Fin H) := (ns[v.val]).toFinset

def measuredLoad (rows : Native.Rows H (2^k)) (v : Fin H) (i : Block k) := (rows[v.val])[i.val]

def measuredDepth (ns : Native.Neighbors H) (rows : Native.Rows H (2^k)) (Δ r f B : ℕ) (v : Fin H) :=
  (Native.profile ns rows (2^f*B) (decayExponent Δ) (k-r) (k-f))[v.val]

/-- All six static geometry assertions hold at the specifically computed
integer depths. The old per-block measurements also supply the all-contact
outgoing reservation inequalities at those actual depths. -/
theorem measured_bases (ns : Native.Neighbors H) (rows : Native.Rows H (2^k)) (Δ r f B K : ℕ)
    (ε : ℝ) (traffic : Fin H→Fin H→Block k→ℝ)
    (sym : ∀v w : Fin H,w∈ns[v.val] ↔ v∈ns[w.val]) (degree : ∀ v : Fin H,(ns[v.val]).length≤Δ)
    (quota : Δ*2^decayExponent Δ≤K) (positive : 0<K) (fr : f≤r) (rk : r≤k)
    (bpos : 0<B) (limit : ∀v i,measuredLoad rows v i≤B)
    (incidence : ∀v i,∑u∈measuredNear ns v,traffic v u i≤(measuredLoad rows v i:ℝ))
    (slack : (H:ℝ)*2^(k-r)*((2^f*B:ℕ):ℝ)≤ε) :
    BaseGeometry (measuredNear ns) Δ r f B K ε (measuredLoad rows) traffic (measuredDepth ns rows Δ r f B) := by
  let S := 2^f*B
  let b := measuredDepth ns rows Δ r f B
  let wt := fun v (i : Block k)=>(measuredLoad rows v i:ℝ)
  have live : 0<S := Nat.mul_pos (Nat.two_pow_pos _) bpos
  have Spos : 0<(S:ℝ) := by exact_mod_cast live
  have fk : f≤k := fr.trans rk
  obtain ⟨rank,smooth,total⟩ := Native.physical_profile ns rows sym degree (decay_degree Δ)
    (Nat.zero_lt_succ _) (show k-r≤k-f by omega) live (Native.dyadic_room rows f B fk limit)
  change (∀v : Fin H,k-r≤b v ∧ b v≤k-f ∧ Native.totalWeight rows v≤S*2^b v) at rank
  change (∀v w : Fin H,w∈ns[v.val]→b w≤b v+decayExponent Δ) at smooth
  have upper (v : Fin H) : Native.totalWeight rows v=∑i : Block k,measuredLoad rows v i := Native.totalWeight_eq _ _
  have weights (v : Fin H) : (Native.totalWeight rows v:ℝ)=∑i,wt v i := by
    change (Native.totalWeight rows v : ℝ) = ∑i : Block k,(measuredLoad rows v i : ℝ)
    rw [upper v, Nat.cast_sum]
  have load (v : Fin H) : (∑i,wt v i)≤(S:ℝ)*2^b v := by
    rw [←weights]
    exact_mod_cast (rank v).2.2
  have range (v : Fin H) : b v≤k := (rank v).2.1.trans (Nat.sub_le _ _)
  have smooth' (v u : Fin H) (hu : u∈measuredNear ns v) : b u≤b v+decayExponent Δ :=
    smooth v u (List.mem_toFinset.mp hu)
  have mean (v : Fin H) : (2:ℝ)^(k-b v)*blockMean k (wt v)≤S := by
    unfold blockMean
    rw [←mul_div_assoc,div_le_iff₀ (by positivity : (0:ℝ)<2^k)]
    calc
      _ ≤ (2:ℝ)^(k-b v)*((S:ℝ)*2^b v) := mul_le_mul_of_nonneg_left (load v) (by positivity)
      _ = (S:ℝ)*(2^(k-b v)*2^b v) := by ring
      _ = _ := by rw [←pow_add,Nat.sub_add_cancel (range v)]
  refine ⟨fun v=>⟨(rank v).1,(rank v).2.1⟩,smooth',?_,?_,?_,?_⟩
  · intro v
    have norm : (∑i,wt v i/(S:ℝ))≤(2:ℝ)^b v := by
      rw [←Finset.sum_div,div_le_iff₀ Spos,mul_comm]
      exact load v
    simpa [normalized,S,wt,b] using norm
  · change (S:ℝ)*(∑v,(2:ℝ)^b v)≤4*(ε+∑v,∑i,wt v i)
    have t : (S:ℝ)*(∑v : Fin H,(2:ℝ)^b v) ≤
        4*((H:ℝ)*2^(k-r)*S+∑v : Fin H,(Native.totalWeight rows v:ℝ)) := by exact_mod_cast total
    simp_rw [weights] at t
    exact t.trans (by gcongr)
  · intro v i
    apply reservation_budget (measuredNear ns) b range smooth' (fun j=>(List.toFinset_card_le _).trans (degree j))
      quota positive (S:ℝ) Spos.le (fun v w=>blockMean k (traffic v w)) (fun v=>blockMean k (wt v)) _ mean v i
    intro u
    simpa [blockMean,Block,wt] using mean_incidence (measuredNear ns) wt traffic incidence u
  · intro v full
    have meanEq : blockMean k (wt v)=(B:ℝ) := by
      have den : (2:ℝ)^k≠0 := by positivity
      simp [blockMean,wt,full,Block,den]
    have h := mean v
    rw [meanEq] at h
    change (2:ℝ)^(k-b v)*B≤((2^f*B:ℕ):ℝ) at h
    push_cast at h
    have ex : k-b v≤f := (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp
      (le_of_mul_le_mul_right h (by exact_mod_cast bpos : 0<(B:ℝ)))
    have high := (rank v).2.1
    exact show b v=k-f by omega

/-- Reindex the actual native ROM rows and their incident traffic sum back to
the caller's site type. All physical inequalities refer to its original site,
block and edge weights. -/
theorem measured_bases_at {V : Type*} [Fintype V] [DecidableEq V] (idx : V≃Fin H)
    (ns : Native.Neighbors H) (rows : Native.Rows H (2^k)) (Δ r f B K : ℕ) (ε : ℝ)
    (near : V→Finset V) (weight : V→Block k→ℕ) (traffic : V→V→Block k→ℝ)
    (topology : ∀v,(near v).map idx.toEmbedding=measuredNear ns (idx v))
    (loads : ∀v i,measuredLoad rows (idx v) i=weight v i)
    (sym : ∀v u,u∈near v↔v∈near u) (degree : ∀v : Fin H,(ns[v.val]).length≤Δ)
    (quota : Δ*2^decayExponent Δ≤K) (positive : 0<K) (fr : f≤r) (rk : r≤k)
    (bpos : 0<B) (limit : ∀v i,weight v i≤B)
    (incidence : ∀v i,∑u∈near v,traffic v u i≤(weight v i:ℝ))
    (slack : (Fintype.card V:ℝ)*2^(k-r)*((2^f*B:ℕ):ℝ)≤ε) :
    BaseGeometry near Δ r f B K ε weight traffic ((measuredDepth ns rows Δ r f B) ∘ idx) := by
  let t := fun v u : Fin H=>traffic (idx.symm v) (idx.symm u)
  have mem (v u : V) : idx u∈ns[(idx v).val] ↔ u∈near v := by
    change idx u∈ns[(idx v).val]↔_
    rw [←List.mem_toFinset]
    change idx u∈measuredNear ns (idx v)↔_
    simp [←topology]
  have sy (v u : Fin H) : u∈ns[v.val]↔v∈ns[u.val] := by
    obtain ⟨v,rfl⟩ := idx.surjective v
    obtain ⟨u,rfl⟩ := idx.surjective u
    exact (mem v u).trans ((sym v u).trans (mem u v).symm)
  have hload (v : Fin H) (i : Block k) : measuredLoad rows v i≤B := by
    obtain ⟨v,rfl⟩ := idx.surjective v
    rw [loads];exact limit _ _
  have budget (v : Fin H) (i : Block k) :
      ∑u∈measuredNear ns v,t v u i≤(measuredLoad rows v i:ℝ) := by
    obtain ⟨v,rfl⟩ := idx.surjective v
    rw [←topology,Finset.sum_map,loads]
    simpa only [t,Equiv.coe_toEmbedding,Equiv.symm_apply_apply] using incidence v i
  have card : Fintype.card V=H := by simpa using Fintype.card_congr idx
  have data := measured_bases ns rows Δ r f B K ε t sy degree quota positive fr rk bpos hload budget (card ▸ slack)
  let b := measuredDepth ns rows Δ r f B
  refine ⟨fun v=>data.bounds (idx v),fun v u hu=>data.smooth (idx v) (idx u) ((List.mem_toFinset.mpr ((mem _ _).mpr hu))),?_,?_,?_,?_⟩
  · intro v
    simpa only [normalized,loads,Function.comp_apply] using data.density (idx v)
  · have volume := data.span
    rw [←idx.sum_comp (fun v=>(2:ℝ)^b v),←idx.sum_comp (fun v=>∑i,(measuredLoad rows v i:ℝ))] at volume
    simpa only [Function.comp_apply,loads,b] using volume
  · intro v i
    have h := data.capacity (idx v) i
    rw [←topology,Finset.sum_map] at h
    simpa only [t,Equiv.coe_toEmbedding,Equiv.symm_apply_apply,Function.comp_apply] using h
  · intro v full
    exact data.hubs (idx v) (fun i=>(loads v i).trans (full i))

end Hierarchy.DescentColonies

end
end OAI
