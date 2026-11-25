import OAI.Hierarchy.DescentPhysicalPlacement
import OAI.Hierarchy.DescentObservedBitLoads
import OAI.Hierarchy.DescentResetPieces

namespace OAI
/-! # All incidences and stored history in the one-bit subdivision of a marked branch -/

namespace Hierarchy.DescentSixParty
open DescentGL DescentColonies DescentBaseVariance DescentChosenRouter.Dyadic
open Hierarchy.DescentSixParty.StarKeys
open scoped BigOperators Classical
noncomputable section
variable {F H P V : Type} [Field F] [Fintype V] [DecidableEq V] {k d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)
variable (hub : W.graph.Site→Bool) (atoms : W.graph.Site→List H) (wire hist : ℕ)
local notation "units" => MarkedWorld.siteUnits W hub atoms wire 256 hist
local notation "mass" => blockMass W.graph pos ix units

omit [Field F] in
theorem bit_incidences (q : ℝ) (hq : 0≤q) (p : V×Block k) :
    load (physicalOld W pos ix false) (fun i=>if i∈W.fine.core then q*wire*1 else 0) p+
    load (physicalOld W pos ix true) (fun i=>if i∈W.fine.core then q*wire*1 else 0) p≤q*mass p.1 p.2 := by
  have side (s : Bool) (old : W.graph.Edge→W.graph.Site)
      (truth : ∀i : BitsOf W,physicalOld W pos ix s i=(pos (old i.1),ix (old i.1))) :
      load (physicalOld W pos ix s) (fun i=>if i∈W.fine.core then q*wire*1 else 0) p =
        q * load (fun e : W.core=>(pos (old e.val),ix (old e.val)))
          (fun e=>(wire*W.graph.width e.val:ℕ)) p := by
    have marked (i : BitsOf W) : i ∈ W.fine.core ↔ i.1 ∈ W.core := W.fine_mark i
    let fee (e : W.graph.Edge) : ℝ :=
      if p = (pos (old e), ix (old e)) then ((wire * W.graph.width e : ℕ) : ℝ) else 0
    have coarse : (∑ e : W.graph.Edge, if e ∈ W.core then q * fee e else 0) =
        q * load (fun e : W.core => (pos (old e.val), ix (old e.val)))
          (fun e => (wire * W.graph.width e.val : ℕ)) p := calc
      _ = ∑ e ∈ Finset.univ.filter (fun e : W.graph.Edge => e ∈ W.core), q * fee e :=
        (Finset.sum_filter (fun e : W.graph.Edge => e ∈ W.core) (fun e => q * fee e)).symm
      _ = ∑ e ∈ W.core, q * fee e := by
        rw [show Finset.univ.filter (fun e : W.graph.Edge => e ∈ W.core) = W.core by ext e; simp]
      _ = q * (∑ e ∈ W.core, fee e) := (Finset.mul_sum ..).symm
      _ = q * ∑ e : W.core, fee e.val :=
        congrArg (fun x : ℝ => q * x) (Finset.sum_coe_sort W.core fee).symm
      _ = _ := by
        apply congrArg (fun x : ℝ => q * x)
        unfold load
        apply Finset.sum_congr rfl
        intro i _
        by_cases hit : p = (pos (old i.val), ix (old i.val)) <;> simp [fee, hit]
    refine Eq.trans ?_ coarse
    unfold load
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro e _
    by_cases core : e∈W.core <;> by_cases atp : p=(pos (old e),ix (old e)) <;>
      simp [fee,truth,marked,core,atp,Nat.cast_mul,mul_comm,mul_assoc]
  rw [side false W.graph.src (fun _=>rfl),side true W.graph.dst (fun _=>rfl),←mul_add]
  apply mul_le_mul_of_nonneg_left _ hq
  simpa only [blockMass,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero] using
    (endpoints_at W pos ix wire hub atoms 256 hist (by decide) p.1 p.2)

omit [Field F] in
theorem all_bits_bill (q ε : ℝ) (hq : 0≤q)
    (inside : ∀e∈W.core,hub (W.graph.src e)=false ∧ hub (W.graph.dst e)=false)
    (outside : ∀e∉W.core,hub (W.graph.src e)≠hub (W.graph.dst e))
    (history : (hist:ℝ)*(∑ v,((atoms v).length:ℝ))≤ε) :
    (∑v,∑i,q*mass v i)≤2*(q*wire*W.fine.liveWidth)+257*(q*wire*W.fine.tetherWidth)+q*ε := by
  have total : (∑v,∑i,mass v i)=∑v,units v := by
    unfold blockMass
    calc
      _ = ∑v,∑w : W.graph.Site,∑i : Block k,if pos w=v ∧ ix w=i then units w else 0 :=
        Finset.sum_congr rfl (fun v _=>Finset.sum_comm)
      _ = ∑w : W.graph.Site,∑v,∑i : Block k,if pos w=v ∧ ix w=i then units w else 0 := Finset.sum_comm
      _ = _ := by simp [ite_and]
  have one (v) : (units v:ℝ)=W.siteLoad hub atoms wire 256 hist v := by
    simpa using MarkedWorld.siteUnits_scaled W hub atoms wire 256 hist 1 v
  have count : (∑v,∑i,(mass v i:ℝ))=∑v,W.siteLoad hub atoms wire 256 hist v := by
    simp_rw [←one]
    exact_mod_cast total
  have cost := MarkedWorld.siteLoad_bound W hub atoms wire 256 hist ε inside outside history
  rw [MarkedWorld.fine_core,MarkedWorld.fine_tether]
  simp_rw [←Finset.mul_sum]
  rw [count]
  calc
    _ ≤ q*(2*((wire:ℝ)*W.liveWidth)+((256:ℝ)+1)*((wire:ℝ)*W.tetherWidth)+ε) :=
      mul_le_mul_of_nonneg_left cost hq
    _ = _ := by ring

omit [Field F] in
theorem scaled_marked (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k)
    (keys : Finset (V×ℕ)) (q ε : ℝ) (hq : 0≤q) (hops : ℕ)
    (paid : (hops:ℝ)*(∑p∈validBases b keys,baseValue b hk (fun v i=>(mass v i:ℝ)) L p)
      ≤ε+∑v,∑i,(mass v i:ℝ)) :
    (hops:ℝ)*(∑p∈validBases b keys,baseValue b hk (fun v i=>q*mass v i) L p)
      ≤q*ε+∑v,∑i,q*mass v i := by
  have linear (p : BaseId b) : baseValue b hk (fun v i=>q*mass v i) L p =
      q*baseValue b hk (fun v i=>(mass v i:ℝ)) L p := by
    rcases p with ⟨v,i⟩
    unfold baseValue load
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp_all
  simp_rw [linear,←Finset.mul_sum]
  simpa [mul_add,mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left paid hq

end
end Hierarchy.DescentSixParty

end OAI
