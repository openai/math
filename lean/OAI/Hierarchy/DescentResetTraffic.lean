import OAI.Hierarchy.DescentIntegralSiteLoad
import OAI.Hierarchy.DescentResetPlacement
import OAI.Hierarchy.DescentPackMass

namespace OAI
/-! # Measured symmetric old-core traffic for both sides of the real reset -/

namespace Hierarchy.DescentSixParty
open DescentColonies StarKeys
open scoped Classical BigOperators
noncomputable section

variable {E S V I : Type*} [Fintype E] [Fintype S] [Fintype V] [DecidableEq V] [DecidableEq I]

def directedLoad (edges : Finset E) (src dst : E→S) (position : S→V) (block : S→I)
    (weight : E→ℕ) (v w : V) (i : I) :=
  ∑e∈edges, if position (src e)=v ∧ position (dst e)=w ∧ block (src e)=i then weight e else 0

omit [Fintype E] in
theorem directed_sum (edges : Finset E) (src dst : E→S) (position : S→V) (block : S→I)
    (weight : E→ℕ) (v : V) (i : I) :
    (∑w,directedLoad edges src dst position block weight v w i)=
      ∑u : S,if position u=v ∧ block u=i then
        (∑e∈edges,if src e=u then weight e else 0) else 0 := by
  have sourceRow (u : S) :
      (if position u = v ∧ block u = i then
        ∑e ∈ edges, if src e = u then weight e else 0 else 0) =
      ∑e ∈ edges, if src e = u then
        (if position u = v ∧ block u = i then weight e else 0) else 0 := by
    by_cases selected : position u = v ∧ block u = i <;> simp [selected]
  unfold directedLoad
  simp_rw [sourceRow]
  rw [Finset.sum_comm (s := (Finset.univ : Finset V)) (t := edges),
      Finset.sum_comm (s := (Finset.univ : Finset S)) (t := edges)]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.sum_ite_eq (src e) (fun u => if position u = v ∧ block u = i then weight e else 0)]
  by_cases actual : position (src e) = v ∧ block (src e) = i
  · obtain ⟨site,index⟩ := actual
    simp [site,index]
  · have absent (w : V) : ¬(position (src e)=v ∧ position (dst e)=w ∧ block (src e)=i) :=
      fun h => actual ⟨h.1,h.2.2⟩
    simp [absent,actual]

variable {F : Type*} [Field F] {d k : ℕ} {P : Type*} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)
variable (wire : ℕ)
local notation "wt" => (fun e:W.graph.Edge=>wire*W.graph.width e)

def pairLoad (v w : V) (i : Block k) : ℕ :=
  directedLoad W.core W.graph.src W.graph.dst pos ix wt v w i+
  directedLoad W.core W.graph.dst W.graph.src pos ix wt v w i

omit [Fintype V] [Field F] in
theorem pairLoad_symm (same : ∀e∈W.core,ix (W.graph.src e)=ix (W.graph.dst e))
    (v w : V) (i : Block k) : pairLoad W pos ix wire v w i=pairLoad W pos ix wire w v i := by
  unfold pairLoad directedLoad
  rw [add_comm]
  apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro e he <;> rw [same e he] <;> simp [and_left_comm]

omit [Field F] in
theorem pairLoad_le {H : Type*} (hub : W.graph.Site→Bool) (atoms : W.graph.Site→List H) (β hist : ℕ)
    (hβ : 1≤β) (near : V→Finset V) (v : V) (i : Block k) :
    (∑w∈near v,pairLoad W pos ix wire v w i)≤
      (∑ a : W.graph.Site, if pos a=v ∧ ix a=i then
        MarkedWorld.siteUnits W hub atoms wire β hist a else 0) := by
  apply (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans
  simp only [pairLoad,Finset.sum_add_distrib,directed_sum]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  by_cases addr : pos u=v ∧ ix u=i
  · simp only [addr,MarkedWorld.siteUnits]
    have part (side : W.graph.Edge→W.graph.Site) :
        (∑e∈W.core,if side e=u then wt e else 0) ≤
          ∑e : W.graph.Edge,if u=side e then wt e*(if hub (side e) then β else 1) else 0 := by
      apply (Finset.sum_le_sum_of_subset (Finset.subset_univ W.core)).trans
      apply Finset.sum_le_sum
      intro e _
      by_cases h : side e=u
      · cases col : hub (side e) <;> simp [h,Nat.le_mul_of_pos_right,Nat.zero_lt_of_lt hβ]
      · simp [h,Ne.symm h]
    exact (Nat.add_le_add (part _) (part _)).trans (Nat.le_add_right _ _)
  · simp [addr]

omit [Field F] in
/-- The unordered core amount is counted twice, once at each actual endpoint.
The generic capacity estimator therefore has an explicit global numerator. -/
theorem pairLoad_total :
    (∑v,∑w,∑i,pairLoad W pos ix wire v w i)=2*(wire*W.liveWidth) := by
  have all (src dst : W.graph.Edge→W.graph.Site) :
      (∑v,∑w,∑i,directedLoad W.core src dst pos ix wt v w i)=wire*W.liveWidth := by
    unfold directedLoad MarkedWorld.liveWidth
    simp_rw [Finset.sum_comm (t:=W.core)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp [ite_and]
  simp only [pairLoad,Finset.sum_add_distrib,all,two_mul]

omit [Field F] in
/-- Occupied adjacent row pairs account for the real double-endpoint wire bill.
Using just the adjacency list never requires a separate unrestricted-pair budget. -/
theorem ordered_contact_budget (near : V→Finset V) :
    (∑e : Contacts near,∑i,(pairLoad W pos ix wire e.1 e.2.val i:ℝ))≤
      2*(wire:ℝ)*W.liveWidth := by
  have cap : (∑e : Contacts near,∑i,pairLoad W pos ix wire e.1 e.2.val i)≤2*(wire*W.liveWidth) := by
    rw [←pairLoad_total W pos ix wire,Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro v _
    calc
      _ = ∑ w ∈ near v, ∑ i, pairLoad W pos ix wire v w i :=
        Finset.sum_coe_sort (near v) (fun w : V => ∑ i, pairLoad W pos ix wire v w i)
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  exact_mod_cast cap.trans_eq (Nat.mul_assoc ..).symm

omit [Field F] in
/-- Both physical endpoint loads of the actual old core in a flattened site/block
bin. This is the invoice used by the exceptional set even for directed loops. -/
theorem endpoints_at (hub : W.graph.Site→Bool) {H : Type*} (atoms : W.graph.Site→List H)
    (β hist : ℕ) (hβ : 1≤β) (v : V) (i : Block k) :
    let src := fun e : W.core => (pos (W.graph.src e),ix (W.graph.src e))
    let dst := fun e : W.core => (pos (W.graph.dst e),ix (W.graph.dst e))
    let w := fun e : W.core=>(wt e:ℝ)
    DescentBaseVariance.load src w (v,i)+DescentBaseVariance.load dst w (v,i) ≤
      ((∑ a : W.graph.Site, if pos a=v ∧ ix a=i then
        MarkedWorld.siteUnits W hub atoms wire β hist a else 0):ℝ) := by
  dsimp only
  have calcEnds (s t : W.graph.Edge→W.graph.Site) :
      DescentBaseVariance.load (fun e : W.core=>(pos (s e),ix (s e))) (fun e=>(wt e.val:ℝ)) (v,i)=
        (∑w : V,directedLoad W.core s t pos ix wt v w i : ℕ) := by
    unfold DescentBaseVariance.load directedLoad
    rw [Finset.sum_comm]
    simp only [Nat.cast_sum]
    rw [Finset.sum_coe_sort W.core (fun e : W.graph.Edge =>
      if (v,i) = (pos (s e), ix (s e)) then ((wire * W.graph.width e : ℕ) : ℝ) else 0)]
    apply Finset.sum_congr rfl
    intro e _
    by_cases matchAt : pos (s e)=v ∧ ix (s e)=i
    · simp [matchAt.1,matchAt.2]
    · by_cases hv : pos (s e)=v
      · have hi : ix (s e)≠i := fun h=>matchAt ⟨hv,h⟩
        simp [Prod.ext_iff,hv,hi,Ne.symm hi]
      · simp [Prod.ext_iff,hv,Ne.symm hv]
  rw [calcEnds W.graph.src W.graph.dst,calcEnds W.graph.dst W.graph.src,←Nat.cast_add,
    ←Finset.sum_add_distrib]
  exact_mod_cast (pairLoad_le W pos ix wire hub atoms β hist hβ (fun _=>Finset.univ) v i)

end
end Hierarchy.DescentSixParty

end OAI
