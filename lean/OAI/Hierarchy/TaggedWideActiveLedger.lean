import OAI.Hierarchy.TaggedWideActiveCost
import OAI.Hierarchy.ProbeBudget

namespace OAI
/-! # Moving the paid link bill to the observed, densely numbered emitter tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open AdaptiveProbe ProtocolRAMEmit TaggedPrune
open scoped BigOperators Classical
variable {rows h w k M : ℕ} {b : Fin k→ℕ} {D : Layout h w b}
variable (raw : Fin rows→Row)

def activeScale (scale : ActiveRows raw→ℝ) (i : Fin rows) : ℝ :=
  if pos:0<(raw i).width then scale ⟨i,pos⟩ else 0

theorem ledger_of_active {E : Type*} [Fintype E] (ord : E↪Fin rows) (scale len y : E→ℝ)
    (edge : ActiveRows raw→E) (atRow : ∀i,ord (edge i)=i.val)
    (metric : ∀i,((raw i.val).lengthCode:ℝ)=len (edge i))
    (ratio : ∀i,((raw i.val).width:ℝ)/w=y (edge i))
    {p q Q Λ : ℝ} {n Nc : ℕ} (hΛ : 0≤Λ)
    (ht : ∀e,0 ≤ scale e) (hl : ∀e,0≤len e) (hy : ∀e,0≤y e)
    (paid : TermBudget p q Q Λ n w M Nc scale len y) :
    TermBudget p q Q Λ n w M Nc (activeScale raw (scale ∘ edge))
      (fun i=>(raw i).lengthCode) (fun i=>((raw i).width:ℝ)/w) := by
  let live (i : Fin rows) := 0<(raw i).width
  let native (i : Fin rows) : ℝ := ((raw i).lengthCode:ℝ)*(((raw i).width:ℝ)/w)+
    Λ*capacity p q Q (activeScale raw (scale ∘ edge) i) (raw i).lengthCode
  let cost (e:E) := len e*y e+Λ*capacity p q Q (scale e) (len e)
  have key (i:ActiveRows raw): native i.val=cost (edge i) := by
    simp only [native,cost,activeScale,dite_eq_left i.property,Function.comp_apply,ratio i,metric i]
  have nn (e:E):0≤cost e := by
    apply add_nonneg (mul_nonneg (hl e) (hy e)) (mul_nonneg hΛ ?_)
    unfold capacity
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Real.rpow_nonneg (ht e) _) ((Real.rpow_nonneg (hl e) _).trans (le_max_left ..))
  have active := active_le_catalogue raw ord cost (fun i=>native i.val) (fun i=>⟨edge i,atRow i,key i⟩) nn
  have idle : (∑ i : {t : Fin rows // ¬live t},native i.val)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have no:¬0<(raw i.val).width:=i.property
    have zero: (raw i.val).width=0:=Nat.eq_zero_of_not_pos no
    simp [native,activeScale,zero]
  change (∑ i,native i)≤_
  rw [←Fintype.sum_subtype_add_sum_subtype live native,idle,add_zero]
  exact active.trans paid

def activeOrdinal : Fin (Fintype.card (ActiveRows raw))↪Fin rows :=
  (Fintype.equivFin (ActiveRows raw)).symm.toEmbedding.trans (Function.Embedding.subtype _)

def denseCross (G : Geometry D M 1 raw) := G.links.cross.map (activeOrdinal raw)

theorem denseCross_zero (G : Geometry D M 1 raw) (i : Fin rows) (inside : i∈denseCross raw G) :
    activeScale raw G.scale i=0 := by
  obtain ⟨j,hj,rfl⟩:=Finset.mem_map.mp inside
  have diff := (Finset.mem_filter.mp hj).2
  have enough : G.scale (activeIndex raw j) = 0 := G.links.different_zero j diff
  change activeScale raw G.scale (activeIndex raw j).val=0
  simpa only [activeScale,dite_eq_left (activeIndex raw j).property] using! enough

theorem keep_dense (G : Geometry D M 1 raw) (n : ℕ) :
    G.links.Keep n ↔ 2*(M:ℝ)*(∑j,(b j:ℝ))/w-n≤
      ∑i∈denseCross raw G,((raw i).lengthCode:ℝ)*((raw i).width/w) := by
  let price (i : Fin rows) : ℝ := ((raw i).lengthCode : ℝ) * ((raw i).width / w)
  let cross : Finset (Fin (Fintype.card (ActiveRows raw))) := G.links.cross
  have total : G.links.charge = ∑ i ∈ denseCross raw G, price i := by
    calc
      G.links.charge = ∑ j ∈ cross, price (activeOrdinal raw j) := by
        apply Finset.sum_congr rfl
        intro j _
        change ((raw (activeIndex raw j).val).lengthCode : ℝ) / (↑(1 : ℕ) : ℝ) *
          ((raw (activeIndex raw j).val).width / w) = price (activeOrdinal raw j)
        rw [Nat.cast_one, div_one]
        rfl
      _ = ∑ i ∈ denseCross raw G, price i :=
        (Finset.sum_map (s := cross) (activeOrdinal raw) price).symm
  change (_ ≤ G.links.charge) ↔ (_ ≤ ∑ i ∈ denseCross raw G, price i)
  rw [total]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
