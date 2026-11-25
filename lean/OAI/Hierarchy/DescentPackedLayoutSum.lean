import OAI.Hierarchy.DescentPackedSixBirths
import OAI.Hierarchy.DescentPackedMatchPhysicalOrder
import OAI.Hierarchy.DescentLayoutRows

namespace OAI
/-! # The two layout totals in the actual packed birth shelf -/
namespace Hierarchy.DescentPacking.PackedMatch.LayoutSum
open DescentSixParty DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section
variable {F C : Type} [Field F] [Fintype C] {G : PoweredGadget F} {pages M letters : ℕ}
variable (s : Shape) (code : Profile G.C↪Fin letters)
def price (side : Bool) (token : ℕ) : ℕ :=
  if token=0 then 0 else layoutROM code G.k side (token-1)
theorem price_live (side : Bool) (profile : Profile G.C) :
    price (G:=G) code side ((code profile).val+1)=layoutUnits G.k side profile := by
  simp [price,layoutROM_read]

def score (M : ℕ) (side : Bool) (key : ℕ) : ℕ :=
  ∑ lane : Fin M,∑j : Fin s.pairs,price (G:=G) code side
    (digit (s.digit+1) (SixBirths.slot lane j (0:Fin 6)).val key)

variable {I : C→Type} [∀c,Fintype (I c)]
    (seat : C↪Fin pages×Fin M) (item : ∀c,I c≃Fin (Fintype.card (I c)))
    (cnt : Fin pages→Fin M→Fin (s.pairs+1)) (rows : Chronology.Counts seat (fun c=>Fintype.card (I c)) cnt)
    (profile : (Σc,I c)→Profile G.C) (key : Fin pages→ℕ)
abbrev Address (pages M pairs : ℕ) := Fin pages×(Fin M×Fin pairs)

def spot : (Σc,I c)↪Address pages M s.pairs where
  toFun x:=((seat x.1).1,(seat x.1).2,⟨(item x.1 x.2).val,((item x.1 x.2).isLt.trans_le
    ((rows.live x.1) ▸ Nat.le_of_lt_succ (cnt (seat x.1).1 (seat x.1).2).isLt))⟩)
  inj' := by
    rintro ⟨c,x⟩ ⟨d,y⟩ h
    have same : c = d := seat.injective
      (congrArg (fun z : Address pages M s.pairs => (z.1, z.2.1)) h)
    subst d
    exact congrArg (Sigma.mk c) ((item c).injective (Fin.ext (congrArg (fun z=>z.2.2.val) h)))

theorem spot_hole (i : Address pages M s.pairs) (outside : i∉Finset.univ.map (spot s seat item cnt rows)) :
    (cnt i.1 i.2.1).val≤ i.2.2.val := by
  by_cases active : ∃c,seat c=(i.1,i.2.1)
  · obtain ⟨c,hc⟩:=active
    by_contra! live
    have counted:=rows.live c
    rw [hc] at counted
    have room : i.2.2.val < Fintype.card (I c) := lt_of_lt_of_eq live counted
    let j : Fin (Fintype.card (I c)):=⟨_,room⟩
    apply outside
    apply Finset.mem_map.mpr
    refine ⟨⟨c,(item c).symm j⟩,Finset.mem_univ _,?_⟩
    apply Prod.ext
    · change (seat c).1 = i.1
      exact congrArg (fun p : Fin pages × Fin M => p.1) hc
    · apply Prod.ext
      · change (seat c).2 = i.2.1
        exact congrArg (fun p : Fin pages × Fin M => p.2) hc
      · apply Fin.ext
        change ((item c) ((item c).symm j)).val = j.val
        exact congrArg (fun a : Fin (Fintype.card (I c)) => a.val) ((item c).apply_symm_apply j)
  · have zero:=rows.hole i.1 i.2.1 (fun c h=>active ⟨c,h⟩)
    omega

theorem total (side : Bool)
    (live : ∀c x,digit (s.digit+1) (SixBirths.slot (seat c).2
      (spot s seat item cnt rows ⟨c,x⟩).2.2 (0:Fin 6)).val (key (seat c).1)=(code (profile ⟨c,x⟩)).val+1)
    (hole : ∀ (i : Fin pages) (a : Fin M) (j : Fin s.pairs),(cnt i a).val≤j.val→digit (s.digit+1) (SixBirths.slot a j (0:Fin 6)).val (key i)=0) :
    (∑i,score (G:=G) s code M side (key i))=∑x,layoutUnits G.k side (profile x) := by
  let val (i : Address pages M s.pairs):=price (G:=G) code side (digit (s.digit+1) (SixBirths.slot i.2.1 i.2.2 (0:Fin 6)).val (key i.1))
  have absent (i : Address pages M s.pairs) (_ : i∈Finset.univ) (notIn : i∉Finset.univ.map (spot s seat item cnt rows)) :
      val i=0 := by
    rw [show val i=price (G:=G) code side _ from rfl,hole i.1 i.2.1 i.2.2 (spot_hole s seat item cnt rows i notIn)]
    rfl
  calc
    _=∑i,val i := by simp only [Fintype.sum_prod_type,score,val]
    _=∑x,val (spot s seat item cnt rows x) := by
      rw [←Finset.sum_subset (Finset.subset_univ (Finset.univ.map (spot s seat item cnt rows))) absent,Finset.sum_map]
    _=_ := by
      apply Finset.sum_congr rfl
      rintro ⟨c,x⟩ _
      exact (congrArg (price (G := G) code side) (live c x)).trans
        (price_live code side (profile ⟨c,x⟩))

end
end Hierarchy.DescentPacking.PackedMatch.LayoutSum

end OAI
