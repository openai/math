import OAI.ThreeFlat.Diagonal.ShrinkActualSlots
import OAI.ThreeFlat.Diagonal.ShrinkOwnerKernel
import OAI.ThreeFlat.Diagonal.GroupedRewrite

namespace OAI
/-! # Correspondence of the grouped crossing graph with retained supply types -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {c d : ℕ} {V H Tag L : Type}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable (P : PackingData V H Tag L d c)

def supplyGraph : PortGraph (Fin 6) (Fin 8) := ⟨ShrinkMotif.supplySrc,ShrinkMotif.supplyDst⟩

abbrev CrossType (layout : Bool) (m : P.Motif) :=
  MotifKernel.Cross (fun _ : P.Motif => supplyGraph) (partySite P layout) m

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
private theorem different_roles (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
    (layout : Bool) (m : P.Motif) :
    Function.Injective (![P.roleA m,P.roleB m,P.roleD layout m] : Fin 3 → _) := by
  obtain ⟨hab,had,hbd⟩ := distinct_bases P hn good layout m
  intro i j h
  have h' := congrArg base h
  fin_cases i <;> fin_cases j <;> simp_all

/-- The four crossing edges are the four survivors in the selected old layout. -/
def crossTypeEquiv (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
    (layout : Bool) (m : P.Motif) : Fin 4 ≃ CrossType P layout m := by
  let yes (e : Fin 8) : MotifKernel.wireOwner supplyGraph.tail supplyGraph.head (partySite P layout m) e = none
      ↔ ∃ i, ShrinkMotif.survivor layout i = e := by
    simp only [MotifKernel.wireOwner, ite_eq_right_iff, reduceCtorEq, imp_false]
    exact (not_congr (different_roles P hn good layout m).eq_iff).trans (ShrinkMotif.survives_iff layout e)
  let f : Fin 4 → CrossType P layout m := fun i => ⟨_,(yes _).mpr ⟨i,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · exact fun i j he => ShrinkMotif.survivor_distinct layout (congrArg Subtype.val he)
  · rintro ⟨e,he⟩
    obtain ⟨i,hi⟩ := (yes e).mp he
    exact ⟨i,Subtype.ext hi⟩

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
@[simp] theorem crossTypeEquiv_val (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
    (layout : Bool) (m : P.Motif) (i : Fin 4) :
    (crossTypeEquiv P hn good layout m i).val = ShrinkMotif.survivor layout i := rfl

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
/-- A party is placed at the old role it denotes. -/
theorem partySite_eq_role (layout : Bool) (m : P.Motif) (j : Fin 6) :
    partySite P layout m j = siteOf P layout (partyRole layout j) m := by
  cases layout <;> fin_cases j <;> rfl

variable (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset) (layout : Bool)

abbrev CrossEdge := Σ m, CrossType P layout m

/-- Number of a retained crossing type in the conventional four-type order. -/
def typeIndex (e : CrossEdge P layout) : Fin 4 := (crossTypeEquiv P hn good layout e.1).symm e.2

private theorem pair_fin_heq {X : Type} {a b : ℕ} (m : X) (i : Fin a) (j : Fin b)
    (same : a=b) (number : i.val=j.val) : HEq (m,i) (m,j) := by
  subst b
  exact heq_of_eq (congrArg (Prod.mk m) (Fin.ext number))

/-- Reorder a crossing edge and its parallel piece into the physical occurrence
identifier used by the rooted slot graph construction. -/
def crossingPieces (n : Fin 4 → ℕ) :
    (Σ e : CrossEdge P layout, Fin (n (typeIndex P hn good layout e))) ≃ PhysicalPiece P n := by
  let f : (Σ e : CrossEdge P layout, Fin (n (typeIndex P hn good layout e))) → PhysicalPiece P n :=
    fun x => ⟨typeIndex P hn good layout x.1,x.1.1,x.2⟩
  let inv : PhysicalPiece P n → (Σ e : CrossEdge P layout, Fin (n (typeIndex P hn good layout e))) :=
    fun ⟨t,m,i⟩ => ⟨⟨m,crossTypeEquiv P hn good layout m t⟩, Fin.cast (congrArg n ((crossTypeEquiv P hn good layout m).symm_apply_apply t).symm) i⟩
  exact {
    toFun := f
    invFun := inv
    left_inv := by
      rintro ⟨⟨m,e⟩,i⟩
      apply Sigma.ext
      · exact congrArg (fun j=>Sigma.mk m j) ((crossTypeEquiv P hn good layout m).apply_symm_apply e)
      · exact (Fin.heq_ext_iff (by simp [f,inv,typeIndex])).2 rfl
    right_inv := by
      rintro ⟨t,m,i⟩
      apply Sigma.ext
      · exact (crossTypeEquiv P hn good layout m).symm_apply_apply t
      · exact pair_fin_heq m _ _ (congrArg n ((crossTypeEquiv P hn good layout m).symm_apply_apply t)) rfl
  }

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
/-- The actual site of a crossing incidence in the grouped graph. -/
theorem crossing_site (e : CrossEdge P layout) (side : Bool) :
    (MotifKernel.crossGraph (fun _ : P.Motif => supplyGraph) (partySite P layout)).vertex e side =
      siteOf P layout (if side then (supplyRoles layout (typeIndex P hn good layout e)).2
        else (supplyRoles layout (typeIndex P hn good layout e)).1) e.1 := by
  obtain ⟨m,e⟩ := e
  obtain ⟨t,rfl⟩ := (crossTypeEquiv P hn good layout m).surjective e
  cases side <;> simp [PortGraph.vertex,supplyGraph,typeIndex,actual_roles,partySite_eq_role]

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
