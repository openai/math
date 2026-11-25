import OAI.Hierarchy.ProbeCoreBoard

namespace OAI
/-! # Local incidence of the fixed identifications and the public sampler sockets -/
namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe
open scoped Classical
noncomputable section

variable (S : PurchaseSampler) {h d k : ℕ}

private theorem same_fixed {x y : Fixed h d} (same : x.val.1=y.val.1) : x=y := by
  apply Subtype.ext
  apply Prod.ext same
  apply (fabricBoard h d).injective
  apply (permutationFabric h d).all_fixed_unique (fabricBoard h d y.val.1) _ _ _ y.property.1
  simpa only [←same] using x.property.1

private theorem same_fixed_right {x y : Fixed h d} (same : x.val.2=y.val.2) : x=y := by
  apply Subtype.ext
  apply Prod.ext _ same
  apply (fabricBoard h d).injective
  apply (permutationFabric h d).all_fixed_unique (fabricBoard h d y.val.2)
  · rw [←same]
    exact (permutationFabric h d).fixedAll_symm _ _ x.property.1
  · exact (permutationFabric h d).fixedAll_symm _ _ y.property.1

def fixedEnds (x : Fixed h d × ColumnLayer k) := freeEnds (S:=S) (.inr (.inr (.inl x)))
def sampleEnds (x : Sample S h d × ColumnLayer k) := freeEnds (S:=S) (.inr (.inr (.inr x)))

theorem fixed_fst_card (v : Site h d k) : Fintype.card {e // (fixedEnds S e).1=v}≤1 := by
  apply Fintype.card_le_one_iff.mpr
  intro a b
  have eq : (a.val.1.val.1,a.val.2)=(b.val.1.val.1,b.val.2) := a.2.trans b.2.symm
  exact Subtype.ext (Prod.ext (same_fixed (congrArg (fun z : Site h d k=>z.1) eq)) (congrArg (fun z : Site h d k=>z.2) eq))

theorem fixed_snd_card (v : Site h d k) : Fintype.card {e // (fixedEnds S e).2=v}≤1 := by
  apply Fintype.card_le_one_iff.mpr
  intro a b
  have eq : (a.val.1.val.2,a.val.2)=(b.val.1.val.2,b.val.2) := a.2.trans b.2.symm
  exact Subtype.ext (Prod.ext (same_fixed_right (congrArg (fun z : Site h d k=>z.1) eq)) (congrArg (fun z : Site h d k=>z.2) eq))

private abbrev Token (h d k : ℕ) := (Σt : StageAt h d,(stageAt h d t).Group × Fin (stageAt h d t).span) × ColumnLayer k

private def socket (output : Bool) : Token h d k ↪ Site h d k :=
  let side (m : ℕ) : Fin m ↪ Fin m ⊕ Fin m :=
    if output then Function.Embedding.inr else Function.Embedding.inl
  let stage : (Σt : StageAt h d,(stageAt h d t).Group × Fin (stageAt h d t).span) ↪ StageColumns h d :=
    (Function.Embedding.refl _).sigmaMap (fun t=>(Function.Embedding.refl _).prodMap (side (stageAt h d t).span))
  (stage.trans stageColumnsIntoPayload).prodMap (Function.Embedding.refl _)

private abbrev Out (z : Token h d k) := {i : Fin (stageAt h d z.1.1).span //
    i∈S.rows (stageAt h d z.1.1).span z.1.2.2}
private abbrev In (z : Token h d k) := {o : Fin (stageAt h d z.1.1).span //
    z.1.2.2∈S.rows (stageAt h d z.1.1).span o}

private def outgoing : (Sample S h d × ColumnLayer k) ≃ Σ z : Token h d k, Out S z where
  toFun := fun ⟨⟨t,g,o,i⟩,l⟩=>⟨(⟨t,g,o⟩,l),i⟩
  invFun := fun ⟨⟨⟨t,g,o⟩,l⟩,i⟩=>(⟨t,g,o,i⟩,l)
  left_inv _:=rfl
  right_inv _:=rfl

private def incoming : (Sample S h d × ColumnLayer k) ≃ Σ z : Token h d k, In S z where
  toFun := fun ⟨⟨t,g,o,i⟩,l⟩=>⟨(⟨t,g,i.val⟩,l),⟨o,i.2⟩⟩
  invFun := fun ⟨⟨⟨t,g,i⟩,l⟩,o⟩=>(⟨t,g,o.val,⟨i,o.2⟩⟩,l)
  left_inv _:=rfl
  right_inv _:=rfl

private def selectField {T : Type} {B : T→Type} (t : T) : {e : Σ t,B t // e.1=t} ↪ B t where
  toFun e:=e.2 ▸ e.val.2
  inj' := by
    rintro ⟨⟨i,x⟩,hx⟩ ⟨⟨j,y⟩,hy⟩ eq
    change i=t at hx
    change j=t at hy
    subst i
    subst j
    change x=y at eq
    cases eq
    rfl

private theorem restrict {T E C : Type} [Fintype E] {B : T→Type} [∀t,Fintype (B t)]
    (labels : E≃Σ t,B t) (loc : T ↪ C) (endAt : E→C) (law : ∀e,endAt e=loc (labels e).1)
    {deg : ℕ} (cap : ∀t,Fintype.card (B t)≤deg) (v : C) : Fintype.card {e // endAt e=v}≤deg := by
  classical
  by_cases hv : ∃ t,loc t=v
  · obtain ⟨t,rfl⟩:=hv
    let label : {e // endAt e=loc t} ↪ {z : Σ t,B t // z.1=t} :=
      ⟨fun e=>⟨labels e.val,loc.injective ((law e.val).symm.trans e.2)⟩,
        fun _ _ eq=>Subtype.ext (labels.injective (congrArg Subtype.val eq))⟩
    exact (Fintype.card_le_of_embedding (label.trans (selectField t))).trans (cap t)
  · let : IsEmpty {e // endAt e=v} := ⟨fun e=>hv ⟨(labels e.val).1,(law e.val).symm.trans e.2⟩⟩
    simp

theorem sample_fst_card (v : Site h d k) : Fintype.card {e // (sampleEnds S e).1=v}≤S.degree := by
  refine restrict (outgoing S) (socket true) (fun e=>(sampleEnds S e).1) ?_ ?_ v
  · rintro ⟨⟨t,g,o,i⟩,l⟩;rfl
  · intro z
    let ns:=(S.rows (stageAt h d z.1.1).span z.1.2.2).toFinset
    let embed : Out S z ↪ ns := ⟨fun i=>⟨i.val,List.mem_toFinset.mpr i.2⟩,
      fun _ _ eq=>Subtype.ext (congrArg (fun u : ns=>u.val) eq)⟩
    exact (Fintype.card_le_of_embedding embed).trans ((Fintype.card_coe ns).le.trans
      ((List.toFinset_card_le _).trans (S.out_degree ..)))

theorem sample_snd_card (v : Site h d k) : Fintype.card {e // (sampleEnds S e).2=v}≤S.degree := by
  refine restrict (incoming S) (socket false) (fun e=>(sampleEnds S e).2) ?_ ?_ v
  · rintro ⟨⟨t,g,o,i⟩,l⟩;rfl
  · intro z
    let ns:=Finset.univ.filter (fun o=>z.1.2.2∈S.rows (stageAt h d z.1.1).span o)
    let embed : In S z ↪ ns := ⟨fun o=>⟨o.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,o.2⟩⟩,
      fun _ _ eq=>Subtype.ext (congrArg (fun u : ns=>u.val) eq)⟩
    exact (Fintype.card_le_of_embedding embed).trans ((Fintype.card_coe ns).le.trans (S.in_degree ..))

end
end Hierarchy.ProbeStage.CoreBoard

end OAI
