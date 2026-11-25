import OAI.Hierarchy.ProbeCoreSlots

namespace OAI
/-! # Linear size of the actual public core catalogue -/

namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe
open scoped Classical BigOperators
noncomputable section

/-- Each physical fixed connector is counted once, including the two exterior
banks. The source column determines the other side of the public matching. -/
theorem fixed_count (h d : ℕ) : Fintype.card (Fixed h d)≤Fintype.card (Columns h d) := by
  apply Fintype.card_le_of_injective (fun e : Fixed h d=>e.val.1)
  intro e f same
  apply Subtype.ext
  apply Prod.ext same
  apply (fabricBoard h d).injective
  apply (permutationFabric h d).all_fixed_unique (fabricBoard h d f.val.1) _ _ _ f.property.1
  simpa only [←same] using e.property.1

private theorem port_degree (S : PurchaseSampler) (m : ℕ) (o : Fin m) :
    Fintype.card {i : Fin m // i∈S.rows m o}≤ S.degree := by
  let v := (S.rows m o).toFinset
  let e : {i : Fin m // i∈S.rows m o} ↪ v :=
    ⟨fun x=>⟨x.val,List.mem_toFinset.mpr x.property⟩,fun _ _ eq=>Subtype.ext (congrArg (fun y : v=>y.val) eq)⟩
  exact (Fintype.card_le_of_injective e e.injective).trans
    ((Fintype.card_coe v).le.trans ((S.rows m o).toFinset_card_le.trans (S.out_degree m o)))

theorem sample_count (S : PurchaseSampler) (h d : ℕ) (hd : 1≤d) :
    Fintype.card (Sample S h d)≤(Stages h d)*(4^(rounds d+1)*2^h)*S.degree := by
  let cap := 4^(rounds d+1)*2^h
  have one (t : StageAt h d) :
      Fintype.card ((stageAt h d t).Group × (Σ o : Fin (stageAt h d t).span,
        {i : Fin (stageAt h d t).span // i∈S.rows (stageAt h d t).span o})) ≤ cap*S.degree := by
    let s := stageAt h d t
    have area : Fintype.card s.Group*s.span ≤ cap :=
      (template_dyadic (h:=h) hd s (List.get_mem ..)).2
    rw [Fintype.card_prod,Fintype.card_sigma]
    calc
      _ ≤ Fintype.card s.Group*(∑ _o : Fin s.span,S.degree) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun o _=>port_degree S s.span o))
      _ = Fintype.card s.Group*s.span*S.degree := by simp [Nat.mul_assoc]
      _ ≤ cap*S.degree := Nat.mul_le_mul_right _ area
  change Fintype.card (Σ t : StageAt h d, _) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _t : StageAt h d,cap*S.degree := Finset.sum_le_sum (fun t _=>one t)
    _ = _ := by simp [cap,Stages,StageAt,Nat.mul_assoc]

/-- Total core edge records are linear in the number of routing demands,
with an explicit factor independent of h and of the permutation. -/
theorem edge_count (S : PurchaseSampler) (d k : ℕ) (hd : 1≤d) :
    let N := 18*(d-1)+1
    let cap := 4^(rounds d+1)
    let layers := 1+2*k
    let columns := 2+2*N*cap
    ∀ h : ℕ, Fintype.card (Edges S h d k) ≤
      (columns*(2*k+4*k*k+layers)+(N*cap*S.degree+N)*layers)*2^h := by
  intro N cap layers columns h
  let π := Equiv.refl (Fin (2^h))
  have lay := (advisedRoute h d π).layer_shapes
  have num : Stages h d=N :=
    (show (advisedRoute h d π).layers.length=Stages h d by
      simpa only [List.length_map] using congrArg List.length lay).symm.trans (advised_length h d π)
  have col : Fintype.card (Columns h d)≤columns*2^h := calc
    _ ≤ 2*2^h+2*(Stages h d)*(cap*2^h) := payloadColumns_card_le h d hd
    _ = _ := by rw [num];dsimp [columns];ring
  have axes : Fintype.card {a : Fin k × Fin k // a.1<a.2}≤k*k := by
    simpa using Fintype.card_le_of_injective
      (fun a : {z : Fin k × Fin k // z.1<z.2} => a.val) Subtype.val_injective
  have fix := (fixed_count h d).trans col
  have sam := sample_count S h d hd
  rw [num] at sam
  have chan : Fintype.card (ColumnLayer k)=layers := by simp [ColumnLayer,layers,Nat.mul_comm,add_comm]
  simp only [Edges,CoreRow,Free,Radius,Cross,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    Fintype.card_bool,chan,num]
  change _ + _ + _ ≤ _
  calc
    _ ≤ columns*2^h*(k*2) +
        (columns*2^h*((k*k)*(2*2))+(columns*2^h*layers + N*(cap*2^h)*S.degree*layers)) +
        (2^h*N)*layers := by
      dsimp only [cap] at *
      gcongr <;> simpa only [Columns,PayloadColumns,Fintype.card_sum,Fintype.card_fin] using col
    _ = _ := by dsimp only [layers];ring

end
end Hierarchy.ProbeStage.CoreBoard

end OAI
