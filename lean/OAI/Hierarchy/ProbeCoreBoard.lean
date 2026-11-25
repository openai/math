import OAI.Hierarchy.ProbeFabricBoard
import OAI.Hierarchy.ProbeFixedNeighbors
import OAI.Hierarchy.ProbeCorePayment
import OAI.Hierarchy.ProbeAdvisedCost

namespace OAI
/-! # The core links of the advised routing board and their initial charge -/

namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe Filter
open scoped BigOperators Classical
noncomputable section

abbrev Columns (h d : ℕ) := PayloadColumns h d
abbrev Site (h d k : ℕ) := ColumnSite (Columns h d) k
abbrev Stages (h d : ℕ) := (permutationFabric h d).shapes.length

/-- Each public fixed identification occurs once, with a canonical orientation. -/
abbrev Fixed (h d : ℕ) := {e : Columns h d × Columns h d //
  (permutationFabric h d).fixedAll (fabricBoard h d e.1) (fabricBoard h d e.2) ∧
    Fintype.equivFin (Columns h d) e.1 < Fintype.equivFin (Columns h d) e.2}

/-- A sampler edge is present for every actual neighbor at the stage's common
group span. Duplicate ROM occurrences give the same physical link. -/
abbrev Sample (S : PurchaseSampler) (h d : ℕ) := Σ t : StageAt h d,
  (stageAt h d t).Group × (Σ o : Fin (stageAt h d t).span,
    {i : Fin (stageAt h d t).span // i ∈ S.rows (stageAt h d t).span o})

abbrev Radius (h d k : ℕ) := Columns h d × (Fin k × Bool)
abbrev Cross (h d k : ℕ) := Columns h d × ({a : Fin k × Fin k // a.1<a.2} × (Bool × Bool))
abbrev Free (S : PurchaseSampler) (h d k : ℕ) :=
  Radius h d k ⊕ (Cross h d k ⊕ ((Fixed h d × ColumnLayer k) ⊕ (Sample S h d × ColumnLayer k)))
abbrev Edges (S : PurchaseSampler) (h d k : ℕ) :=
  CoreRow (Free S h d k) (Fin (2^h)) (Stages h d) k

def freeLength {S : PurchaseSampler} {h d k : ℕ} (M : ℝ) : Free S h d k → ℝ
  | .inl _ => M
  | .inr (.inl _) => ⌈Real.sqrt 2*M⌉
  | .inr (.inr _) => 0

def inputCol {h d : ℕ} (t : StageAt h d) (g : (stageAt h d t).Group)
    (i : Fin (stageAt h d t).span) : Columns h d := .inr (.inl ⟨t,g,.inl i⟩)

def outputCol {h d : ℕ} (t : StageAt h d) (g : (stageAt h d t).Group)
    (i : Fin (stageAt h d t).span) : Columns h d := .inr (.inl ⟨t,g,.inr i⟩)

def freeEnds {S : PurchaseSampler} {h d k : ℕ} : Free S h d k → Site h d k × Site h d k
  | .inl (c,axis) => ((c,none),(c,some axis))
  | .inr (.inl (c,a,s,u)) => ((c,some (a.val.1,s)),(c,some (a.val.2,u)))
  | .inr (.inr (.inl (e,l))) => ((e.val.1,l),(e.val.2,l))
  | .inr (.inr (.inr (⟨t,g,⟨o,i⟩⟩,l))) => ((outputCol t g o,l),(inputCol t g i.val,l))

def ends {S : PurchaseSampler} {h d k : ℕ} (π : Equiv.Perm (Fin (2^h))) :
    Edges S h d k → Site h d k × Site h d k
  | .inl e => freeEnds e
  | .inr ((p,t),l) =>
    let a := advisedStage h d π t
    ((inputCol t (a.group p) (a.input p),l),(outputCol t (a.group p) (a.output p),l))

/-- This sum includes every fixed and sampler edge, each column's radius links
and diagonals, and one tile per routed record at each stage and layer. -/
theorem invoice (S : PurchaseSampler) (h d k : ℕ) (p q Q Λ t M : ℝ) (ht : 0<t) :
    (∑ e : Edges S h d k, Λ*capacity p q Q (coreScale t e) (coreLength (freeLength M) e)) =
      (2^h:ℕ)*(Λ*(1+2*k)*(Stages h d)*t^p) := by
  simpa only [Fintype.card_fin] using
    (core_capacity_bill (P:=Fin (2^h)) (Stages h d) k p q Q Λ t ht
      (freeLength (S:=S) (h:=h) (d:=d) (k:=k) M))

/-- The actual CT stage count fixes an affordable dyadic width simultaneously
for all board heights, permutations, public fixed matchings and sampler rows. -/
theorem affordable (k : ℕ) {p σ Λ : ℝ} (hp : 1<p) (hσ : 0<σ) (hΛ : 0<Λ) :
    ∀ᶠ W : ℕ in atTop, ∀ (h : ℕ) (S : PurchaseSampler) (M q Q : ℝ),
      let d := 2^W
      (∑ e : Edges S h d k, Λ*capacity p q Q (coreScale (dyadicScale W) e)
        (coreLength (freeLength M) e)) ≤ (2^h:ℕ) := by
  filter_upwards [affordable_advised hp hσ hΛ (show (0:ℝ)<1 by norm_num) k] with W paid
  intro h S M q Q d
  have ht : 0<dyadicScale W := by unfold dyadicScale; positivity
  rw [invoice S h d k p q Q Λ (dyadicScale W) M ht]
  let π := Equiv.refl (Fin (2^h))
  have counts := (advisedRoute h d π).layer_shapes
  have same : (advisedRoute h d π).layers.length=Stages h d := by
    simpa only [List.length_map] using congrArg List.length counts
  have fee := (paid h π).2.1
  change Λ*(1+2*k)*(advisedRoute h d π).layers.length*(dyadicScale W)^p≤1 at fee
  rw [same] at fee
  simpa only [mul_one] using (mul_le_mul_of_nonneg_left fee (Nat.cast_nonneg (α:=ℝ) (2^h)))

end
end Hierarchy.ProbeStage.CoreBoard

end OAI
