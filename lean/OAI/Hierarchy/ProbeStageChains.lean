import OAI.Hierarchy.ProbeSampler
import OAI.Hierarchy.ProbeStagePorts

namespace OAI
/-! # Tile-disjoint chains on the actual input/output rows of each subdivision stage -/

namespace Hierarchy.ProbeStage.Tiles
open AdaptiveProbe
noncomputable section

variable {R G : Type*} {m : ℕ} (stage : Tiles R G m)

def inputPort (g : G) : {r : R // stage.group r=g} ↪ Fin m :=
  ⟨fun r => stage.input r.val,fun r s eq => Subtype.ext
    (stage.input_inj (Prod.ext (r.property.trans s.property.symm) eq))⟩

def outputPort (g : G) : {r : R // stage.group r=g} ↪ Fin m :=
  ⟨fun r => stage.output r.val,fun r s eq => Subtype.ext
    (stage.output_inj (Prod.ext (r.property.trans s.property.symm) eq))⟩

/-- The sampler lists are shared by all stages of a given size and independent of every
permutation or mark. The bound applies to each unused set for its actual tile arrows. -/
theorem sampler_family {δ : ℝ} (hd : 0<δ) :
    ∃ D : ℕ, ∀ m : ℕ, 0 < m → ∃ next : Fin m → List (Fin m),
      (∀ i, (next i).length ≤ D) ∧
      (∀ j, (Finset.univ.filter fun i => j ∈ next i).card ≤ D) ∧
      ∀ (R G : Type) [Fintype R] [DecidableEq G] (stage : Tiles R G m) (g : G)
        (a H : ℕ) (_ha : 0 < a) (_hH : 0 < H), δ*m ≤ a →
        ∀ left : Finset {r : R // stage.group r=g}, H*(2*a) ≤ left.card →
        ∃ walk : Fin H ↪ {r : R // stage.group r=g}, (∀ j,walk j∈left) ∧
          ∀ j : ℕ, ∀ hj : j+1 < H, stage.input (walk ⟨j+1,hj⟩).val ∈
            next (stage.output (walk ⟨j,by omega⟩).val) := by
  classical
  obtain ⟨D,graphs⟩ := exists_group_samplers hd
  refine ⟨D,fun m hm => ?_⟩
  obtain ⟨next,row,col,cross⟩ := graphs m hm
  refine ⟨next,row,col,?_⟩
  intro R G _ _ stage g a H ha hH scale left plenty
  have mix : SamplerMixes (fun x y => y ∈ next x) a := cross (Equiv.refl _) a scale
  exact exists_sampler_chain a H ha hH (mix.on_tiles (stage.outputPort g) (stage.inputPort g)) left plenty

end
end Hierarchy.ProbeStage.Tiles

end OAI
