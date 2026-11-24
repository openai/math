import OAI.Computability.VPVNP.LiveWordCapacity

/-!
# Site-count powers in the live program's workspace layout

The physical and virtual site counts are the only power-of-two operations in
these address expressions. Fixed natural powers, such as the label bound and
the evaluator radius, are compiled as iterated word multiplications.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram

local macro "site_expr" : tactic => `(tactic| repeat' first
  | assumption
  | exact True.intro
  | apply PublicExpr.SitePowers.natPow
  | exact Or.inl rfl
  | exact Or.inr rfl
  | constructor)

namespace Constants

@[simp] theorem states_sitePowers (c : Constants) : c.states.SitePowers := by site_expr

@[simp] theorem grammarLabels_sitePowers (c : Constants) : c.grammarLabels.SitePowers := by
  have := c.states_sitePowers
  site_expr

@[simp] theorem labels_sitePowers (c : Constants) : c.labels.SitePowers := by
  have := c.grammarLabels_sitePowers
  site_expr

@[simp] theorem height_sitePowers (c : Constants) : c.height.SitePowers := by site_expr

@[simp] theorem Z_sitePowers (c : Constants) : c.Z.SitePowers := by
  have := c.height_sitePowers
  site_expr

@[simp] theorem radius_sitePowers (c : Constants) : c.radius.SitePowers := by site_expr

@[simp] theorem configWords_sitePowers (c : Constants) : c.configWords.SitePowers := by
  have := c.radius_sitePowers
  site_expr

@[simp] theorem prefixCapacity_sitePowers (c : Constants) : c.prefixCapacity.SitePowers := by site_expr

@[simp] theorem lengths_h_sitePowers (c : Constants) : c.lengths.h.SitePowers := by
  have := c.height_sitePowers
  site_expr

@[simp] theorem lengths_delta_sitePowers (c : Constants) : c.lengths.delta.SitePowers := by site_expr
@[simp] theorem lengths_advice_sitePowers (c : Constants) : c.lengths.advice.SitePowers := by site_expr

@[simp] theorem lengths_e_sitePowers (c : Constants) : c.lengths.e.SitePowers := by
  have := c.labels_sitePowers
  have := c.Z_sitePowers
  site_expr

@[simp] theorem lengths_config_sitePowers (c : Constants) : c.lengths.config.SitePowers := by
  have := c.configWords_sitePowers
  site_expr

end Constants

namespace Layout

@[simp] theorem stageTag_sitePowers : stageTag.SitePowers := by site_expr

@[simp] theorem header_sitePowers : header.SitePowers := by
  have := stageTag_sitePowers
  site_expr

@[simp] theorem descriptor_sitePowers (c : Constants) : (descriptor c).SitePowers := by
  have := header_sitePowers
  have := c.lengths_h_sitePowers
  have := c.lengths_delta_sitePowers
  have := c.lengths_advice_sitePowers
  have := c.lengths_e_sitePowers
  have := c.lengths_config_sitePowers
  site_expr

@[simp] theorem counter_sitePowers (c : Constants) : (counter c).SitePowers := by
  have := descriptor_sitePowers c
  site_expr

@[simp] theorem oldState_sitePowers (c : Constants) : (oldState c).SitePowers := by
  have := counter_sitePowers c
  have := c.labels_sitePowers
  site_expr

@[simp] theorem newState_sitePowers (c : Constants) : (newState c).SitePowers := by
  have := oldState_sitePowers c
  have := c.configWords_sitePowers
  site_expr

@[simp] theorem transitionScratch_sitePowers (c : Constants) : (transitionScratch c).SitePowers := by
  have := newState_sitePowers c
  have := c.configWords_sitePowers
  site_expr

@[simp] theorem adviceFrames_sitePowers (c : Constants) : (adviceFrames c).SitePowers := by
  have := transitionScratch_sitePowers c
  site_expr

@[simp] theorem packedPrefix_sitePowers (c : Constants) : (packedPrefix c).SitePowers := by
  have := adviceFrames_sitePowers c
  site_expr

@[simp] theorem orderMap_sitePowers (c : Constants) : (orderMap c).SitePowers := by
  have := packedPrefix_sitePowers c
  have := c.prefixCapacity_sitePowers
  site_expr

@[simp] theorem shadow_sitePowers (c : Constants) : (shadow c).SitePowers := by
  have := orderMap_sitePowers c
  have := c.labels_sitePowers
  site_expr

@[simp] theorem virtualSiteBits_sitePowers : virtualSiteBits.SitePowers := by
  have := stageTag_sitePowers
  site_expr

@[simp] theorem virtualSiteCount_sitePowers : (PublicExpr.pow2 virtualSiteBits).SitePowers :=
  ⟨virtualSiteBits_sitePowers,Or.inr rfl⟩

@[simp] theorem pairWorkspace_sitePowers (c : Constants) : (pairWorkspace c).SitePowers := by
  have := shadow_sitePowers c
  have := virtualSiteCount_sitePowers
  site_expr

end Layout

end LiveProgram

end VPVNP
end Computability
end OAI
