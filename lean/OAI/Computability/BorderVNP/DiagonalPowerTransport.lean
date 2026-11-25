import OAI.Computability.BorderVNP.DiagonalPowerSites
import OAI.Computability.BorderVNP.ShortenSeedIntervalsNetwork
import OAI.Computability.BorderVNP.PackedSubdivision
import OAI.Computability.BorderVNP.CrossingParallel

/-! # Transporting the original unary sites through public rewiring -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening
open scoped BigOperators Classical

variable {D b m : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
    {Team Param Gadget : Type*} {tags : N.Tables (Entry Param Gadget)}

/-- Boolean factors carry no powers of the parse parameters. -/
theorem guard_noPower (ok : Prop) [Decidable ok] :
    (counters (if ok then (1 : Entry Param Gadget) else 0)).1 = 0 := by
  split <;> rfl

/-- An entire packed product of scalar gadget entries has zero parameter tally. -/
theorem scalar_product_noPower {I : Type*} [Fintype I] (position : I → Gadget) :
    (counters (∏ i, gadget (Param := Param) (position i))).1 = 0 := by
  rw [counters_prod (fun i => gadget (Param := Param) (position i)) (fun _ => WithZero.coe_ne_zero)]
  simp [gadget]

/-- All three kinds of local box in a profile preserve the zero parameter
tally. The center and terminals check the shared selector, while the bank
accumulates gadget counts over the selected copies. -/
theorem profile_noPower {E : Type*} [Field E] (e : PaidIdentity E D m)
    (pos : e.Entry → Gadget) (j : ℕ) (h : Fin e.count → ℕ) (first : Fin D × Bool)
    (v : (e.profile j h).Site) (a x) :
    (counters (profileTags (Param := Param) e pos j h first v a x)).1 = 0 := by
  rcases v with ⟨⟩ | u | ⟨k,w⟩
  · exact guard_noPower _
  · exact guard_noPower _
  · exact scalar_product_noPower (I := Fin (h k)) _

namespace PowerSites

variable (sites : PowerSites Team Param Gadget b N tags)

/-- Replacing a bundle of cables by an arbitrary network of scalar factors
preserves the injection of the original unary sites. The claim uses
independent incident inputs even for the two ends of a cut cable. -/
noncomputable def cutSew (S : Finset N.Edge)
    (G : Network D (N.CutPorts S) (N.cutWidths S)) (inner : G.Tables (Entry Param Gadget))
    (hzero : ∀ v z x, (counters (inner v z x)).1 = 0) :
    PowerSites Team Param Gadget b ((N.cut S).sew G)
      ((N.cut S).sewTables G (N.cutTables S tags) inner) where
  site := sites.site.trans Function.Embedding.inl
  named w _ _ := sites.named w _ _
  other v hv z x := by
    rcases v with old | new
    · apply sites.other old _ _ _
      rintro ⟨w,rfl⟩
      exact hv ⟨w,rfl⟩
    · exact hzero new _ _

/-- Splitting a wire into its ordered bands changes only the lookup
of a local input word. The surviving unary vertices retain their names. -/
noncomputable def bands {J : Type} [Fintype J] (label : ∀ e, Fin (N.width e) → J) :
    PowerSites Team Param Gadget b (N.bands label) (N.bandTables label tags) where
  site := sites.site
  named w _ _ := sites.named w _ _
  other v hv _ _ := sites.other v hv _ _

/-- Adding intermediate sites on routed cables creates only equality guards. -/
noncomputable def subdivision (routes : Network.WireRoutes N) :
    PowerSites Team Param Gadget b (N.subdivide routes) (N.subdivideTables routes tags) where
  site := sites.site.trans Function.Embedding.inl
  named w _ _ := sites.named w _ _
  other v hv z x := by
    rcases v with old | new
    · apply sites.other old _ _ _
      rintro ⟨w,rfl⟩
      exact hv ⟨w,rfl⟩
    · exact guard_noPower _

end PowerSites

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
