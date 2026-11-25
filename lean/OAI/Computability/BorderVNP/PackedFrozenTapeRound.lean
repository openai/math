import OAI.Computability.BorderVNP.PackedFrozenTapeSections
import OAI.Computability.BorderVNP.CellPacketGeometryBankBirth

/-! # A shortening node's complete immutable public tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open CellSparse Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open BankJoint InheritedBank InheritedProfile
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P A : Type} [Fintype P] {bits : P → ℕ} [Fintype A] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
variable (first : Fin D × Bool) (q : Counts e p bin perm) (binName : A → ℕ) (position : e.Entry → ℕ)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable {ns ne np : ℕ} (siteID : (G e p bin perm positive first q).Site ↪ Fin ns)
variable (edgeID : (G e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)

/-- Existing history at a retained site. Seed sites start at the current stage. -/
def carriedRows : SiteShape e p A → List Record := Sum.elim (fun v => (old v).rows) (fun _ => [])

/-- New interval rows at the old endpoint, in the physical cut order. -/
def layerRows : SiteShape e p A → List Record :=
  Sum.elim (fun v => (cuts v).map (Slice.record (old v))) (fun _ => [])

/-- Main intrinsic row block of a newly inserted origin, terminal or paid site. -/
noncomputable def birthRows : SiteShape e p A → List Record :=
  Sum.elim (fun _ => []) (fun z => emitted e first (relativeRaw e p bin perm positive first q z.1 edgeID portID) z.2)

/-- A terminal's compact gathered-hook rows follow its main profile checks. -/
noncomputable def terminalRows : SiteShape e p A → List Record
  | .inr ⟨a,.inr (.inl t)⟩ => hookRows e p bin perm positive first q a siteID edgeID portID binName t
  | _ => []

local notation3 "tapes₀" => roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts

/-- Every site in the genuine sewn branch has exactly these four chronological
blocks. Old choices, paid-box rows and the separate clipped terminal checks
retain their physical order. -/
theorem round_rows (v : SiteShape e p A) :
    carriedRows e p old v ++ (layerRows e p old cuts v ++
      (birthRows e p bin perm positive first q edgeID portID v ++
        terminalRows e p bin perm positive first q binName siteID edgeID portID v)) = (tapes₀ v).rows := by
  rcases v with v | ⟨a,⟨⟩ | t | ⟨b,v⟩⟩
  · simp [carriedRows,layerRows,birthRows,terminalRows,roundSites,Site.retain_rows]
  · have he := profile_emitted e p bin perm positive first q siteID edgeID portID a (.inl ())
    simpa [carriedRows,layerRows,birthRows,terminalRows,roundSites,originSite,Site.rows,profileNode] using he
  · have he := profile_emitted e p bin perm positive first q siteID edgeID portID a (.inr t)
    simpa [carriedRows,layerRows,birthRows,terminalRows,roundSites,terminalSite,Site.rows,profileNode] using
      congrArg (· ++ hookRows e p bin perm positive first q a siteID edgeID portID binName t) he
  · simpa [carriedRows,layerRows,birthRows,terminalRows,roundSites] using
      PaidSite.relative_emitted e p bin perm positive first q a b v edgeID portID position

section Joint

variable {R₀ R₁ R₂ R₃ B₀ B₁ B₂ B₃ σ : Type*} [Fintype σ]
variable [Fintype R₀] [Fintype R₁] [Fintype R₂] [Fintype R₃]
variable [Fintype B₀] [Fintype B₁] [Fintype B₂] [Fintype B₃]
variable (S₀ : Schema R₀ B₀) (S₁ : Schema R₁ B₁) (S₂ : Schema R₂ B₂) (S₃ : Schema R₃ B₃)
variable {d : ℕ} (f₀ : Frame σ (Pins R₀ B₀ d)) (f₁ : Frame σ (Pins R₁ B₁ d))
variable (f₂ : Frame σ (Pins R₂ B₂ d)) (f₃ : Frame σ (Pins R₃ B₃ d))

/-- Fixed schema of the carried, newly clipped, seed-main and terminal-hook arrays. -/
def nodeSchema := S₀.append (S₁.append (S₂.append S₃))

/-- Join the four real emitters on their common source table. This frame is independent
of the geometric branch and retains both presence and complete scalar payloads. -/
noncomputable def nodeFrame := appendFrame f₀ (appendFrame f₁ (appendFrame f₂ f₃))

/-- Each component gate list is charged once. Chronological wiring adds no gates. -/
theorem nodeFrame_size : (nodeFrame f₀ f₁ f₂ f₃).size = f₀.size + (f₁.size + (f₂.size+f₃.size)) := by
  simp only [nodeFrame,appendFrame_size]

/-- The owner keys of the public frame can be any common injection of the real sites.
Physical operand addresses still use the actual cable and site ordinals. -/
theorem node_image_key (key : SiteShape e p A ↪ ℕ) (x : σ → Bool)
    (h₀ : S₀.Section (f₀.eval x) key (carriedRows e p old))
    (h₁ : S₁.Section (f₁.eval x) key (layerRows e p old cuts))
    (h₂ : S₂.Section (f₂.eval x) key (birthRows e p bin perm positive first q edgeID portID))
    (h₃ : S₃.Section (f₃.eval x) key
      (terminalRows e p bin perm positive first q binName siteID edgeID portID)) :
    (nodeSchema S₀ S₁ S₂ S₃).Image ((nodeFrame f₀ f₁ f₂ f₃).eval x) key tapes₀ := by
  have z := appendFrame_section S₂ S₃ f₂ f₃ x key _ _ h₂ h₃
  have y := appendFrame_section S₁ (S₂.append S₃) f₁ (appendFrame f₂ f₃) x key _ _ h₁ z
  have whole := appendFrame_section S₀ (S₁.append (S₂.append S₃)) f₀ (appendFrame f₁ (appendFrame f₂ f₃)) x key _ _ h₀ y
  exact Schema.Section.image _ whole tapes₀ (round_rows e p bin perm positive first q binName position siteID edgeID portID old cuts)

/-- On the shared physical source, the four actual public sections form a complete
image of the persistent site programs on this histogram. -/
theorem node_image (x : σ → Bool)
    (h₀ : S₀.Section (f₀.eval x) (siteID.trans Fin.valEmbedding) (carriedRows e p old))
    (h₁ : S₁.Section (f₁.eval x) (siteID.trans Fin.valEmbedding) (layerRows e p old cuts))
    (h₂ : S₂.Section (f₂.eval x) (siteID.trans Fin.valEmbedding) (birthRows e p bin perm positive first q edgeID portID))
    (h₃ : S₃.Section (f₃.eval x) (siteID.trans Fin.valEmbedding)
      (terminalRows e p bin perm positive first q binName siteID edgeID portID)) :
    (nodeSchema S₀ S₁ S₂ S₃).Image ((nodeFrame f₀ f₁ f₂ f₃).eval x) (siteID.trans Fin.valEmbedding) tapes₀ :=
  node_image_key e p bin perm positive first q binName position siteID edgeID portID old cuts
    S₀ S₁ S₂ S₃ f₀ f₁ f₂ f₃ (siteID.trans Fin.valEmbedding) x h₀ h₁ h₂ h₃

end Joint

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
