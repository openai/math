import OAI.Computability.BorderVNP.PackedFrozenFormats
import OAI.Computability.BorderVNP.PackedInheritedNamedWidthRead

/-! # Geometry, both width fields and immutable record image of an attained named node -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited Packing.Inherited.FrozenTape
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m b k last high w np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {path : SourcePath b e h H ν} {V E cap : ℕ → ℕ}
    {Extra : ℕ → Type*} {keep : ∀ j,path.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
    {nodes : ∀ i : Fin b,path.Node last high V E w k i} (r : path.NamedRun last high V E w cap keep hk nodes)
    (header : WorkWords.Ports np) (leaf : P ↪ Fin np) (bound : ℕ → ℕ) (j : ℕ) (S : Format)
    (a : NamedState.Admissible (path.NamedGood last high V E w cap keep) j)
    (programs : Site.Programs a.val.placed.pack.layout)
    (y : S.Output (path.StatePins last high V E w j) (V j) w w → Bool)

/-- The complete saved public valuation and its actual family of private programs. -/
structure Read : Prop where
  /-- True selected geometry, both private width columns, original port attachments and tile loads. -/
  widths : WidthRead header leaf bound j a programs (y ∘ Sum.inl)
  /-- All and only the actual site programs' public marked record fields at their saved names. -/
  tape : S.schema.Image (y ∘ Sum.inr) (a.val.names.sites.trans Fin.valEmbedding) (fun v => (programs v).program)

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
