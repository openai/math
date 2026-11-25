import OAI.Computability.NearSquareRoot.KernelEffectiveMixBankPacket
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct

/-! # Linking the fixed ruler prepass to the generated matrix commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveMixBank

open IntegerMultiplication IntegerMultiplication.Code CommonRegisters GeneratorSyntax
open KernelEffectiveFamily RegisterSelect Filter

variable {H P : Type} [Codec H] [Primcodable P]

/-- A generated list-processing command receives the physically replicated rulers.
The remaining header fields are parked throughout the entire operation. -/
theorem assemble (key : H → Rulers) (hk : Code.Easy key)
    (i o : P → ℕ) (f : P → RowFunction)
    (hfinish : ∀ᶠ R in atTop, Family R (fun p => finish (i p) (o p) (f p))) :
    ∀ᶠ R in atTop, ∃ c : P → Cmd, Effective ltr c ∧
      ∀ p, Within R (c p) ∧ Sound (c p) key (i p) (o p) (f p) := by
  obtain ⟨prep,C,hprep⟩ := prepare key hk
  filter_upwards [within_eventually prep, hfinish, eventually_ge_atTop 3] with R hR hf h₃
  obtain ⟨c,he,hc⟩ := Family.right (Z := H) h₃ hf
  refine ⟨fun p => prep.join (c p), (effective_const ltr prep).join he,fun p => ⟨⟨hR,(hc p).1⟩,?_⟩⟩
  obtain ⟨D,hd⟩ := (hc p).2
  refine ⟨C+D*4+2,fun z env park => ((hprep z env park).join
    (hd (replicated key z) env park)).mono ?_⟩
  have hs := size_replicated key z
  have hb : size (replicated key z)+1 ≤ 4*(expense key z+1) := by omega
  have hn := Nat.mul_le_mul_left D hb
  rw [← Nat.mul_assoc] at hn
  simp only [Nat.add_mul]
  omega

end KernelEffectiveMixBank

end NearSquareRoot
end Computability
end OAI
