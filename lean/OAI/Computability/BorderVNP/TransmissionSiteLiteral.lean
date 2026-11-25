import OAI.Computability.BorderVNP.TeamSiteProcessor
import OAI.Computability.BorderVNP.TeamContractionWires
import OAI.Computability.BorderVNP.TransmissionInputEntry

/-! # The physical literal of the signed processor, including distributed RAM advice -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM TeamTapeHandoff
open Wires

variable {k reg w r : ℕ}

/-- Prefix consumed after the four startup fields. At the first real processor the
canonical initial frame is supplied by the literal itself. The routing metadata follows. -/
def sitePrefix (pub : Fin k → Word w) (H limit burst : Word w) (start : Frame w reg)
    (j : Fin r) (e n : ℕ) : List Bool :=
  TeamPublicWords.bytes (TeamSite.Layout.parameters pub H limit burst) ++
    [decide (j.val = 0), decide (j.val+1 = r)] ++
    (if j.val = 0 then start.bits else []) ++
    TeamTapeInputRoute.metadataBits n e (w+1) (primary j) (secondary j)

/-- A single public length suffices for all site prefixes, including the optional
initial frame and both possible virtual indices. -/
def prefixCapacity (r k reg w n : ℕ) : ℕ :=
  (k+8)*w + 2 + frameWidth reg w + (2*Nat.clog 2 (n+1)+1) + 2*(2*Nat.clog 2 r+1)+1

/-- The optional frame and optional secondary row each fit in their declared reservation. -/
theorem sitePrefix_length_le (pub : Fin k → Word w) (H limit burst : Word w) (start : Frame w reg)
    (j : Fin r) (e n : ℕ) :
    (sitePrefix pub H limit burst start j e n).length ≤ prefixCapacity r k reg w n := by
  cases h : secondary j <;> by_cases hj : j.val = 0 <;>
    simp [sitePrefix, prefixCapacity, TeamPublicWords.bytes_length, frameWidth,
      TeamTapeInputRoute.metadataBits, TeamTapeInputRoute.sizeBits, TeamTapeInputRoute.secondId,
      TeamTapeInput.digits, Evaluator.InputBank.length_fieldBits, h, hj, Frame.bits_length] <;> omega

/-- Every processor puts its independent advice bit at the same literal offset, after
all startup data. Remaining arbitrary literal bits follow this designated position. -/
def payload {a : ℕ} (pub : Fin k → Word w) (H limit burst : Word w) (start : Frame w reg)
    (j : Fin r) (e n : ℕ) (advice : Bool) (free : Fin a → Bool) : List Bool :=
  let pref := sitePrefix pub H limit burst start j e n
  pref ++ List.replicate (prefixCapacity r k reg w n - pref.length) false ++ [advice] ++ List.ofFn free

/-- The bit reservation and arbitrary free suffix give one common literal width. -/
theorem payload_length {a : ℕ} (pub : Fin k → Word w) (H limit burst : Word w) (start : Frame w reg)
    (j : Fin r) (e n : ℕ) (advice : Bool) (free : Fin a → Bool) :
    (payload pub H limit burst start j e n advice free).length = prefixCapacity r k reg w n+1+a := by
  have h := sitePrefix_length_le pub H limit burst start j e n
  simp [payload]
  omega

/-- The fixed literal position contains the chosen advice bit even when the site
omits one or both of the optional metadata fields. -/
theorem payload_advice {a : ℕ} (pub : Fin k → Word w) (H limit burst : Word w) (start : Frame w reg)
    (j : Fin r) (e n : ℕ) (advice : Bool) (free : Fin a → Bool) :
    (payload pub H limit burst start j e n advice free)[prefixCapacity r k reg w n]? = some advice := by
  let pref := sitePrefix pub H limit burst start j e n
  let cap := prefixCapacity r k reg w n
  have hl : (pref ++ List.replicate (cap-pref.length) false).length = cap := by
    have h := sitePrefix_length_le pub H limit burst start j e n
    simp [cap,pref]; omega
  change (((pref ++ List.replicate (cap-pref.length) false) ++ [advice]) ++ List.ofFn free)[cap]? = _
  rw [List.append_assoc, List.getElem?_append_right hl.le, hl, Nat.sub_self]
  rfl

/-- The exactly sized input to the four-field constructor `entryWiring`. -/
def payloadBits {a : ℕ} (pub : Fin k → Word w) (H limit burst : Word w) (start : Frame w reg)
    (j : Fin r) (e n : ℕ) (advice : Bool) (free : Fin a → Bool) :
    Fin (prefixCapacity r k reg w n+1+a) → Bool :=
  fun i => (payload pub H limit burst start j e n advice free)[i.val]'(by rw [payload_length]; exact i.isLt)

/-- Reading the pinned site-specific fields as one finite bit array recovers their original order. -/
theorem ofFn_payloadBits {a : ℕ} (pub : Fin k → Word w) (H limit burst : Word w) (start : Frame w reg)
    (j : Fin r) (e n : ℕ) (advice : Bool) (free : Fin a → Bool) :
    List.ofFn (payloadBits pub H limit burst start j e n advice free) =
      payload pub H limit burst start j e n advice free := by
  apply List.ext_getElem
  · rw [List.length_ofFn, payload_length]
  · intros; simp [payloadBits]

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
