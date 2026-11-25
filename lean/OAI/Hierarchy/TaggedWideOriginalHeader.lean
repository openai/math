import OAI.Hierarchy.TaggedWideHeaderWires
import OAI.Hierarchy.ProbeFixedWideHostPins
import OAI.Hierarchy.ProbeFixedBroadcastCap
import OAI.Hierarchy.ProbeFixedFundedHeader
import OAI.Hierarchy.TaggedWideInputInverse

namespace OAI
/-! # The physical input of both native programs, including the inverse permutation pass -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory AdaptiveProbe ProbeStage CoreBoard CoreRoute
open Tagged Tagged.WideControlJoin WireTelescope StripChart CatalystArchive
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "D" => 2^v.W
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "V" => v.catalystMarkets P h width
local notation "W" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "o" => wideRouteOrder h D k
local notation "es" => events v.mesh
local notation "L" => (v.wideSelector h width age budget small).format.windows
local notation "slot" => (v.wideSelector h width age budget small).format.slot
variable (S : ℕ) (highSeed : Boot.Tape h (2^v.W))

def wideFixedCPUInput :=
  Boot.header V S (v.wideSignedWords h width stock v.radius (Equiv.refl _) o
    (v.wideFundedRaw h width v.maxBits highSeed))

def wideInverseTarget (π : Equiv.Perm (Row h)) (raw : Bits (CalendarTape.bits slot es)) :=
  Boot.header V S (v.wideSignedWords h width stock v.radius π.symm o
    (v.wideFundedRaw h width v.maxBits ((L).header es raw highSeed)))

private theorem fundedSplit (extent : (A).endAddress v.mesh≤S) (π : Equiv.Perm (Row h))
    (raw : Bits (CalendarTape.bits slot es)) :
    Boot.header V S (v.wideSignedWords h width stock v.radius π o
      (v.wideFundedRaw h width v.maxBits ((L).header es raw highSeed)))=
    Boot.tagRows (fun i=>(π i).val) ((L).header es raw (v.wideFixedCPUInput h width S highSeed)) := by
  have bounds:=v.wide_stock_sizes h width age budget small
  rw [v.wide_funded_raw_header h width age budget small v.maxBits raw highSeed,
    ←v.wide_tag_header_eq h width stock v.radius π o]
  exact v.wide_header_pins h width stock v.radius o _ _ _ _ _ _ S extent bounds.words.addresses bounds.copies
    _ raw (v.wideFundedRaw h width v.maxBits highSeed)

variable {E : Type} (label : Row h×Fin h→E)
local notation "base" => v.wideFixedCPUInput h width S highSeed
local notation "image" => (L).tape es label base
local notation "target" => v.wideInverseTarget h width age budget small S highSeed

/-- Authentic assignments enter the original CT with p⁻¹ in all n rows.
The initial image itself has only ordinary external tag bits, dated private
bits, and fixed public bits, including on non-bijective assignments. -/
theorem wide_tag_inverse_entry (extent : (A).endAddress v.mesh≤S) (low : 2^h≤S)
    (room : S+2*(2^h)<2^W) (e : E→Bool) (q : Bits (CalendarTape.bits slot es))
    (π : Equiv.Perm (Row h)) (auth : ∀i,CalendarTape.WordSlots.exposed label e i=π i) :
    (TagInverse.program W h S).Exec (initialMemory S (image e q)) (initialMemory S (target π q))
      (TagInverse.ticks h) := by
  have back:=v.fundedSplit h width age budget small S highSeed extent π.symm q
  have tag (i : Row h) : image e q i.val=((π i).val:Word W):=by
    simp only [CalendarTape.WordSlots.tape,Boot.tagRows,dite_eq_left i.isLt,auth]
  have inverse (i : Row h) : target π q i.val=((π.symm i).val:Word W):=by
    change (Boot.header _ _ _) _=_
    rw [back]
    simp only [Boot.tagRows,dite_eq_left i.isLt]
  have same (a : ℕ) (after : 2^h≤a) : image e q a=target π q a:=by
    change (Boot.tagRows _ _ a)=(Boot.header _ _ _) a
    rw [back]
    simp only [Boot.tagRows,dite_eq_right (not_lt.mpr after)]
  intro Psz Rsz Ksz machine pc reg pub exit installed publicData config mem enter starts
  exact TagInverse.run h S π _ _ low room tag inverse same machine pc reg pub exit installed publicData
    config mem enter starts

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
