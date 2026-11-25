import OAI.Hierarchy.TaggedWideWindowWords
import OAI.Hierarchy.TaggedWideOriginalCutFields

namespace OAI
/-! # The original packed group and scaled socket at the actual frozen-format input -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles Tagged ProtocolRAMFrozenWindow
open ProtocolRAMSupergroupDirectory
open scoped BigOperators Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    {κ A : ℝ} (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
    (cap : ℕ) (dated : WideCPU.Dated (events v.mesh).length) (bits romStart : ℕ)
local notation "l" => v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart
local notation "g" => (WideMemory.dir x.h v.W k v.wideJobs).groups
local notation "H" => WideMemory.H x.h v.W k v.wideJobs
local notation "base" => v.wideGroupROM x dated bits romStart
local notation "first" => v.wideFormatROM x dated bits romStart
local notation "words" => v.wideWindowWords x m ell short u δ ξ cap dated bits romStart

local notation "P" => v.widePlacement x.h x.w
local notation "r" => (P).catalogue.rows
local notation "dst" => CatalystArchive.TerminalLayout.destination (v.wideSignedPage x.h x.w (v.fixedTerminalStock P x.h x.w))

/-- Column zero of the third emitted triple carries the packed group of each
original row. This includes dormant rows and uses the same nine-word output
interval preserved by the terminal pruning run. -/
theorem wideWindow_owner_read {W : ℕ} (i : Fin (m+1)) (raw : Fin r→ ProtocolRAMEmit.Row)
    (source before : Memory W)
    (reported : ∀a,dst≤ a → a< dst+9*r → before a=ProtocolRAMEmit.emitted dst raw source a)
    (room : 3*r<2^W) (j : Fin r) :
    ((l).inputs i).owner.eval before (j.val:Word W)=((raw j).group:Word W) := by
  let gates:=RoleROM.bank (dst+6*r) (3*r)
  change (PruneFlag.field gates 0).eval before (j.val:Word W)=_
  rw [PruneFlag.field_read gates 0 before j (ProtocolRAMPurchaseSampler.lt_span _).le room]
  change before (dst+6*r+3*j.val+0)=_
  rw [reported _ (by omega) (by have := j.isLt; omega)]
  exact (ProtocolRAMEmit.emitted_read dst raw source j 0).2.2

/-- The literal type ROM and the authenticated transport-only width page supply
every numerical input of the native format procedure. -/
theorem wideWindow_input_words {W : ℕ} (i : Fin (m+1)) (seed before : Memory W)
    (old : Fin r→ ProtocolRAMEmit.Row) (fit : ((l).windows i).Limits W old)
    (retain : ∀y,((l).windows i).rom≤ y → y<((l).windows i).adviceEnd → before y=words seed y)
    (width : ∀j : Fin r,((l).inputs i).width.read before ((3*j.val:ℕ):Word W)=
      ((old j).width:Word W)) :
    ((l).windows i).InputWords ((l).windowBase i) ((l).inputs i) old before := by
  let groups:=ProtocolRAMSupergroupDirectory.mount base 1 (Equiv.refl (Fin g)) (packedDirectory g H) seed
  let pre:=PruneFlag.layerAdvice (v.widePruneLayout x) (l).layers groups
  apply ((l).windows i).input_words ((l).windowBase i) ((l).inputs i) before pre old fit _ width
  intro y lo hi
  exact (retain y lo hi).trans
    (v.wideWindowWords_read x m ell short u δ ξ cap dated bits romStart seed i ⟨lo,hi⟩)

private theorem packed_word {W : ℕ} (mem : Memory W) (j : ℕ) (low : j< base+2*span g) :
    words mem j=mount base 1 (Equiv.refl (Fin g)) (packedDirectory g H) mem j := by
  have before : j<(l).layers.base := low
  have small : j< first := before.trans_le (Nat.le_add_right _ _)
  rw [v.wideWindowWords_outside_types x m ell short u δ ξ cap dated bits romStart mem j small]
  change (if (l).layers.base≤ j ∧ j<(l).layers.base+(l).layers.size then _ else _)=_
  rw [ite_eq_right (fun h=>before.not_ge h.1)]

/-- Every purchased format reads the same immutable packed group and the zero offset.
All format tables and the geometric layer page are already installed. -/
theorem wideWindowWords_packed {W : ℕ} (mem : Memory W) (i : Fin (m+1))
    (fit : g≤2^W) (j : Fin g) :
    ((l).inputs i).directory.read (words mem) (j.val:Word W)=(j.val:Word W) ∧
      ((l).inputs i).offset.read (words mem) (j.val:Word W)=0 := by
  let grp := mount base 1 (Equiv.refl (Fin g)) (packedDirectory g H) mem
  have real := resident base 1 (Equiv.refl (Fin g)) (packedDirectory g H) mem fit j
  let z := (j.val:Word W)
  have lt : z.val%span g < span g := Nat.mod_lt _ (Nat.two_pow_pos _)
  change words mem (base+z.val%span g)=_ ∧ words mem (base+span g+z.val%span g)=_
  constructor
  · rw [packed_word v x m ell short u δ ξ cap dated bits romStart mem _ (by omega)]
    exact real.1
  · rw [packed_word v x m ell short u δ ξ cap dated bits romStart mem _ (by omega)]
    have offsetRead := real.2
    change grp (base+span g+z.val%span g)=(((packedDirectory g H).base j*1:ℕ):Word W) at offsetRead
    exact offsetRead.trans (by rw [show (packedDirectory g H).base j=0 from rfl, Nat.zero_mul, Nat.cast_zero])

/-- A later filter may use private working memory while retaining the two immutable group pages. -/
theorem wideWindowWords_packed_at {W : ℕ} (mem out : Memory W) (i : Fin (m+1)) (fit : g≤2^W)
    (keep : ∀a,base≤ a → a< base+2*span g → out a=words mem a) (j : Fin g) :
    ((l).inputs i).directory.read out (j.val:Word W)=(j.val:Word W) ∧
      ((l).inputs i).offset.read out (j.val:Word W)=0 := by
  let z := (j.val:Word W)
  have lt : z.val%span g < span g := Nat.mod_lt _ (Nat.two_pow_pos _)
  change out (base+z.val%span g)=_ ∧ out (base+span g+z.val%span g)=_
  have posted := v.wideWindowWords_packed x m ell short u δ ξ cap dated bits romStart mem i fit j
  change words mem (base+z.val%span g)=(j.val:Word W) ∧
    words mem (base+span g+z.val%span g)=(0:Word W) at posted
  exact ⟨(keep _ (by omega) (by omega)).trans posted.1,
    (keep _ (by omega) (by omega)).trans posted.2⟩

/-- The packed owner page and the two terminal scans provide exactly the grouped
rows and physical subslot starts required by the original positive-board anchor. -/
theorem wideWindow_live_sources {W : ℕ} (mem before : Memory W) (i : Fin (m+1))
    (old : Fin ((l).windows i).N→ ProtocolRAMEmit.Row)
    (limits : ((l).windows i).Limits W old)
    (keep : ∀a,base≤ a → a< base+2*span g → before a=words mem a)
    (port : Bool→ Fin ((l).windows i).N→ Fin H)
    (owner : ∀j,0< ProtocolRAMReportedPorts.pieces old x.w j → (old j).group< g)
    (groupRead : ∀j,0< ProtocolRAMReportedPorts.pieces old x.w j →
      ((l).inputs i).owner.eval before (j.val:Word W)=((old j).group:Word W))
    (portsRead : ∀side (j : ProtocolRAMPackedPlacement.Live old x.w),
      (if side then ((l).inputs i).right else ((l).inputs i).left).read before (j.val.val:Word W)=
        ((port side j.val).val*2^ell:ℕ)) :
    (∀j,0< ProtocolRAMReportedPorts.pieces old x.w j →
       ((((l).windows i).rows ((l).inputs i) before old) j).group=(old j).group) ∧
    ∀side (j : ProtocolRAMPackedPlacement.Live old x.w),
       ((l).windows i).starts ((l).inputs i) before side j.val=(port side j.val).val*2^ell := by
  have groupsFit : g≤2^W := limits.groups.trans limits.groupWords
  have slotsFit : H*2^ell≤2^W := limits.boundCap.trans limits.wide
  have resident := v.wideWindowWords_packed_at x m ell short u δ ξ cap dated bits romStart
    mem before i groupsFit keep
  constructor
  · intro j live
    let group : Fin g := ⟨(old j).group,owner j live⟩
    change (((l).inputs i).directory.read before (((l).inputs i).owner.eval before (j.val:Word W))).val=_
    rw [groupRead j live,(resident group).1,Fin.val_cast_of_lt (group.isLt.trans_le groupsFit)]
  · intro side j
    let group : Fin g := ⟨(old j.val).group,owner j.val j.property⟩
    have inside : (port side j.val).val*2^ell<2^W :=
      (Nat.mul_lt_mul_of_pos_right (port side j.val).isLt (Nat.two_pow_pos ell)).trans_le slotsFit
    unfold Format.starts
    rw [groupRead j.val j.property,(resident group).2,portsRead side j,zero_add,Fin.val_cast_of_lt inside]


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
