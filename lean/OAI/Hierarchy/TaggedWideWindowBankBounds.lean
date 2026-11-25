import OAI.Hierarchy.TaggedWideInstalledWindowGeometry
import OAI.Hierarchy.TaggedWideWindowROMBanks
import OAI.Hierarchy.TaggedWideFundedGateRoom
import OAI.Hierarchy.TaggedWideReportGrouping

namespace OAI
/-! # Address bounds and readiness for the installed frozen windows -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard HistoryRoles RoleProgram
open Tagged ProtocolRAMFrozenWindow ProtocolRAMSupergroupDirectory
open scoped Classical Fin.CommRing

private theorem bank_below {W top : ℕ} (b : Bank) (endAt : b.base+b.size≤ top) (room : top<2^W) :
    b.Fits W top :=
  ⟨Nat.two_pow_pos _,by omega,endAt⟩

private theorem dated_before {T : ℕ} (d : WideCPU.Dated T) (s : ℕ) :
    s≤ d.maskStart s ∧ s≤ d.romEnd s ∧
    (d.stageWidth s).base+(d.stageWidth s).size≤ d.workEnd s+2 ∧
    ∀b,(d.slotBank s b).base+(d.slotBank s b).size≤ d.workEnd s+2 := by
  have widths := ProtocolRAMPurchaseSampler.span_le (3*d.rawEdges)
  have slots := ProtocolRAMPurchaseSampler.span_le d.rawEdges
  refine ⟨?_,?_,?_,?_⟩
  · unfold WideCPU.Dated.maskStart WideCPU.Dated.controlStart WideCPU.Dated.rolesEnd WideCPU.endOf
    omega
  · unfold WideCPU.Dated.romEnd WideCPU.Dated.maskROM WideCPU.Dated.controlROMStart
      WideCPU.Dated.firstROM WideCPU.Dated.siteROM WideCPU.endOf
    omega
  · change d.maskStart s+1+ProtocolRAMPurchaseSampler.span (3*d.rawEdges)≤ _
    unfold WideCPU.Dated.workEnd WideCPU.Dated.slotStart
    omega
  · intro b
    change d.slotBase s b+ProtocolRAMPurchaseSampler.span d.rawEdges≤ _
    cases b <;> simp only [WideCPU.Dated.slotBase,WideCPU.Dated.workEnd,Bool.toNat_false,
      Bool.toNat_true,zero_mul,one_mul] <;> omega

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A)
    (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
local notation "P" => v.widePlacement x.h x.w
local notation "n" => (P).catalogue.rows
local notation "stock" => v.fixedTerminalStock P x.h x.w
local notation "page" => v.wideSignedPage x.h x.w stock
local notation "dst" => CatalystArchive.TerminalLayout.destination page
local notation "dates" => (events v.mesh).length
local notation "groups" => (WideMemory.dir x.h v.W k v.wideJobs).groups
local notation "slices" => v.widePaidSlices x.h x.w v.maxBits
local notation "root" => v.wideInstalledRoot x

theorem wide_report_before_root :
    dst+6*n+ProtocolRAMPurchaseSampler.span (3*n)≤ root := by
  let ss:=slices
  let high:=v.wideRoleStart x.h x.w stock ss
  let z:=RoleRoom.shape (R:=WideMemory.R v.sampler x.h v.W k) v.sampler
    (WideMemory.dir x.h v.W k v.wideJobs) n
  have edge : n<2^page := by
    unfold wideSignedPage CatalystArchive.TerminalLayout.pageBits
    refine Nat.lt_of_le_of_lt ?_ Nat.lt_log2_self
    unfold CatalystArchive.TerminalLayout.footprint
    omega
  have pageHigh : 28*2^page≤ high := (le_max_left ..).trans (le_max_right ..)
  have stopped : high≤ z.stop high := by
    simp only [RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,RoleRoom.Sizes.axis,
      RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
    omega
  have prefixEnd : 3*(z.stop high+1)≤ root := by
    change (v.wideWidthLayout x.h x.w ss).archive≤(v.wideReserveLayout x.h x.w ss).scratch+_
    simp only [wideReserveLayout,PrefixWidths.Layout.reserveLayout,PrefixWidths.Layout.packed,PrefixWidths.Layout.bank]
    omega
  have size:=ProtocolRAMPurchaseSampler.span_le (3*n)
  change 18*2^page+6*n+ProtocolRAMPurchaseSampler.span (3*n)≤ _
  omega

theorem wide_window_after_terminal (work : ℕ) : work+2≤ v.wideTerminalWorkEnd x.h x.w v.maxBits work := by
  let b:=v.wideTerminalBoard x.h x.w v.maxBits work
  let t:=v.wideTurnWindow x.h x.w v.maxBits work
  let lo:=v.wideTerminalRankStart x.h x.w v.maxBits work
  have board : work≤ b.endAt := by
    change work≤ work+4*b.old+4*b.edges
    omega
  have ranked : b.endAt≤ lo := by
    change b.endAt≤ b.endAt+3*b.old+b.widthBank.size+(b.newRole true).size
    omega
  have after : lo≤ t.floor := by
    change lo≤ ProtocolRAMTurnReplayed.endAt lo _ _
    simp only [ProtocolRAMTurnReplayed.endAt,ProtocolRAMTurnReplayed.rank,
      ProtocolRAMTurnReplayed.ranks,ProtocolRAMTurnReplayed.counters,
      ProtocolRAMTurnReplayed.groups,ProtocolRAMTurnReplayed.rows,ProtocolRAMTurnReplayed.scratch,
      ProtocolRAMTurnReplayed.weight,ProtocolRAMTurnReplayed.key]
    omega
  obtain ⟨a,b₁,c,e,g⟩ := t.bounds
  change work+2≤ t.stop
  omega

variable (d : WideCPU.Dated (events v.mesh).length)
local notation "cap" => v.wideInstalledCap unitCost
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost d
local notation "start" => v.wideInstalledSize x m ell unitCost d
local notation "rom" => v.wideFormatROM x d v.maxBits root
local notation "gr" => v.wideGroupROM x d v.maxBits root

/-- The only word bound covers the actual start of the frozen format series.
Both slot banks, the masked width and the emitted group use their full padded spans. -/
theorem wideWindow_resident {W : ℕ} (room : (l).floor<2^W) (i : Fin (m+1)) :
    ((l).windows i).Resident W (l).floor ((l).inputs i) := by
  let f:=(l).windows i
  let bank:=RoleROM.bank (dst+6*n) (3*n)
  let a:=(l).inputs i
  have calendar : root≤ gr := by
    have advance (a b : ℕ) : b ≤ a+2*b+2 := by omega
    exact (dated_before d root).2.1.trans (advance _ _)
  have low : gr+2*span groups≤ rom := Nat.le_add_right ..
  have mounted : rom≤ start := Nat.le_add_right ..
  have datedEnd := dated_before d start
  have later : d.maskStart start≤ d.workEnd start := by
    unfold WideCPU.Dated.workEnd WideCPU.Dated.slotStart
    omega
  have after : d.workEnd start+2≤ (l).floor := v.wide_window_after_terminal x _
  have shelf : start≤ (l).floor := datedEnd.1.trans (later.trans (by omega))
  have head : f.adviceEnd≤ (l).floor :=
    (v.wideWindow_rom_bound x m ell short u δ ξ cap rom i).trans shelf
  have groupFit : (groupBank gr groups).Fits W (l).floor := bank_below _ (by
    change gr+span groups≤ (l).floor
    omega) room
  have offsetFit : (offsetBank gr groups).Fits W (l).floor := bank_below _ (by
    change gr+span groups+span groups≤ (l).floor
    omega) room
  have slots (b : Bool) : (d.slotBank start b).Fits W (l).floor :=
    bank_below _ ((datedEnd.2.2.2 b).trans after) room
  have width : (d.stageWidth start).Fits W (l).floor := bank_below _ (datedEnd.2.2.1.trans after) room
  have gate : bank.Fits W (l).floor := bank_below _ ((v.wide_report_before_root x).trans
    (calendar.trans (by omega))) room
  have owner : a.owner.Fits W (l).floor := by
    change (PruneFlag.field bank 0).Fits W (l).floor
    refine ⟨gate,?_⟩
    simp [scale,Expr.Fits]
  apply f.resident_of_external W (l).floor a head room.le owner
  intro operand listed
  change operand∈[groupBank gr groups,offsetBank gr groups,d.slotBank start false,
    d.slotBank start true,d.stageWidth start] at listed
  simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with rfl|rfl|rfl|rfl|rfl
  · exact groupFit
  · exact offsetFit
  · exact slots false
  · exact slots true
  · exact width

/-- Both original report banks and the layer ROM end below the first mutable
format window, hence the final pruning scan may still read their dyadic spans. -/
theorem wideWindow_prune_banks {W : ℕ} (word : (l).floor<2^W) :
    dst+9*n≤(l).floor ∧ (l).layers.base+(l).layers.size≤(l).floor ∧
      (l).prune.Fits W (l).pruneScratch := by
  have datedLo:=(dated_before d start).1
  have last : d.maskStart start≤ d.workEnd start := by
    unfold WideCPU.Dated.workEnd WideCPU.Dated.slotStart
    omega
  have top : d.workEnd start+2≤(l).floor := v.wide_window_after_terminal x _
  have low : start≤(l).floor := by omega
  have rootLo := (v.wide_installed_root_le_size x m ell unitCost d).trans low
  have reports := (v.wide_report_before_root x).trans rootLo
  have rounded := ProtocolRAMPurchaseSampler.lt_span (3*n)
  have layer : (l).layers.base+(l).layers.size≤(l).floor := by
    apply le_trans (show (l).layers.base+(l).layers.size≤ start from ?_) low
    change rom≤ rom+(m+1)*_
    omega
  have target : (l).floor≤(l).pruneScratch := Nat.le_add_right _ _
  refine ⟨by omega,layer,?_⟩
  have bankAt (b : Bank) (bound : b.base+b.size≤(l).floor) : b.Fits W (l).pruneScratch :=
    let first:=bank_below b bound word
    ⟨first.1,first.2.1,first.2.2.trans target⟩
  exact PruneFlag.term_fits _ _ _ _ _
    (bankAt (l).ends (by change dst+ProtocolRAMPurchaseSampler.span (3*n)≤(l).floor; omega))
    (bankAt (l).metrics (by change dst+3*n+ProtocolRAMPurchaseSampler.span (3*n)≤(l).floor; omega))
    (bankAt (l).layers layer)

open Tagged.WideStack ReportSockets
local notation "word" => Native.wordBits x.h (2^v.W) Native.copies

/-- All original group operands fit before the floor of the native paid window. -/
theorem wideWindow_rows_fit (wrap : (l).floor<2^word) : 3*n<2^word := by
  have low:=v.wide_report_before_root x
  have header:=v.wide_installed_root_le_size x m ell unitCost d
  have datedEnd:=dated_before d start
  have last : d.maskStart start≤ d.workEnd start := by
    unfold WideCPU.Dated.workEnd WideCPU.Dated.slotStart
    omega
  have after : d.workEnd start+2≤ (l).floor := v.wide_window_after_terminal x _
  omega

/-- Every scalar needed by the real format reader is bounded at the same funded
word width. The link ordinal and the transported widths are the original report. -/
theorem wideWindow_limits
    (large : purchaseWordHeight v.W k v.wideJobs ell≤ x.h) (wrap : (l).floor<2^word)
    (i : Fin (m+1)) (raw : Fin n→ ProtocolRAMEmit.Row) (ids : ∀j,(raw j).link=j.val)
    (width : ∀j,(raw j).width≤ cap*x.w) : ((l).windows i).Limits word raw := by
  let f:=(l).windows i
  obtain ⟨groupCode,groupCap,slotCap,mapCap,tableCap,rate⟩ :=
    v.wideWindow_addresses x m ell short u δ ξ cap rom i
  have datedLo:= (dated_before d start).1
  have last : d.maskStart start≤ d.workEnd start := by
    unfold WideCPU.Dated.workEnd WideCPU.Dated.slotStart
    omega
  have high : d.workEnd start+2≤ (l).floor := v.wide_window_after_terminal x _
  have before : start≤ (l).floor := by omega
  have alloc : f.adviceEnd≤ (l).floor :=
    (v.wideWindow_rom_bound x m ell short u δ ξ cap rom i).trans before
  have spanFit : f.rom+13*2^f.bits+2^f.gb+2^f.gb≤ (l).floor := alloc
  have intact : (0:ℕ)<2^f.bits := Nat.two_pow_pos _
  have within (a c g top : ℕ) (pos : 0<c) (cover : a+13*c+g+g≤top) :
      c≤top ∧ g≤top ∧ 10≤top := ⟨by omega, by omega, by omega⟩
  obtain ⟨codeRoom, groupRoom, tenRoom⟩ := within _ _ _ _ intact spanFit
  have codeFit : 2^f.bits≤2^word := codeRoom.trans wrap.le
  have groupWord : 2^f.gb≤2^word := groupRoom.trans wrap.le
  have unitFit : cap≤ cap*x.w := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left cap (show 1≤ x.w from x.formats.2.1)
  have menuFit : m<2^word := by
    have stridePos : 0< v.wideWindowStride x ell cap := by unfold wideWindowStride; positivity
    have menuBound:=Nat.mul_le_mul_left (m+1) (show 1≤ v.wideWindowStride x ell cap from stridePos)
    rw [Nat.mul_one] at menuBound
    change rom+(m+1)*v.wideWindowStride x ell cap≤ (l).floor at before
    omega
  have digits : f.n≤ word :=
    purchase_word_fit (u:=u) (δ:=δ) (ξ:=ξ) v.W m k v.wideJobs ell short v.stage_positive x large i
  have exp : f.B=2^(f.n-1):=rfl
  have idFit : f.B≤2^f.n := by rw [exp]; exact Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  have batchFit := idFit.trans (Nat.pow_le_pow_right (by decide) digits)
  refine ⟨groupCode,groupWord,?_,pieces_of_bit_bound raw x.w cap x.formats.2.1 width,
    groupCap,slotCap,mapCap,tableCap,fun j=>(width j).trans_lt rate,
    codeFit,menuFit,?_,?_,unitFit.trans_lt (rate.trans_le codeFit),?_,idFit,batchFit⟩
  · intro j j' lt
    change (raw j).link < (raw j').link
    rw [ids j, ids j']
    exact lt
  · exact Nat.le_of_lt_succ i.isLt
  · exact tenRoom.trans wrap.le
  · rw [exp]
    exact Nat.two_pow_pos _

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native Tagged WideCPU ProtocolRAMFrozenWindow
open scoped Classical
set_option quotPrecheck false

/-- Move the original immutable input bounds past the earlier windows and bound
the complete mutable interval by the end of the same finite series. -/
theorem window_ready_of_resident {m W : ℕ} (l : WideCPU.Layout m)
    (room : WindowSeries.finish l.floor l.need<2^W) (i : Fin (m+1))
    (resident : (l.windows i).Resident W l.floor (l.inputs i)) :
    (l.windows i).Ready W (l.windowBase i) (l.inputs i) := by
  have before : l.floor≤l.windowBase i := Nat.le_add_right _ _
  have interval : (l.windows i).window.stop (l.windowBase i)≤WindowSeries.finish l.floor l.need := by
    rw [Size.stop_add]
    exact WindowSeries.within l.floor l.need i
  have bank (b : Bank) (input : b.Fits W l.floor) : b.Fits W (l.windowBase i) :=
    ⟨input.1,input.2.1,input.2.2.trans before⟩
  exact ⟨interval.trans_lt room,ProtocolRAMGeneratedWrite.fits_mono _ before resident.owner,
    fun b member=>bank b (resident.inputs b member),fun j=>bank _ (resident.rom j)⟩

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A : ℝ} (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
  (dated : WideCPU.Dated (events v.mesh).length)
local notation "layout" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated

/-- The original canonical layout supplies every owner, signed input and table
bound; only the machine's absolute top address remains. -/
theorem wideWindow_ready {W : ℕ} (room : (layout).pruneScratch<2^W) (i : Fin (m+1)) :
    ((layout).windows i).Ready W ((layout).windowBase i) ((layout).inputs i) := by
  have total : WindowSeries.finish (layout).floor (layout).need=(layout).pruneScratch:=rfl
  have floorLe : (layout).floor≤WindowSeries.finish (layout).floor (layout).need:=Nat.le_add_right _ _
  rw [total] at floorLe
  exact window_ready_of_resident (layout) (by simpa only [total] using room) i
    (v.wideWindow_resident x m ell short u δ ξ unitCost dated (floorLe.trans_lt room) i)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
