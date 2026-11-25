import OAI.Hierarchy.TaggedWideWindowFullLocal
import OAI.Hierarchy.TaggedWideWindowCutImage
import OAI.Hierarchy.TaggedWideCalendarMask
import OAI.Hierarchy.TaggedWideSwitchTariff

namespace OAI
/-! # Positive-port masks on the original frozen width banks -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreBoard.PhysicalTerm
open Tagged Tagged.WideStack Tagged.WideControlJoin ProtocolRAMFrozenWindow
open TaggedShorterSlotWidth ProtocolRAMReportedPorts ProtocolStackContraction
open LinearAlgebra.SpectralBooks ThreeFlat Routing
open scoped Classical

/-- Physical row observed for an original endpoint width. The width and the two
scatter-control tables occupy disjoint parts of the same frozen window. -/
def ProtocolRAMFrozenWindow.Format.widthRow (f : ProtocolRAMFrozenWindow.Format) {U : ℕ} (start : ℕ)
    (room : start+f.window.stop 0≤ U) (q : TaggedShorterSlotWidth.Slot f.groups f.D) : Fin U :=
  ⟨f.address start (.inl q),(f.cell_bound start (.inl q)).trans_le room⟩

namespace Tagged.WideStack.Leaf
variable {F : Type} [Field F] {E Se Dst T Priv H P : Type}
  [Fintype E] [Fintype Se] [Fintype Dst] [Fintype T] [Fintype Priv] [Fintype H] [Fintype P]
  {N w m groups ports lanes : ℕ} (cls : T→ℕ) {rows : T→ Fin N→ ProtocolRAMEmit.Row}
  (s : ∀t,Installed F groups ports lanes w m (cls t) (rows t))
  (cap : Priv→ℕ) (G : Gate) (maxWidth : ℕ)
variable (address : ∀ _t : T, TaggedShorterSlotWidth.Slot groups (ports*lanes) → Fin G.u)
    (low : WideParent.columnBits maxWidth ≤ G.W+1)

/-- The native comparator consumes precisely the paid low bits of each socket width. -/
def positiveWidthPin (t : T) (g : Fin groups) (b : Bool) (i : Fin (ports*lanes))
    (j : Fin (WideParent.columnBits maxWidth)) : SitePins E Se Dst G :=
  .inr (.inr (.inr (address t (g,b,i),j.castLE low)))

private theorem slot_width_le {numGroups size limit : ℕ} {c : Fin numGroups → ℕ}
    (pl : ∀ g, Bool → Fin (c g) ↪ Fin size)
    (bits : TaggedShorterSlotWidth.Transport c → ℕ) (bounded : ∀ u, bits u ≤ limit)
    (v : TaggedShorterSlotWidth.Slot numGroups size) :
    TaggedShorterSlotWidth.value pl bits v ≤ limit := by
  classical
  obtain ⟨g,b,i⟩ := v
  by_cases occupied : i ∈ Set.range (pl g b)
  · obtain ⟨j,rfl⟩ := occupied
    exact (TaggedShorterSlotWidth.value_live pl bits ⟨g,j⟩ b).le.trans (bounded ⟨g,j⟩)
  · exact (TaggedShorterSlotWidth.value_blank pl bits (g,b,i) occupied).le.trans (Nat.zero_le _)

omit [Fintype T] in
private theorem placed_width_le (maximum : ∀ t i, (rows t i).width ≤ maxWidth) (t : T)
    (v : TaggedShorterSlotWidth.Slot groups (ports*lanes)) :
    TaggedShorterSlotWidth.value (groups:=groups) (D:=ports*lanes)
      (c:=fun g : Fin groups => ProtocolRAMReportedPorts.count (rows t) w m (cls t) g.val)
      (s t).bank.place
      (TaggedShorterSlotWidth.reportWidth (groups:=groups) (rows t) w m (cls t) (s t).unique) v
      ≤ maxWidth := by
  exact slot_width_le (numGroups:=groups) (size:=ports*lanes)
    (c:=fun g : Fin groups => ProtocolRAMReportedPorts.count (rows t) w m (cls t) g.val)
    (s t).bank.place (TaggedShorterSlotWidth.reportWidth (groups:=groups) (rows t) w m (cls t)
      (s t).unique)
    (fun u => maximum t (((ProtocolRAMReportedPorts.common (rows t) w m (cls t) u.1.val
      (s t).unique).symm u.2).1.val)) v

omit [Fintype Priv] [Fintype H] [Fintype P] in
/-- The priced, logarithmic comparator is driven by the bits of the actual return
word for live and vacant sockets, with the original payload wire on every assignment. -/
theorem frozen_positive_mask {Other : Type} [Fintype Other]
    (tailOrder : ((Bool × ((e : Priv) × Fin (cap e))) ⊕ (H ⊕ P)) ≃ Other)
    (number : Pos (banks s) ⊕ Other ≃ Dst)
    (out : Memory G.W) (ex : E→ Bool) (sel : Se→ Bool)
    (maximum : ∀t i,(rows t i).width≤ maxWidth)
    (stored : ∀ (t : T) (v : TaggedShorterSlotWidth.Slot groups (ports*lanes)),
      (out (G.addr (address t v)).val).val =
        TaggedShorterSlotWidth.value (groups:=groups) (D:=ports*lanes)
          (c:=fun g : Fin groups => ProtocolRAMReportedPorts.count (rows t) w m (cls t) g.val)
          (s t).bank.place (TaggedShorterSlotWidth.reportWidth (groups:=groups)
            (rows t) w m (cls t) (s t).unique) v)
    (a : ∀t,(banks s t).Slots) (y : PrivatePorts cap) (h : H→ Bool) (p : P→ Bool) :
    TypedWiring.value (positiveMask (F:=F) (V:=SitePins E Se Dst G) (T:=T) (groups:=groups)
      (ports:=ports) (lanes:=lanes) (bits:=WideParent.columnBits maxWidth) (w:=w) cls
      (positiveWidthPin (T:=T) (groups:=groups) (ports:=ports) (lanes:=lanes) (E:=E) (Se:=Se) (Dst:=Dst) G maxWidth address low)
      (fun t v=>.inr (.inr (.inl (number (.inl ⟨t,v.1,v.2⟩)))))) (CalendarTerms.readPins (B:=G)
        ((Equiv.sumCongr (Equiv.refl _) tailOrder).trans number) ex sel (G.terminal out)
        (write (banks s) cap a y h p)) =
      if supported (banks s) (active s) a then 1 else 0 := by
  let words (t : T) (v : TaggedShorterSlotWidth.Slot groups (ports*lanes)) :
      Word (WideParent.columnBits maxWidth) := WideParent.column maxWidth (out (G.addr (address t v)).val)
  have equal (t : T) (v : TaggedShorterSlotWidth.Slot groups (ports*lanes)) : (words t v).val=(out (G.addr (address t v)).val).val :=
    WideParent.column_read _ _ ((stored t v).le.trans (placed_width_le cls s maxWidth maximum t v))
  apply positiveMask_value (F:=F) (V:=SitePins E Se Dst G) (T:=T) (groups:=groups) (ports:=ports)
    (lanes:=lanes) (bits:=WideParent.columnBits maxWidth) (w:=w) cls _ _ s _ a words
  · intro t g b i j
    exact (congrArg (fun width : ℕ => width.testBit j.val) (equal t (g,b,i))).symm
  · exact fun t g b i=>(equal t (g,b,i)).trans (stored t _)
  · intro t v
    simp [CalendarTerms.readPins,write,voltage]

end Tagged.WideStack.Leaf
namespace ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage.ReportSockets TaggedShorterSupergroups TaggedShorterBudget
open ProtocolRAMSupergroupDirectory ProtocolRAMEmit PrivateRAM
open scoped Classical Fin.CommRing
set_option maxRecDepth 2048
attribute [local irreducible] Native.wordBits Nat.pow

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (m ell short : ℕ)
    (u : ℝ→ℝ) (δ ξ : ℝ) (cap : ℕ)
    (dated : WideCPU.Dated (events v.mesh).length) (bits romStart : ℕ)
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
local notation "layout" => v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart
local notation "groups" => (WideMemory.dir x.h v.W k v.wideJobs).groups
local notation "ports" => WideMemory.H x.h v.W k v.wideJobs
local notation "slots" => TaggedShorterSlotWidth.Slot groups (ports*2^ell)
variable (G : Gate) (upper :
  (v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).pruneScratch +
  (v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).pruneRows + 1 ≤ G.u)
local notation "fmt" t => (layout).windows t

include upper in
/-- The observed width fields of the actual paid gate include a word for every
original group, side and packed slot. -/
def wideWindowWidthRow (t : Fin (m+1)) (slot : slots) : Fin G.u :=
  ((fmt t).widthRow ((layout).windowBase t) (by
    have inner:=WindowSeries.within (layout).floor (layout).need t
    change (layout).windowBase t+(fmt t).window.stop 0≤(layout).pruneScratch at inner
    omega) slot)

variable (old : Fin (v.widePlacement x.h x.w).catalogue.rows → ProtocolRAMEmit.Row)
    (ins : ∀ t : Fin (m+1), Leaf.Installed F (WideMemory.dir x.h v.W k v.wideJobs).groups
      (WideMemory.H x.h v.W k v.wideJobs) (2^ell) x.w m t.val old)
    (mem before : Memory (Native.wordBits x.h (2^v.W) Native.copies))
    (fit : ∀ t : Fin (m+1),
      ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).windows t).Limits
        (Native.wordBits x.h (2^v.W) Native.copies) old)
    (retained : ∀ j : ℕ, v.wideGroupROM x dated bits romStart ≤ j →
      j < v.wideGroupROM x dated bits romStart + 2*span (WideMemory.dir x.h v.W k v.wideJobs).groups →
      @Eq (Word (Native.wordBits x.h (2^v.W) Native.copies)) (before j)
        (v.wideWindowWords («W» := Native.wordBits x.h (2^v.W) Native.copies)
          x m ell short u δ ξ cap dated bits romStart mem j))
    (owner : ∀ j, 0 < pieces old x.w j → (old j).group < (WideMemory.dir x.h v.W k v.wideJobs).groups)
    (originalGroup : ∀ (t : Fin (m+1)) j, 0 < pieces old x.w j →
      @Eq (Word (Native.wordBits x.h (2^v.W) Native.copies))
        (((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).inputs t).owner.eval
          before (j.val : Word (Native.wordBits x.h (2^v.W) Native.copies)))
        ((old j).group : Word (Native.wordBits x.h (2^v.W) Native.copies)))
    (portsRead : ∀ (t : Fin (m+1)) (side : Bool) (j : ProtocolRAMPackedPlacement.Live old x.w),
      @Eq (Word (Native.wordBits x.h (2^v.W) Native.copies))
        ((if side then ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).inputs t).right
          else ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).inputs t).left).read
          before (j.val.val : Word (Native.wordBits x.h (2^v.W) Native.copies)))
        ((((ins t).port side j.val).val*2^ell : ℕ) : Word (Native.wordBits x.h (2^v.W) Native.copies)))
    (widthEq : Native.wordBits x.h (2^v.W) Native.copies = G.W) (dense : ∀ i, (G.addr i).val=i.val)
    (out : Memory (Native.wordBits x.h (2^v.W) Native.copies))
    (stored : ∀ (t : Fin (m+1)) (slot : TaggedShorterSlotWidth.Slot
      (WideMemory.dir x.h v.W k v.wideJobs).groups (WideMemory.H x.h v.W k v.wideJobs * 2^ell)),
      @Eq (Word (Native.wordBits x.h (2^v.W) Native.copies))
        (out (((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).windows t).address
          ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).windowBase t) (.inl slot)))
        ((v.wideCutAnchor x m ell short u δ ξ cap dated bits romStart t mem before old (fit t)
          (ins t) retained owner (originalGroup t) (portsRead t)).word
          («W» := Native.wordBits x.h (2^v.W) Native.copies)
          (f := (v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).windows t)
          (a := (v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).inputs t)
          (m₀ := before) (limits := fit t) old (.inl slot)))

local notation "src" t => (layout).inputs t
local notation "addr" => v.wideWindowWidthRow x m ell short u δ ξ cap dated bits romStart G upper
local notation "liveBanks" => Leaf.banks (F := F) (T := Fin (m+1)) («groups» := groups)
  («ports» := ports) (lanes := 2^ell) (N := (v.widePlacement x.h x.w).catalogue.rows) (m := m)
  (w := x.w) (cls := fun t : Fin (m+1) => t.val) (records := fun _ : Fin (m+1) => old) ins

private theorem read_cast_memory {a b : ℕ} (same : a=b) (out : Memory a) (i : ℕ) :
    ((cast (congrArg Memory same) out) i).val=(out i).val := by
  subst b
  rfl

set_option maxHeartbeats 600000 in
include upper ins mem before fit retained owner originalGroup portsRead widthEq dense out stored in
/-- Read back the actual slot widths after the final retained observation. The original
common rank chooses the printed width on a live slot and a vacant slot has value zero. -/
theorem wideWindow_mask_stored (t : Fin (m+1)) (slot : slots) :
    ((cast (congrArg Memory widthEq) out) (G.addr (addr t slot)).val).val =
      TaggedShorterSlotWidth.value («groups»:=groups) (D:=ports*2^ell)
        (c:=fun g : Fin groups => ProtocolRAMReportedPorts.count old x.w m t.val g.val)
        (ins t).bank.place (TaggedShorterSlotWidth.reportWidth («groups»:=groups) old x.w m t.val (ins t).unique) slot := by
  rw [read_cast_memory widthEq out (G.addr (addr t slot)).val, dense]
  have sourceWords := v.wideWindow_live_sources («W» := W) x m ell short u δ ξ cap dated bits romStart
    mem before t old (fit t) retained (ins t).port owner (originalGroup t) (portsRead t)
  exact (congrArg (fun value : Word W => value.val) (stored t slot)).trans
    ((fmt t).originalAnchor_width_val («W» := W) ports (2^ell) (src t) old before (fit t) (ins t)
      sourceWords.1 owner sourceWords.2 slot)

variable {Ex Se Priv H P Tail : Type} [Fintype Ex] [Fintype Se] [Fintype Priv] [Fintype H]
    [Fintype P] [Fintype Tail] (privateCap : Priv→ℕ)
local notation "data" => Leaf.Pos liveBanks ⊕ Tail
variable (privateOrder : ((Bool × ((e : Priv) × Fin (privateCap e))) ⊕ (H ⊕ P)) ≃ Tail) (ex : Ex→ Bool) (sel : Se→ Bool)
    (maximum : ℕ) (bounded : ∀j,(old j).width≤ maximum) (widthBits : WideParent.columnBits maximum≤ G.W+1)
local notation "word" => Leaf.positiveWidthPin (T:=Fin (m+1)) («groups»:=groups) («ports»:=ports) (lanes:=2^ell) (E:=Ex) (Se:=Se) (Dst:=data) G maximum addr widthBits
local notation "field" => fun (t : Fin (m+1))
  (q : ProtocolStackContraction.Slot (Fin groups) (ports*2^ell) × Fin ⌈dyadic t.val*x.w⌉₊) =>
  (Sum.inr (Sum.inr (Sum.inl (Sum.inl ⟨t,q.1,q.2⟩))) : SitePins Ex Se data G)
local notation "ord" => Equiv.sumCongr (Equiv.refl (Leaf.Pos liveBanks)) privateOrder

set_option maxHeartbeats 600000 in
include upper ins mem before fit retained owner originalGroup portsRead widthEq dense out stored
  privateCap privateOrder ex sel maximum bounded widthBits in
omit [Fintype Priv] [Fintype H] [Fintype P] in
/-- The paid positive mask at the genuine public, private and historical assignments.
The comparator reads only the logarithmic width field from each returned native word. -/
theorem wideWindow_mask_value (a : ∀ t : Fin (m+1), (liveBanks t).Slots) (y : PrivatePorts privateCap)
    (hist : H→ Bool) (publicBits : P→ Bool) :
    TypedWiring.value (Leaf.positiveMask (F:=F) (V:=SitePins Ex Se data G) (T:=Fin (m+1))
      («groups»:=groups) («ports»:=ports) (lanes:=2^ell) (bits:=WideParent.columnBits maximum)
      (w:=x.w) Fin.val word field)
      (CalendarTerms.readPins (B:=G) ord ex sel (G.terminal (cast (congrArg Memory widthEq) out))
        (Leaf.write liveBanks privateCap a y hist publicBits)) =
      if Leaf.supported liveBanks (Leaf.active ins) a then 1 else 0 := by
  apply Leaf.frozen_positive_mask (F:=F) (E:=Ex) (Se:=Se) (Dst:=data) (T:=Fin (m+1))
    (cls:=Fin.val) (rows:=fun _ : Fin (m+1) => old) ins privateCap G maximum addr widthBits privateOrder
    (Equiv.refl data) (cast (congrArg Memory widthEq) out) ex sel (fun _=>bounded) _ a y hist publicBits
  exact fun t slot=>v.wideWindow_mask_stored x m ell short u δ ξ cap dated bits romStart G upper old
    ins mem before fit retained owner originalGroup portsRead widthEq dense out stored t slot


end ProtocolRAM.Calendar.FixedProtocolFormat
end Hierarchy
end

end OAI
