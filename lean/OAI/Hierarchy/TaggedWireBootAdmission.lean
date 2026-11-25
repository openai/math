import OAI.Hierarchy.TaggedWireOriginalAdmission
import OAI.Hierarchy.ProtocolRAMCalendarBootChoices
import OAI.Hierarchy.ProtocolRAMCalendarStripBootSize

namespace OAI
/-! # Original chronological admission from the physical CT boot tape -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage StripDirectory
open WireTelescope Tagged Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {z d k q depth r : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "W" => wordBits z d copies
variable (v : Slab) (s : Boards z d k q depth) (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (c : Mesh) (initial width cap : ℕ) (finish : ℝ) (prices : PhasePrice) (catalogue : CatalogueRows.Board)
  (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
local notation "A" => arena v s
local notation "C" => chart F c A initial width cap (install v s c) finish prices catalogue r banks src tbl dst owners
variable (room : q*rows s ≤ 2^(wordBits z d copies))
  (copyRoom : ∀a, ((chart F c (arena v s) initial width cap (install v s c)
    finish prices catalogue r banks src tbl dst owners).raw a).batch.copies < 2^(wordBits z d copies))
local notation "D" => selectorROM v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom

local notation "L" => (D).format.windows
local notation "E" => events c

local notation "profiles" => formats F c A initial (install v s c)
local notation "V" => Whole.markets c finish prices profiles

theorem original_pages_separate : (L).disjoint E := by
  have low:=page_lower (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom
  have high:=page_end (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom
  have seq : ((E).map (position c)).Pairwise (·<·) := by rw [positions];exact List.pairwise_lt_range
  have p : (E).Pairwise (fun x y=>position c x<position c y) := by simpa only [List.pairwise_map] using seq
  suffices ∀xs:List Event,xs.Pairwise (fun x y=>position c x<position c y)→(L).disjoint xs from this E p
  intro xs pp
  induction xs with
  | nil=>trivial
  | cons e xs ih=>
    obtain ⟨h,rest⟩:=List.pairwise_cons.mp pp
    refine ⟨?_,ih rest⟩
    intro f hf j within
    exact (Nat.not_lt_of_ge ((high e).trans (((A).apart c (h f hf)).trans (low f j)))) within.2

theorem header_slots_at (size : ℕ) (covers : (A).endAddress c≤ size) (heap : heapEnd z d copies≤v.headerEnd) :
    ∀e∈E,∀x,(L).inside e x→heapEnd z d copies≤x ∧ x<size ∧
      ∀i,¬ProtocolRAMStaticSlabs.Inside (fun j=>Boot.low (V j)) (fun j=>Boot.high (V j)) i x := by
  rintro (a|b) appears x within
  · have lo : (A).base c (.attempt a)≤x:=within.1
    have hi : x<(A).base c (.attempt a)+q*rows s := by
      have h:=within.2
      change x<(A).base c (.attempt a)+(profiles a).market.rows*q at h
      simpa only [(sizes v s F c initial a).1,Nat.mul_comm (rows s) q] using h
    have before : heapEnd z d copies≤x:=heap.trans ((Nat.le_add_right .. : v.headerEnd≤(A).base c (.attempt a)).trans lo)
    have sz : x<(A).endAddress c:=
      within.2.trans_le ((page_end (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom _).trans
        ((A).within c (.attempt a) appears))
    refine ⟨before,sz.trans_le covers,?_⟩
    intro i
    rintro ⟨below,above⟩
    let b := (Whole.attempts c)[i.val]
    by_cases earlier : position c (.attempt b)<position c (.attempt a)
    · have endB := (boot_bounds v s F c initial finish prices i).2.1
      have gap := (A).apart c earlier
      exact (Nat.not_lt_of_ge (endB.trans (gap.trans lo))) above
    · have ordered := Nat.le_of_not_gt earlier
      have left : (A).base c (.attempt a)≤(A).base c (.attempt b) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right (A).stride ordered) (A).first
      have data := (sizes v s F c initial b).2.2.1
      change (profiles b).market.shelf.table.base≤x at below
      rw [data] at below
      have room : q*rows s≤ selectorSpan s := selector_room s
      omega
  · have impossible : x<0:=within.2
    omega

theorem boot_original_at (size : ℕ) (covers : (A).endAddress c≤ size) (heap : heapEnd z d copies≤v.headerEnd) (hd : 1≤d) (π : Equiv.Perm (Fin (2^z)))
    (mem : Boot.Tape z d) (tag : ∀u : Fin (2^z),mem u.val=((π u).val:Word W)) (raw : Bits (CalendarTape.bits (D).format.slot E)) :
    Boot.booted V size ((L).header E raw mem)=(L).header E raw (Boot.booted V size mem) := by
  apply Boot.booted_header V ((boot_layout v s F c initial finish prices heap).mono covers) hd π mem tag L E raw
    (original_pages_separate v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom)
  exact header_slots_at v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom size covers heap

theorem boot_original (heap : heapEnd z d copies≤v.headerEnd) (hd : 1≤d) (π : Equiv.Perm (Fin (2^z)))
    (mem : Boot.Tape z d) (tag : ∀u : Fin (2^z),mem u.val=((π u).val:Word W)) (raw : Bits (CalendarTape.bits (D).format.slot E)) :
    Boot.booted V ((A).endAddress c) ((L).header E raw mem)=(L).header E raw (Boot.booted V ((A).endAddress c) mem) :=
  boot_original_at v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom
    ((A).endAddress c) le_rfl heap hd π mem tag raw

theorem boot_admission_at (size : ℕ) (covers : (A).endAddress c≤ size) (heap : heapEnd z d copies≤v.headerEnd) (hd : 1≤d) (π : Equiv.Perm (Fin (2^z)))
    (mem : Boot.Tape z d) (tag : ∀u : Fin (2^z),mem u.val=((π u).val:Word W)) (raw : Bits (CalendarTape.bits (D).format.slot E))
    (mount : ∀u,mounted C E (Boot.booted V size ((L).header E u mem))) (fits : (A).endAddress c<2^W)
    (tables : ∀a,.attempt a∈E→beforeTables v s F c initial a)
    (alphabet : ∀a prior tail,E=prior++(.attempt a::tail)→∀i,
      CalendarTape.CounterROM.measured («C»:=C) a (run C prior (Boot.booted V size ((L).header E raw mem))) i≤q) :
    admissible C E (Boot.booted V size ((L).header E raw mem)) ↔
      ∃! p : CalendarTape.Path (D).format.slot E (Boot.booted V size mem),
        CalendarTape.encode (D).format.slot E (Boot.booted V size mem) p=raw := by
  have swap:=boot_original_at v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom size covers heap hd π mem tag
  rw [swap raw]
  apply original_admission v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom _ raw
    (fun u=>swap u ▸ mount u) fits tables
  exact swap raw ▸ alphabet

theorem boot_admission (heap : heapEnd z d copies≤v.headerEnd) (hd : 1≤d) (π : Equiv.Perm (Fin (2^z)))
    (mem : Boot.Tape z d) (tag : ∀u : Fin (2^z),mem u.val=((π u).val:Word W)) (raw : Bits (CalendarTape.bits (D).format.slot E))
    (mount : ∀u,mounted C E (Boot.booted V ((A).endAddress c) ((L).header E u mem))) (fits : (A).endAddress c<2^W)
    (tables : ∀a,.attempt a∈E→beforeTables v s F c initial a)
    (alphabet : ∀a prior tail,E=prior++(.attempt a::tail)→∀i,
      CalendarTape.CounterROM.measured («C»:=C) a (run C prior (Boot.booted V ((A).endAddress c) ((L).header E raw mem))) i≤q) :
    admissible C E (Boot.booted V ((A).endAddress c) ((L).header E raw mem)) ↔
      ∃! p : CalendarTape.Path (D).format.slot E (Boot.booted V ((A).endAddress c) mem),
        CalendarTape.encode (D).format.slot E (Boot.booted V ((A).endAddress c) mem) p=raw :=
  boot_admission_at v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom
    ((A).endAddress c) le_rfl heap hd π mem tag raw mount fits tables alphabet

end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab

end
end OAI
