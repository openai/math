import OAI.Hierarchy.TaggedWireStripAdmission
import OAI.Hierarchy.TaggedWireReplayAdmission

namespace OAI
/-! # Chronological admission on the executable calendar for every original input -/

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

def effects : CalendarTape.CounterROM.Effects C where
  endAt e:= (A).base c e+(A).stride
  read e m m' h h' low:=after_below v s F c initial width cap finish prices catalogue banks src tbl dst owners
    e m m' _ low le_rfl h h'
  frame e m h u hi:=after_outside C e m u h
    (past_writes v s F c initial width cap finish prices catalogue banks src tbl dst owners e u hi)

theorem page_end (e : Event) : (L).base e+(L).cells e≤(A).base c e+(A).stride := by
  cases e with
  | feed b=>exact Nat.zero_le _
  | attempt a=>
    change (A).base c (.attempt a)+(formats F c A initial (install v s c) a).market.rows*q≤_
    apply Nat.add_le_add_left
    rw [(sizes v s F c initial a).1,Nat.mul_comm]
    apply (selector_room s).trans
    change selectorSpan s≤ stride v s
    simp only [stride,PostLayout.column,PostLayout.startColumns,mask,flags,first,Nat.zero_add,Nat.add_assoc]
    exact Nat.le_add_right ..

theorem dates_separate : (E).Pairwise (fun a b=>∀u,(L).inside b u→
    (effects (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners).endAt a≤u) := by
  have positionsOrdered : (E).Pairwise (fun a b=>position c a<position c b) := by
    have h : ((E).map (position c)).Pairwise (·<·) := by rw [positions];exact List.pairwise_lt_range
    simpa only [List.pairwise_map] using h
  have spans : (E).Pairwise (fun a b=>(A).base c a+(A).stride≤(A).base c b) :=
    positionsOrdered.imp (fun h=>(A).apart c h)
  have lower:=page_lower (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom
  apply spans.imp
  intro a b separated u within
  let j : Fin ((L).cells b):=⟨u-(L).base b,by obtain ⟨h,h'⟩:=within;omega⟩
  have atCell : (L).base b+j.val=u:=Nat.add_sub_of_le within.1
  exact (separated.trans (lower b j)).trans atCell.le

theorem authentic_admission (baseline : Memory W) (raw : Bits (CalendarTape.bits (D).format.slot E))
    (all : ∀input,mounted C E ((L).header E input baseline))
    (election : ∀a prior tail m u,E=prior++(.attempt a::tail) → run C prior ((L).header E raw baseline)=u→
      ReadBanks.Agree ((D).hidden (.attempt a::tail)) m u→ ready C (.attempt a) m→ ready C (.attempt a) u→
      (D).format.observed a m u) :
    admissible C E ((L).header E raw baseline) ↔
      ∃! p : CalendarTape.Path (D).format.slot E baseline, CalendarTape.encode (D).format.slot E baseline p=raw := by
  let P:=effects (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners
  have positionsOrdered : (E).Pairwise (fun a b=>position c a<position c b) := by
    have h : ((E).map (position c)).Pairwise (·<·) := by rw [positions];exact List.pairwise_lt_range
    simpa only [List.pairwise_map] using h
  have spans : (E).Pairwise (fun a b=>(A).base c a+(A).stride≤(A).base c b) :=
    positionsOrdered.imp (fun h=>(A).apart c h)
  have lower:=page_lower (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom
  have upper:=page_end (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom
  have native:=words_ordered (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners D E
    (fun t _=>lower t) spans
  have dates : (E).Pairwise (fun a b=>∀u,(L).inside b u→P.endAt a≤u) :=
    dates_separate (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom
  have split (xs : List Event) (order : xs.Pairwise (fun a b=>(A).base c a+(A).stride≤(A).base c b)) : (L).disjoint xs := by
    induction xs with
    | nil=>trivial
    | cons e xs ih=>
      obtain ⟨before,rest⟩:=List.pairwise_cons.mp order
      refine ⟨?_,ih rest⟩
      intro f hf j bound
      exact (Nat.not_lt_of_ge ((upper e).trans ((before _ hf).trans (lower f j)))) bound.2
  exact (D).replay_admission P E baseline raw (split E spans) native dates
    (fun a _=>current_protected (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom a)
    all election

end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab

end
end OAI
