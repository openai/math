import OAI.Hierarchy.TaggedWireChronologicalTape
import OAI.Hierarchy.ProtocolRAMCalendarStripCausal

namespace OAI
/-! # Admission on the actual native strip arenas and their original input pages -/

noncomputable section
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
variable (R : CalendarTape.CounterROM (chart F c (arena v s) initial width cap (install v s c)
  finish prices catalogue r banks src tbl dst owners))

theorem current_step (e : Event) (tail : List Event) (left right : Memory W)
    (branch : (R.format.slot e).choice left) (agree : ReadBanks.Agree (R.hidden (e::tail)) left right)
    (same : (R.format.slot e).word left branch=R.format.windows.read e right)
    (future : ∀u,R.hidden tail u→(A).base c e+(A).stride≤u)
    (patched : ready C e (R.patch e left branch)) (actual : ready C e right) :
    ReadBanks.Agree (R.hidden tail) ((R.format.slot e).next left branch) (after C e right) := by
  apply R.native_slab_step e tail left right branch agree same ((A).base c e+(A).stride) future
  · intro lower
    exact after_below v s F c initial width cap finish prices catalogue banks src tbl dst owners
      e _ right _ lower le_rfl patched actual
  · intro u high
    have frame:=past_writes (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners e u high
    exact ⟨after_outside C e _ u patched frame,after_outside C e _ u actual frame⟩

theorem words_ordered (es : List Event)
    (pages : ∀t∈es,∀i : Fin (R.format.windows.cells t),(A).base c t≤R.format.windows.base t+i.val)
    (sorted : es.Pairwise (fun a b=>(A).base c a+(A).stride≤(A).base c b)) :
    R.format.windows.ordered C es := by
  induction es with
  | nil=>trivial
  | cons e tail ih=>
    obtain ⟨now,rest⟩:=List.pairwise_cons.mp sorted
    refine ⟨?_,ih (fun t ht=>pages t (List.mem_cons_of_mem _ ht)) rest⟩
    intro t ht i
    exact past_writes v s F c initial width cap finish prices catalogue banks src tbl dst owners e _
      ((now t ht).trans (pages t (List.mem_cons_of_mem _ ht) i))

/-- The current histogram starts at the original event input range. The
generated selector operands are the same row-major `q*i+j` expressions. -/
def selectorROM (room : q*rows s≤2^W) (copyRoom : ∀a,((C).raw a).batch.copies<2^W) : CalendarTape.CounterROM C where
  bank a := ⟨(A).base c (.attempt a),z+q*rowFactor s⟩
  fields a j := by cases a <;> rfl
  fits a := by
    change (formats F c A initial (install v s c) a).market.rows*q≤2^(z+q*rowFactor s)
    rw [(sizes v s F c initial a).1,Nat.mul_comm]
    exact selector_room s
  room a := by
    change (formats F c A initial (install v s c) a).market.rows*q≤2^W
    rw [(sizes v s F c initial a).1,Nat.mul_comm]
    exact room
  copiesFit := copyRoom

variable (room : q*rows s ≤ 2^(wordBits z d copies))
  (copyRoom : ∀a, ((chart F c (arena v s) initial width cap (install v s c)
    finish prices catalogue r banks src tbl dst owners).raw a).batch.copies < 2^(wordBits z d copies))
local notation "D" => selectorROM v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom

theorem current_protected (a : Attempt) (i : Fin (((C).layout a).candidates*q)) :
    protected C (((D).bank a).base+i.val) (.attempt a) := by
  apply (selector_protected v s F c initial width cap finish prices catalogue banks src tbl dst owners a _ _).1
  apply Nat.add_lt_add_left
  have hi:=i.isLt
  change i.val<(formats F c A initial (install v s c) a).market.rows*q at hi
  simpa only [(sizes v s F c initial a).1,Nat.mul_comm (rows s) q] using hi

theorem page_lower (e : Event) (i : Fin ((D).format.windows.cells e)) :
    (A).base c e≤(D).format.windows.base e+i.val := by
  cases e with
  | feed _=>exact i.elim0
  | attempt a=>exact Nat.le_add_right _ _

theorem unread_page (e : Event) {tail : List Event} (sorted : ∀t∈tail,position c e<position c t) :
    ∀u,(D).hidden tail u→(A).base c e+(A).stride≤u := by
  rintro u ⟨t,ht,lo,hi⟩
  cases t with
  | feed b=>exact False.elim (by change u<0 at hi;omega)
  | attempt a=>exact ((A).apart c (sorted _ ht)).trans lo

end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab

end
end OAI
