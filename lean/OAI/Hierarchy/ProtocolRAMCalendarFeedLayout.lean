import OAI.Hierarchy.ProtocolRAMNativeLiveFormats
import OAI.Hierarchy.ProtocolRAMCalendarFeedRead
import OAI.Hierarchy.ProtocolRAMCalendarSliceROM
import OAI.Hierarchy.ProtocolRAMCalendarPriced
import OAI.Hierarchy.ProtocolRAMCalendarPrevious

namespace OAI
/-! # Placing the feed ROM and both boundary inventory banks on the public calendar -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Classical
noncomputable section
variable {h z d k N q goods : ℕ}

theorem previous_before (c : Mesh) (arena : Arena) (initial width : ℕ) (published : Event→ℕ)
    (initialRoom : initial+width≤arena.first) (room : ∀ e,published e+width≤arena.base c e+arena.stride)
    (e : Event) : previousStock c initial published e+width≤arena.base c e := by
  dsimp only [previousStock]
  split
  next h =>
    apply (room _).trans (arena.apart c _)
    rw [position_at]
    omega
  · exact initialRoom.trans (Nat.le_add_right ..)

def FeedLayout.atEvent (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial width cap : ℕ) (b : Boundary) : FeedLayout z N k :=
  let stockSize := PurchaseInventory.footprint z N k
  let saved := match b with
    | .outer _ => initial
    | .inner p a _ => (format (.outer p a)).pricedArea.output+(format (.outer p a)).pricedArea.goods
  let stride := cap*width+1
  ⟨previousStock c initial (publishedStock c arena format) (.feed b),saved,arena.base c (.feed b),
    width,cap,sliceROM (initial+stockSize) c.reserveSteps stride,stride⟩

def feedColumns (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial width cap : ℕ) (b : Boundary) :=
  (FeedLayout.atEvent (N:=N) c arena format initial width cap b).columns

/-- Stock-base assignment is acyclic. The format's output and its archived
mode addresses depend only on the fixed placement and scan lengths. -/
def Format.withStock (format : Format z d k q goods) (active : ℕ) : Format z d k q goods :=
  {format with market:={format.market with shelf:={format.market.shelf with stockBase:=active}}}

@[simp] theorem Format.withStock_area (format : Format z d k q goods) (active : ℕ) :
    (format.withStock active).area=format.area := rfl

@[simp] theorem Format.withStock_pricedArea (format : Format z d k q goods) (active : ℕ) :
    (format.withStock active).pricedArea=format.pricedArea := rfl

@[simp] theorem Format.withStock_mode (format : Format z d k q goods) (active : ℕ) :
    (format.withStock active).board.modeOut=format.board.modeOut := rfl

def stockFormats (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial : ℕ) (a : Attempt) : Format z d k q goods :=
  (format a).withStock (previousStock c initial (publishedStock c arena format) (.attempt a))

theorem stockFormats_source (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial : ℕ) (a : Attempt) : (stockFormats c arena format initial a).stockSource.old.base=
      previousStock c initial (publishedStock c arena format) (.attempt a) := rfl

theorem feedColumns_pricedInstalled (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial width cap : ℕ) (b : Boundary) (finish : ℝ) (prices : PhasePrice)
    {r edges : ℕ} (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr)
    (ids : Attempt→Fin goods→Expr) :
    (pricedInstalled c finish prices (stockFormats c arena format initial)
      (feedColumns (N:=N) c arena format initial width cap) sink idBase role ids).columns b =
      (FeedLayout.atEvent (N:=N) c arena format initial width cap b).columns := rfl

theorem FeedLayout.atEvent_before (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial width cap : ℕ) (b : Boundary)
    (initialRoom : initial+PurchaseInventory.footprint z N k+
      (sliceROM (initial+PurchaseInventory.footprint z N k) c.reserveSteps (cap*width+1)).size≤arena.first)
    (attemptRoom : ∀ a,(format a).pricedArea.output+(format a).pricedArea.goods+PurchaseInventory.footprint z N k≤
      arena.base c (.attempt a)+arena.stride)
    (modeRoom : ∀ a,(format a).board.modeOut+1≤arena.base c (.attempt a)+arena.stride)
    (feedRoom : 2*PurchaseInventory.footprint z N k≤arena.stride) :
    (FeedLayout.atEvent (N:=N) c arena format initial width cap b).Before c
      (fun a=>(format a).board.modeOut) b := by
  let L := FeedLayout.atEvent (N:=N) c arena format initial width cap b
  let g := PurchaseInventory.footprint z N k
  have init : initial+g≤arena.first := by dsimp [g]; omega
  have first : arena.first≤arena.base c (.feed b) := Nat.le_add_right ..
  have current : L.kept=arena.base c (.feed b) := rfl
  have before (e : Event) (old : position c e<position c (.feed b)) :
      publishedStock c arena format e+g≤arena.base c (.feed b) := by
    apply le_trans _ (arena.apart c old)
    cases e with
    | attempt a => have pred := attemptRoom a; change (format a).pricedArea.output+g≤_; dsimp only [g]; omega
    | feed f => change arena.base c (.feed f)+g≤_; dsimp only [g]; omega
  have purchase (p a j : ℕ) : position c (.attempt (.outer p a))<position c (.feed (.inner p a j)) := by
    simp only [position,sliceBase]
    omega
  constructor
  · change previousStock c initial (publishedStock c arena format) (.feed b)+g≤arena.base c (.feed b)
    dsimp only [previousStock]
    split
    next eq =>
      apply before
      rw [position_at]
      omega
    · exact init.trans first
  · cases b with
    | outer p => exact init.trans first
    | inner p a j => exact (attemptRoom _).trans (arena.apart c (purchase p a j))
  · exact initialRoom.trans first
  · intro p a j eq
    subst b
    exact (modeRoom _).trans (arena.apart c (purchase p a j))

theorem FeedLayout.atEvent_fits {w : ℕ} (c : Mesh) (arena : Arena) (format : Attempt→Format z d k q goods)
    (initial width cap : ℕ) (b : Boundary) (occurs : Event.feed b∈events c)
    (feedRoom : 2*PurchaseInventory.footprint z N k≤arena.stride) (room : arena.endAddress c<2^w) :
    (FeedLayout.atEvent (N:=N) c arena format initial width cap b).stop<2^w := by
  apply lt_of_le_of_lt _ ((arena.within c (.feed b) occurs).trans_lt room)
  change arena.base c (.feed b)+PurchaseInventory.footprint z N k+PurchaseInventory.footprint z N k≤_
  omega

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
