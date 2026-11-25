import OAI.Hierarchy.ProtocolRAMCalendarStripPorts
import OAI.Hierarchy.ProtocolRAMStripTreeTraversal
import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceROM

namespace OAI
/-! # Format-only tree pages and the two genuine broadcast forests of the native chart -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CatalogueRows
open StockCommit
open scoped Classical Fin.CommRing
variable {z W k q depth w n : ℕ}
local notation "N" => Stages z (2^W)
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

def treeRows (a : Attempt) := (build F (withPorts s c b G) a 0).market.rows

/-- At most one immutable table of each geometry is installed per scheduled event.
The two address ranges are adjacent and all fields depend solely on chart parameters. -/
def treePage (base n : ℕ) : PortROM.Table (events c).length :=
  let rows:=fun i : Fin (events c).length=>match (events c)[i] with
    | .attempt a=>treeRows s c b G F a
    | .feed _=>0
  ⟨base,rows,Fintype.card (Strip.TreeLink n k),Finset.univ.sup rows,fun i=>Finset.le_sup (Finset.mem_univ i)⟩

def payloadPage (base : ℕ) := treePage s c b G F base (PayloadStrip.edgeCount N)
def boughtPage (base : ℕ) := treePage s c b G F (payloadPage s c b G F base).stop (ChainStrip.edgeCount depth)

def treeWords (base : ℕ) (rest : Memory w) : Memory w :=
  (boughtPage s c b G F base).words ((payloadPage s c b G F base).words rest)

def pageStart (t : PortROM.Table n) (c : Mesh) (a : Attempt) := t.base+((events c).idxOf (.attempt a))*t.stride

def originalTree (base : ℕ) (a : Attempt) : Traversals :=
  let rows:=treeRows s c b G F a
  match a with
  | .outer _ _=>stripTree (payloadPortsAt s c G) b (pageStart (payloadPage s c b G F base) c a) rows
  | .inner p t _ _=>stripTree (boughtPortsAt s c b G p t) b (pageStart (boughtPage s c b G F base) c a) rows

/-- Chronological caller of `paidSlices`, including the true bought or payload
tree and its second replacement radius. -/
def withTrees (base : ℕ) (a : Attempt) := forest s c b G F (originalTree s c b G F base a) a

theorem treePage_loaded (base n : ℕ) (a : Attempt) (m : Memory w) (occurs : Event.attempt a∈events c)
    (wide : 0<w) (fit : (treePage s c b G F base n).stop<2^w) :
    let t:=treePage s c b G F base n
    (treeHeader (pageStart t c a) (treeRows s c b G F a) n k).Loaded (t.words m) := by
  let t:=treePage s c b G F base n
  let i : Fin (events c).length:=⟨(events c).idxOf (.attempt a),List.idxOf_lt_length_of_mem occurs⟩
  have date : (events c)[i]=Event.attempt a := List.getElem_idxOf i.isLt
  have rows : t.rows i=treeRows s c b G F a := by change (match (events c)[i] with | .attempt t=>_ | .feed _=>0)=_;rw [date]
  have hdr : t.header i=treeHeader (pageStart t c a) (treeRows s c b G F a) n k := by
    change PortHeader.mk _ (t.rows i) _ = _;rw [rows];rfl
  change (treeHeader (pageStart t c a) (treeRows s c b G F a) n k).Loaded (t.words m)
  rw [←hdr]
  exact t.loaded m wide fit i

theorem treePages_loaded (base : ℕ) (a : Attempt) (m : Memory w) (occurs : Event.attempt a∈events c)
    (wide : 0<w) (fit : (boughtPage s c b G F base).stop<2^w) :
    let p:=payloadPage s c b G F base
    let t:=boughtPage s c b G F base
    let mem:=treeWords s c b G F base m
    (treeHeader (pageStart p c a) (treeRows s c b G F a) (PayloadStrip.edgeCount N) k).Loaded mem ∧
    (treeHeader (pageStart t c a) (treeRows s c b G F a) (ChainStrip.edgeCount depth) k).Loaded mem := by
  intro p t mem
  have order : p.stop≤t.stop:=Nat.le_add_right p.stop _
  have pLoaded:=treePage_loaded s c b G F base _ a m occurs wide (order.trans_lt fit)
  refine ⟨pLoaded.frame ?_,treePage_loaded s c b G F p.stop _ a (p.words m) occurs wide fit⟩
  let i : Fin (events c).length:=⟨(events c).idxOf (.attempt a),List.idxOf_lt_length_of_mem occurs⟩
  have date : (events c)[i]=Event.attempt a := List.getElem_idxOf i.isLt
  have rows : p.rows i=treeRows s c b G F a := by change (match (events c)[i] with | .attempt t=>_ | .feed _=>0)=_;rw [date]
  have hdr : p.header i=treeHeader (pageStart p c a) (treeRows s c b G F a) (PayloadStrip.edgeCount N) k := by
    change PortHeader.mk _ (p.rows i) _ = _;rw [rows];rfl
  intro x lo hi
  apply t.frame _ _ (.inl ?_)
  change x < (treeHeader (pageStart p c a) (treeRows s c b G F a) (PayloadStrip.edgeCount N) k).stop at hi
  rw [←hdr] at hi
  exact hi.trans_le (p.end_le i)

def treeWalk (a : Attempt) (m : Memory w) (row : ℕ) (pos : 0<b.coreRows) : List (Fin b.rows) :=
  match a with
  | .outer _ _=>broadcastWalk (payloadPortsAt s c G) b m row pos
  | .inner p h _ _=>broadcastWalk (boughtPortsAt s c b G p h) b m row pos

theorem withTrees_reads (base : ℕ) (a : Attempt) (m : Memory w) (room : b.rows<2^w) (pos : 0<b.coreRows)
    (rowRoom : treeRows s c b G F a≤2^w)
    (payloadRoom : Fintype.card (Strip.TreeLink (PayloadStrip.edgeCount N) k)≤2^w)
    (boughtRoom : Fintype.card (Strip.TreeLink (ChainStrip.edgeCount depth) k)≤2^w)
    (hP : (treeHeader (pageStart (payloadPage s c b G F base) c a) (treeRows s c b G F a) (PayloadStrip.edgeCount N) k).Loaded m)
    (hB : (treeHeader (pageStart (boughtPage s c b G F base) c a) (treeRows s c b G F a) (ChainStrip.edgeCount depth) k).Loaded m) :
    (withTrees s c b G F base a).Reads m (fun i : Fin (treeRows s c b G F a)=>treeWalk s c b G a m i.val pos) := by
  cases a with
  | outer p h => exact stripTree_guard_reads (payloadPortsAt s c G) b _ _ m _ hP room rowRoom payloadRoom pos
  | inner p h j t => exact stripTree_guard_reads (boughtPortsAt s c b G p h) b _ _ m _ hB room rowRoom boughtRoom pos

/-- The boot starts from the true low permutation and the same recursively
mounted stock, test and static routing tables as the rest of the controller. -/
theorem tree_boot {jobs stages phases : ℕ} (board : JointHeader.Board) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z (2^W)) (base : ℕ)
    (boot : Fin jobs→Market z (2^W) k) {size : ℕ} (layout : Boot.Layout boot size)
    (first : 2^z≤board.initial) (after : JointHeader.stop board z stages k phases≤base)
    (heap : Native.heapEnd z (2^W) Native.copies≤base)
    (fit : (boughtPage s c b G F base).stop<2^(Native.wordBits z (2^W) Native.copies))
    (within : (boughtPage s c b G F base).stop≤ size) (before : ∀j,(boughtPage s c b G F base).stop≤Boot.low (boot j))
    (a : Attempt) (occurs : Event.attempt a∈events c) :
    let p:=payloadPage s c b G F base
    let t:=boughtPage s c b G F base
    let out:=Boot.booted boot size (JointHeader.words board z (2^W) stages k phase π stock (treeWords s c b G F base rest))
    (treeHeader (pageStart p c a) (treeRows s c b G F a) (PayloadStrip.edgeCount N) k).Loaded out ∧
    (treeHeader (pageStart t c a) (treeRows s c b G F a) (ChainStrip.edgeCount depth) k).Loaded out := by
  intro p t out
  let headers:=treeWords s c b G F base rest
  let src:=JointHeader.words board z (2^W) stages k phase π stock headers
  let i : Fin (events c).length:=⟨(events c).idxOf (.attempt a),List.idxOf_lt_length_of_mem occurs⟩
  have date : (events c)[i]=Event.attempt a := List.getElem_idxOf i.isLt
  have rows tBase n : (treePage s c b G F tBase n).rows i=treeRows s c b G F a := by
    change (match (events c)[i] with | .attempt t=>_ | .feed _=>0)=_;rw [date]
  have hdr tBase n : (treePage s c b G F tBase n).header i=treeHeader (pageStart (treePage s c b G F tBase n) c a) (treeRows s c b G F a) n k := by
    change PortHeader.mk _ ((treePage s c b G F tBase n).rows i) _=_;rw [rows];rfl
  have pair:=treePages_loaded s c b G F base a rest occurs (by unfold Native.wordBits;omega) fit
  have launched := (Boot.start boot layout (Nat.two_pow_pos _) π src
    (JointHeader.authentic («N»:=stages) (k:=k) board phase π stock headers first)).2
  have stable (x : ℕ) (lo : base≤x) (hi : x<t.stop) : out x=headers x := by
    have keep:=launched.kept x (heap.trans lo) (fun j member=>Nat.not_lt_of_ge member.1 (hi.trans_le (before j)))
    rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le within)] at keep
    exact keep.trans (JointHeader.tail_words board phase π stock headers x first (after.trans lo))
  have order : p.stop≤t.stop:=Nat.le_add_right p.stop _
  have payloadHeader : p.header i =
      treeHeader (pageStart p c a) (treeRows s c b G F a) (PayloadStrip.edgeCount N) k := hdr base _
  have boughtHeader : t.header i =
      treeHeader (pageStart t c a) (treeRows s c b G F a) (ChainStrip.edgeCount depth) k := hdr p.stop _
  have payloadLoaded : (p.header i).Loaded headers := by rw [payloadHeader]; exact pair.1
  have boughtLoaded : (t.header i).Loaded headers := by rw [boughtHeader]; exact pair.2
  rw [←payloadHeader,←boughtHeader]
  refine ⟨payloadLoaded.frame ?_,boughtLoaded.frame ?_⟩
  · intro x lo hi
    exact stable x ((Nat.le_add_right base _).trans lo) (hi.trans_le ((p.end_le i).trans order))
  · intro x lo hi
    have pre : base≤p.stop := Nat.le_add_right base _
    exact stable x (pre.trans ((Nat.le_add_right p.stop _).trans lo)) (hi.trans_le (t.end_le i))

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
