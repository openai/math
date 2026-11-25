import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Native observations for adjacent occurrences of a terminal route -/

namespace Hierarchy.ProtocolRAMTurnItinerary

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProbeStage.Native
open scoped Fin.CommRing

/-- Each expression reads the current chronological turn row. The origin addresses
the first occurrence in original storage order, before possible route reversal. -/
structure Chart where
  item : Expr
  origin : Expr
  length : Expr
  position : Expr
  reverse : Expr
  width : Expr
  site : Expr
  seat : Expr

structure Banks where
  oldSource : Bank
  oldTarget : Bank
  edge : Bank
  tailSite : Bank
  tailRole : Bank
  headRole : Bank
  /-- Bank based at weighted-prefix output plus three, addressed at four times the row. -/
  starts : Bank

def plus := Expr.op .add
def minus := Expr.op .sub

/-- The successor uses the current forward occurrence or the previous reversed
occurrence. The predecessor uses the other member of the same adjacent pair. -/
def occurrence (p : Chart) (right : Bool) : Expr :=
  let rev := minus p.length p.position
  let a := if right then p.position else minus p.position (.lit 1)
  let b := if right then minus rev (.lit 1) else rev
  plus p.origin (.branch .eq p.reverse (.lit 0) a b)

def onEnd (p : Chart) (right : Bool) (boundary interior : Expr) : Expr :=
  .branch .eq p.position (if right then p.length else .lit 0) boundary interior

def four (x : Expr) : Expr := plus (plus x x) (plus x x)

/-- At a new link the physical role is selected by its actual site, independent of
the index direction in which the link was traversed. At old endpoints it is the
fixed original source or target role of that commodity. -/
def role (p : Chart) (b : Banks) (right : Bool) : Expr :=
  let edge := Expr.lookup b.edge (occurrence p right)
  onEnd p right (.lookup (if right then b.oldTarget else b.oldSource) p.item)
    (.branch .eq (.lookup b.tailSite edge) p.site (.lookup b.tailRole edge) (.lookup b.headRole edge))

/-- Old row words begin at bit zero in the local role. New rows use the selected
occurrence's actual weighted prefix, including repeated traversals of the same link. -/
def start (p : Chart) (b : Banks) (right : Bool) : Expr :=
  onEnd p right (.lit 0) (.lookup b.starts (four (occurrence p right)))

def live (p : Chart) : Expr := .branch .lt p.length p.position (.lit 0) p.width

/-- The first five columns are gate data. The last two are indices for sparse
physical publication of the turn at its static site and seat. -/
def field (p : Chart) (b : Banks) : Fin 7 → Expr :=
  ![role p b false,role p b true,start p b false,start p b true,live p,p.site,p.seat]

def program (W base n : ℕ) (p : Chart) (b : Banks) :=
  ProtocolRAM.program W (columns n base (List.ofFn (field p b)))

def ticks (base n : ℕ) (p : Chart) (b : Banks) :=
  ProtocolRAM.clock (columns n base (List.ofFn (field p b)))

def upper (p : Chart) (b : Banks) := (List.ofFn (field p b)).map Expr.work |>.sum

theorem ticks_le (base n : ℕ) (p : Chart) (b : Banks) :
    ticks base n p b ≤ 4+7*(4+n*(2*upper p b+4)) := by
  have each (e : Expr) (he : e ∈ List.ofFn (field p b)) : e.work ≤ upper p b :=
    List.le_sum_of_mem (List.mem_map_of_mem he)
  simpa only [ticks,List.length_ofFn] using columns_clock n base (upper p b) (List.ofFn (field p b)) each

theorem cheap (W base n : ℕ) (p : Chart) (b : Banks) : CheapCode (program W base n p b) :=
  program_cheap W (columns n base (List.ofFn (field p b)))

/-- One actual field-major scan per observable. Only the seven contiguous columns
are written, so both the occurrence prefix and the incoming history survive. -/
theorem run {W n : ℕ} (base : ℕ) (p : Chart) (b : Banks) (mem : Memory W)
    (inputs : ∀ j,(field p b j).Fits W base) (room : base+7*n < 2^W) :
    ∃ out,(program W base n p b).Exec mem out (ticks base n p b) ∧
      (∀ (f : Fin 7) (i : Fin n),out (base+f.val*n+i.val)=(field p b f).eval mem (i.val:Word W)) ∧
      ∀ a,a < base ∨ base+7*n ≤ a → out a=mem a := by
  let es := List.ofFn (field p b)
  have safe (e : Expr) (he : e ∈ es) : e.Fits W base := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    exact inputs j
  refine ⟨ProtocolRAM.result (columns n base es) mem,columns_exec es mem
    (columns_safe es le_rfl safe (by simpa only [es,List.length_ofFn] using room)),?_,?_⟩
  · intro f i
    have idx : f.val < es.length := by simpa only [es,List.length_ofFn] using f.isLt
    have sel : es[f.val]=field p b f := List.getElem_ofFn (f:=field p b) idx
    exact (columns_read es mem le_rfl safe f.val idx i).trans (congrArg (fun e : Expr=>e.eval mem (i.val:Word W)) sel)
  · intro a outside
    exact columns_frame es mem (by simpa only [es,List.length_ofFn] using outside)

end Hierarchy.ProtocolRAMTurnItinerary

end OAI
