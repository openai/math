import OAI.Hierarchy.ProtocolRAMCalendarMesh
import OAI.Hierarchy.ProtocolRAMAttemptGate
import OAI.Hierarchy.ProtocolRAMStockAccounts
import OAI.Hierarchy.ProtocolRAMFeed

namespace OAI
/-! # The fixed outer mesh and the reserve mesh of a purchased probe

A bounded reduction epoch ends before the single feed at that mesh boundary.
The unconditional outer boundaries still run after the crude-cost exit.
Reserve boundaries test the original acquisition word before returning a slice.
-/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

def word (addr : ℕ) : Expr := .lookup ⟨addr,0⟩ (.lit 0)

@[simp] theorem word_eval {w : ℕ} (a : ℕ) (m : Memory w) (r : Word w) :
    (word a).eval m r=m a := by simp [word,Expr.eval,Bank.read,Bank.size]

/-- Short-circuit on the first historical phase whose saved mode has the indicated value. -/
def anyMode (addresses : List ℕ) (code : ℕ) (yes no : Expr) : Expr :=
  addresses.foldr (fun a t=>.branch .eq (word a) (.lit code) yes t) no

theorem anyMode_eval {w : ℕ} (as : List ℕ) (code : ℕ) (yes no : Expr) (m : Memory w) (r : Word w) :
    (anyMode as code yes no).eval m r =
      if ∃ a ∈ as,m a=(code : Word w) then yes.eval m r else no.eval m r := by
  classical
  induction as with
  | nil => simp [anyMode]
  | cons a as ih =>
    by_cases hit : m a=(code:Word w)
    · simp [anyMode,Expr.eval,Comparison.test,hit]
    · simpa [anyMode,Expr.eval,Comparison.test,word_eval,beq_iff_eq,hit] using ih

def closed (modeAt : Attempt → ℕ) (p a : ℕ) (yes no : Expr) :=
  anyMode ((List.range a).map fun i=>modeAt (.outer p i)) 1 yes no

def innerClosed (modeAt : Attempt → ℕ) (p a j b : ℕ) (yes no : Expr) :=
  anyMode ((List.range b).map fun i=>modeAt (.inner p a j i)) 1 yes no

/-- If all allotted outer reductions ran, one whole fuel budget of decreases is
available for the crude finish. Before the next interval, this is visible in the
last trial's mode (repair or a fully replayed acquisition). -/
def outerSaturated (c : Mesh) (modeAt : Attempt → ℕ) (p : ℕ) (yes no : Expr) : Expr :=
  let ends := (List.range p).map fun j=>modeAt (.outer j (c.outerFuel-1))
  if c.outerFuel=0 then yes else anyMode ends 2 yes (anyMode ends 3 yes no)

/-- A depleted replacement budget skips future repairs on this reserve mesh.
Every remaining reserve boundary nevertheless returns its scheduled slice. -/
def innerSaturated (c : Mesh) (modeAt : Attempt → ℕ) (p a j : ℕ) (yes no : Expr) : Expr :=
  if c.innerFuel=0 then yes else
    anyMode ((List.range j).map fun k=>modeAt (.inner p a k (c.innerFuel-1))) 2 yes no

def stop (c : Mesh) (modeAt : Attempt→ℕ) : Attempt → Expr
  | .outer p a => outerSaturated c modeAt p (.lit 1) (closed modeAt p a (.lit 1) (.lit 0))
  | .inner p a j b =>
    .branch .eq (word (modeAt (.outer p a))) (.lit 3)
      (innerSaturated c modeAt p a j (.lit 1) (innerClosed modeAt p a j b (.lit 1) (.lit 0))) (.lit 1)

theorem no_purchase_no_repair {w : ℕ} (m : Memory w) (r : Word w) (c : Mesh)
    (modeAt : Attempt→ℕ) (p a j b : ℕ) (skip : m (modeAt (.outer p a))≠3) :
    (stop c modeAt (.inner p a j b)).eval m r = 1 := by
  simp [stop,Expr.eval,Comparison.test,word_eval,skip]

/-- A physical reserve boundary is enabled only by the persistent word of its own purchase.
All outer boundaries advance, including the complete remaining payload injections on a crude exit. -/
def onBoundary (modeAt : Attempt → ℕ) (b : Boundary) (yes no : Expr) : Expr :=
  match b with
  | .outer _ => yes
  | .inner p a _ => .branch .eq (word (modeAt (.outer p a))) (.lit 3) yes no

theorem boundary_eval {w : ℕ} (addr : Attempt → ℕ) (p a j : ℕ) (yes no : Expr)
    (m : Memory w) (r : Word w) :
    (onBoundary addr (.inner p a j) yes no).eval m r =
      if m (addr (.outer p a))=3 then yes.eval m r else no.eval m r := by
  simp [onBoundary,Expr.eval,Comparison.test,word_eval,beq_iff_eq]

/-- One real boundary simultaneously writes new capped stock and the overflow
that is discharged on its fixed core route. Selectors cannot enable a second feed. -/
structure Feed where
  rows : ℕ
  cap : ℕ
  stock : Expr
  increment : Expr
  kept : ℕ
  overflow : ℕ

def total (addr : Attempt→ℕ) (b : Boundary) (f : Feed) : Expr :=
  .op .add f.stock (onBoundary addr b f.increment (.lit 0))

def Feed.passes (f : Feed) (addr : Attempt→ℕ) (b : Boundary) : List Pass :=
  [⟨f.kept,f.rows,StockAccounts.clipped f.cap (total addr b f)⟩,
   ⟨f.overflow,f.rows,StockAccounts.overflow f.cap (total addr b f)⟩]

theorem feed_exec {w : ℕ} (addr : Attempt→ℕ) (b : Boundary) (f : Feed) (m : Memory w)
    (fit : ∀ p∈f.passes addr b,p.Fits w) :
    (program w (f.passes addr b)).Exec m (result (f.passes addr b) m) (clock (f.passes addr b)) := by
  intro P R K M pc reg pub exit rom data cfg start entry same
  exact program_exec _ m fit M pc reg pub exit rom data cfg start entry same

/-- Each column names one official commodity and its original saved reserve. The
only exogenous bits are the payload's prescribed integer injection slices. -/
structure CommodityColumn where
  rows : ℕ
  cap : ℕ
  stock : Expr
  reserve : Expr
  feedTable : Bank
  stride : ℕ
  payload : ℕ
  kept : ℕ
  overflow : ℕ

def CommodityColumn.feed (f : CommodityColumn) (c : Mesh) (b : Boundary) : Feed :=
  let amount := match b with
    | .outer p => Expr.lit (if p<c.inject then AdaptiveProbe.slice c.inject f.payload p else 0)
    | .inner _ _ j => Expr.lookup f.feedTable (.op .add (.lit (j*f.stride)) f.reserve)
  ⟨f.rows,f.cap,f.stock,amount,f.kept,f.overflow⟩

theorem injected_exact (c : Mesh) (bits : ℕ) (nonempty : 0<c.inject) :
    ∑ p ∈ Finset.range c.inject,AdaptiveProbe.slice c.inject bits p=bits :=
  AdaptiveProbe.slice_sum c.inject bits nonempty

theorem reserve_exact (c : Mesh) (bits : ℕ) (nonempty : 0<c.reserveSteps) :
    ∑ j ∈ Finset.range c.reserveSteps,AdaptiveProbe.slice c.reserveSteps bits j=bits :=
  AdaptiveProbe.slice_sum c.reserveSteps bits nonempty


end Hierarchy.ProtocolRAM.Calendar

end OAI
