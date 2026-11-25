import OAI.Hierarchy.ProbeFixedCatalystHeaders
import OAI.Hierarchy.ProtocolRAMCalendarStripTreeBudget
import OAI.Hierarchy.ProtocolRAMPaidCatalogueGeometry

namespace OAI
/-! # The three retained purchased-row pointers in the fixed public catalogue -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard BoughtSockets StripChart
open scoped Classical Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (z width K G H R bits idBase : ℕ) (b : JointHeader.Board)
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "phases" => Fin (v.mesh.inject+v.mesh.cool)
local notation "trials" => Fin v.mesh.outerFuel

def sourceOuter (i : Fin n) : phases × trials := finProdFinEquiv.symm i

def sourceAttempt (i : Fin n) : Attempt := .outer (v.sourceOuter i).1.val (v.sourceOuter i).2.val

/-- First pass: the number of slots, the slot numbering and the two catalogue
lengths determine the slab offsets. The source expressions are filled in after
those offsets have been computed. -/
private def emptyDirectory (count : ℕ) : BoughtSockets.Directory count :=
  ⟨0,0,0,0,0,fun _=>⟨0,0,0,0⟩,fun _=>0,fun _=>0⟩

private def socketBoard (original : BoughtSockets.Directory n) : CatalogueRows.Board :=
  CatalogueRows.liveBoard (Public.join original v.sampler z v.W k v.depth K G H R)
    v.sampler z v.W k v.depth R K G H bits idBase

private def socketPlacement (d : BoughtSockets.Directory n) : v.Placement :=
  v.catalystPlacement z K G H R b (v.socketBoard z K G H R bits idBase d) d

private def socketLayout : v.Placement :=
  v.socketPlacement z K G H R bits idBase b (emptyDirectory n)

/-- Each physical archive address belongs to the earlier outer attempt. Only
these three projected fields survive the immutable public-directory installation. -/
def originalSockets : BoughtSockets.Directory n :=
  let P:=v.socketLayout z K G H R bits idBase b
  let shape:=v.nativeBoards P z width
  let f:=v.nativeFormats P z width
  {emptyDirectory n with
    shelf:=fun i=>(shape.outer (v.sourceOuter i).1.val (v.sourceOuter i).2.val).market.shelf
    flagBase:=fun i=>(f (v.sourceAttempt i)).board.purchaseOut
    menuBase:=fun i=>(f (v.sourceAttempt i)).board.boughtFields 6}

def publicBoard : CatalogueRows.Board :=
  v.socketBoard z K G H R bits idBase (v.originalSockets z width K G H R bits idBase b)

def sourcePair : CatalogueRows.Board × BoughtSockets.Directory n :=
  (v.publicBoard z width K G H R bits idBase b,v.originalSockets z width K G H R bits idBase b)

local notation "dir" => v.originalSockets z width K G H R bits idBase b
local notation "cat" => v.publicBoard z width K G H R bits idBase b
local notation "P" => v.catalystPlacement z K G H R b cat dir
local notation "s" => v.nativeBoards P z width
local notation "w" => Native.wordBits z (2^v.W) Native.copies

theorem sourcePair_rows :
    (cat).coreRows=R ∧ (cat).boughtRows=n*(PurchaseFrozen.count z (2^v.W) k*
      PurchaseFrozen.paths z v.sampler.degree v.depth) := ⟨rfl,rfl⟩

section
variable (left right : BoughtSockets.Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)) (phase trial : ℕ)
local notation "placed" => v.socketPlacement z K G H R bits idBase b
local notation "seed₀" => originBoards v z width
  (StockCommit.PortHeader.start (Public.keyHead v.sampler (CoreCatalogue.top z v.W K G H R) z v.W k v.depth))
local notation "sized₀" => v.sized seed₀ width
local notation "allocated" => fun d => v.slab seed₀ (placed d) width
local notation "socketsAt" => fun d => v.nativeBoards (placed d) z width
local notation "programAt" => fun d => v.nativeFormats (placed d) z width (Attempt.outer phase trial)

private theorem tables_end {letters : ℕ} (inputs : Boards z (2^v.W) k letters v.depth)
    (first second : CatalogueRows.Board) (ports₁ ports₂ : PortBanks ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)) :
    (economicHeader F inputs v.cost v.mesh b first ports₁ v.finish (v.basePhase width)
      v.digitRadix v.digitRadix v.precision v.precision).stop =
    (economicHeader F inputs v.cost v.mesh b second ports₂ v.finish (v.basePhase width)
      v.digitRadix v.digitRadix v.precision v.precision).stop := by
  let price := v.basePhase width
  let radix := v.digitRadix
  let prec := v.precision
  let phasePrice := DeadlineROM.prices v.mesh v.finish price
  let next := innerVector F inputs b v.mesh v.finish price radix radix prec prec
  let start := (menuPages F inputs v.cost next.stop radix radix phasePrice).stop
  change (boughtPage inputs v.mesh first ports₁ F start).stop = (boughtPage inputs v.mesh second ports₂ F start).stop
  have one := treePages_exact inputs v.mesh first ports₁ F start
  have two := treePages_exact inputs v.mesh second ports₂ F start
  exact one.trans two.symm

private theorem socket_header_stop :
    (v.header seed₀ (placed left) width).stop = (v.header seed₀ (placed right) width).stop :=
  v.tables_end z width b sized₀ (placed left).catalogue (placed right).catalogue (placed left).routes (placed right).routes

private theorem socket_slab : allocated left = allocated right := by
  let extra := ProtocolRAMPurchaseSampler.bits v.keepLimit
  have samePrior {phases₀ U V steps : ℕ} (first second : EconomicHeader phases₀ U V steps)
      (ends : first.stop = second.stop) :
      chargedSlab F sized₀ v.cost first extra = chargedSlab F sized₀ v.cost second extra := by
    unfold chargedSlab outerReserve
    rw [ends]
  let rowCount := R + n*(PurchaseFrozen.count z (2^v.W) k * PurchaseFrozen.paths z v.sampler.degree v.depth)
  exact congrArg (fun prior : Slab => prior.withTerminal v.mesh z (2^v.W) k (sized₀).sampler.degree v.depth rowCount)
    (samePrior _ _ (v.socket_header_stop z width K G H R bits idBase b left right))

private theorem underlying_shelf (placement : v.Placement) :
    ((v.nativeBoards placement z width).outer phase trial).market.shelf =
      ((v.located (v.seed placement z width) placement width).outer phase trial).market.shelf := rfl

private theorem same_shelf :
    ((socketsAt left).outer phase trial).market.shelf = ((socketsAt right).outer phase trial).market.shelf := by
  rw [v.underlying_shelf z width phase trial (placed left),v.underlying_shelf z width phase trial (placed right)]
  exact congrArg (fun sl : Slab => ((sl.install sized₀ v.mesh).outer phase trial).market.shelf)
    (v.socket_slab z width K G H R bits idBase b left right)

set_option cleanup.letToHave false in
set_option maxHeartbeats 1500000 in
private theorem native_column (placement : v.Placement) (column : ℕ) :
    let f := v.nativeFormats placement z width (Attempt.outer phase trial)
    let input := v.sized (v.seed placement z width) width
    let sl := v.slab (v.seed placement z width) placement width
    let base := (Slab.arena sl input).base v.mesh (.attempt (.outer phase trial))
    PostLayout.column f.maskStart f.indexBits f.market.rows column =
      PostLayout.column (Slab.mask sl input base) (z + Slab.rowFactor input) (Slab.rows input) column := by
  intro f input sl base
  have shape : f.market.flags = Slab.flags sl input base ∧
      f.market.rows = Slab.rows input ∧ f.batch.tests.excess.rows = Slab.goods z (2^v.W) k ∧
      f.batch.tests.payload.rows = Slab.goods z (2^v.W) k ∧
      f.market.failures.rows = Slab.rows input ∧ f.indexBits = z + Slab.rowFactor input := by
    simp only [Slab.rows_eq]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨flags,rows,excess,payload,failed,indices⟩ := shape
  have mask : f.maskStart = Slab.mask sl input base := by
    change f.market.flags+f.market.rows+1+(f.batch.tests.excess.rows+1)+(f.batch.tests.payload.rows+1)+
      (f.market.failures.rows+1) = _
    rw [flags,rows,excess,payload,failed]; rfl
  rw [mask,indices,rows]

private theorem same_column (column : ℕ) :
    PostLayout.column (programAt left).maskStart (programAt left).indexBits (programAt left).market.rows column =
    PostLayout.column (programAt right).maskStart (programAt right).indexBits (programAt right).market.rows column := by
  rw [v.native_column z width phase trial (placed left) column,
      v.native_column z width phase trial (placed right) column]
  exact congrArg (fun sl : Slab => PostLayout.column (Slab.mask sl sized₀
    ((Slab.arena sl sized₀).base v.mesh (.attempt (.outer phase trial))))
    (z + Slab.rowFactor sized₀) (Slab.rows sized₀) column)
    (v.socket_slab z width K G H R bits idBase b left right)

private theorem same_flag :
    (programAt left).board.purchaseOut = (programAt right).board.purchaseOut :=
  v.same_column z width K G H R bits idBase b left right phase trial 1

private theorem same_menu :
    (programAt left).board.boughtFields 6 = (programAt right).board.boughtFields 6 :=
  v.same_column z width K G H R bits idBase b left right phase trial 16
end

set_option maxHeartbeats 500000 in
set_option maxRecDepth 100000 in
/-- The final catalogue reads the literal purchase outcome, menu cell and
original sampler shelf used by the process that owns the indicated outer row. -/
theorem sourcePair_uses (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (p : phases) (a : trials) :
    let C:=v.nativeChart P z width r banks src tab dst owners
    let i:=finProdFinEquiv (p,a)
    (dir).shelf i=((s).outer p a).market.shelf ∧ (dir).flagBase i=(repair C (.outer p a)).purchaseOut ∧
      (dir).menuBase i=(repair C (.outer p a)).boughtFields 6 := by
  intro C i
  have pa : v.sourceOuter i=(p,a):=finProdFinEquiv.symm_apply_apply (p,a)
  let shape:=v.socketLayout z K G H R bits idBase b
  let ss:=v.nativeBoards shape z width
  let ff:=v.nativeFormats shape z width
  change (ss.outer (v.sourceOuter i).1.val (v.sourceOuter i).2.val).market.shelf=((s).outer p a).market.shelf ∧
    (ff (.outer (v.sourceOuter i).1.val (v.sourceOuter i).2.val)).board.purchaseOut=(repair C (.outer p a)).purchaseOut ∧
    (ff (.outer (v.sourceOuter i).1.val (v.sourceOuter i).2.val)).board.boughtFields 6=(repair C (.outer p a)).boughtFields 6
  rw [pa]
  exact ⟨v.same_shelf z width K G H R bits idBase b (emptyDirectory n) dir p.val a.val,
    v.same_flag z width K G H R bits idBase b (emptyDirectory n) dir p.val a.val,
    v.same_menu z width K G H R bits idBase b (emptyDirectory n) dir p.val a.val⟩

theorem sourcePair_ofChart (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank) :
    let C:=v.nativeChart P z width r banks src tab dst owners
    dir= BoughtSockets.Directory.ofChart 0 0 0 0 0 (v.sourceAttempt) C
      (fun i=>((s).outer (v.sourceOuter i).1.val (v.sourceOuter i).2.val).market.shelf) := by
  intro C
  have projection (i : Fin n) :=
    v.sourcePair_uses z width K G H R bits idBase b r banks src tab dst owners
      (v.sourceOuter i).1 (v.sourceOuter i).2
  have pack (i : Fin n) : finProdFinEquiv ((v.sourceOuter i).1,(v.sourceOuter i).2)=i :=
    finProdFinEquiv.apply_symm_apply i
  have shelves : (dir).shelf = fun i=>((s).outer (v.sourceOuter i).1 (v.sourceOuter i).2).market.shelf :=
    funext fun i=>by simpa only [pack] using (projection i).1
  have flags : (dir).flagBase = fun i=>(repair C (v.sourceAttempt i)).purchaseOut :=
    funext fun i=>by simpa only [pack,sourceAttempt] using (projection i).2.1
  have menus : (dir).menuBase = fun i=>(repair C (v.sourceAttempt i)).boughtFields 6 :=
    funext fun i=>by simpa only [pack,sourceAttempt] using (projection i).2.2
  change BoughtSockets.Directory.mk 0 0 0 0 0 (dir).shelf (dir).flagBase (dir).menuBase = _
  rw [shelves,flags,menus]; rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
