import OAI.Hierarchy.DescentMountedRotorSpan
import OAI.Hierarchy.DescentOriginalPublicOperandBoard
import OAI.Hierarchy.DescentNativeFreshRangePlaces

namespace OAI
/-! # Transport of the mounted range law to a recorded board and operand configuration -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentKernelHistory DescentPhysicalSplit DescentResetGates DescentLaneGates DescentFallbackItemSelect
open DescentSIMDLookup DescentRetainedRangeDigits DescentBundleHistory DescentResetPublicOperandBook
open DescentResetOperandSetup DescentRotor DescentRouterSlots DescentBatchedNodeOrder
open DescentDenseHostOrder LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
open DescentChosenRouter DescentMixedRouter DescentBatchedBank DescentBaseProfile

/-- The complete mounted rotor test, with the numerical field reader kept fixed while
the finite graph, native configuration, and measured row change presentation. -/
def MountedRotorLaw {n h : ℕ} (board : NonlinearExpanders.Graph n h) (c : Config) (row : c.Data n)
    (index slot width : ℕ) (read : Fin 3→ℕ) : Prop :=
  ∀{V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
    {k unit N : ℕ} (placement : Placement V I H A k (2^n)) (hw : 0<c.rotor.packet) (pay : ℝ)
    (hardware : Hardware (K:=K) (C₀:=c.multiplicity) (u:=unit) placement board hw pay)
    (key : I↪Fin N) (d : ℕ) (hp : 0<c.grain) (fit : unit=c.rotor.batches*c.grain)
    (side : Bool) (root : placement.Good) (actor : (DescentCommonPalette.rotor board).Site),
    let sel:=selected placement board hw pay hardware
    let bank:=DescentMixedRouter.network board hw unit placement.contact placement.input placement.site
      placement.owner placement.align sel d
    let site : placement.Site:=.inl root
    let installedSite := DescentCommonPalette.rotorSiteEquiv board d
      (selectedRotorLayers placement board hw pay hardware side root) c.multiplicity c.rotor.packet unit actor
    let venue : bank.Site:=⟨(side,site),installedSite⟩
    let prog:=sizedProgram board hw unit c.rotor.batches c.grain hp fit placement.contact placement.input
      placement.site placement.owner placement.align key d sel venue
    let ord:=sizedOrder board hw c.rotor.batches c.grain hp placement.contact placement.input placement.site
      placement.owner placement.align key d unit fit sel venue
    let fund:=(fit ▸ hardware : Hardware (K:=K) (C₀:=c.multiplicity) (u:=c.rotor.batches*c.grain)
      placement board hw pay) side root
    ∀(multiple : ∀e,boundaryWidth bank venue e=boundaryWidth bank venue e/c.grain*c.grain)
      (gate : prog.Node) (badge : ↥(roster board c.rotor.residual c.rotor.depth))
      (ticket : DescentResetHostSize.Code c.rotor.residual)
      (slots : Cells placement side root↪Fin c.oldConfig.count),
      index=(ord gate).val → (c.reg row 1).val=ticket.val.1+1 → (c.reg row 2).val%2=0 →
      (c.reg row 3).val=(localRank board c.rotor.residual c.rotor.depth badge).val →
      (c.oldConfig.header (c.basic row) 2).val=(localRank board c.rotor.residual c.rotor.depth badge).val →
      badge.val=.good side ((),ticket.val.2) actor →
      DescentRecordedRotorLayers.layers n c.rotor.packet c.rotor.gain ((c.reg row 0).val)=fund.layers →
      fund.layers*c.rotor.batches≤c.rotor.addresses →
      (∀e,c.endpoints side ticket row (slots e)=some (DescentChosenRouter.source placement side root e,DescentChosenRouter.target placement side root e)) →
      (∀j,(¬∃e,slots e=j)→c.endpoints side ticket row j=none) →
      (∀e₁ e₂,before (c.oldItem row side) (slots e₁) (slots e₂) ↔ key e₁.val<key e₂.val) →
      c.traffic row side ticket=matrixOfBundles (DescentChosenRouter.source placement side root) (DescentChosenRouter.target placement side root) →
      2<2^width → ∀axis,
        let sh:=ofProgram (fun e=>boundaryWidth bank venue e/c.grain) multiple hp prog
        atSlot sh gate slot axis<2^width → read axis=atSlot sh gate slot axis

theorem MountedRotorLaw.relabel {n n' d d' : ℕ} {board : NonlinearExpanders.Graph n d}
    {after : NonlinearExpanders.Graph n' d'} {c c' : Config} {row : c.Data n} {index slot width read}
    (law : MountedRotorLaw board c row index slot width read)
    (config : c=c') (dim : n=n') (degree : d=d') (graph : HEq board after) :
    MountedRotorLaw after c' (Config.relabel config dim row) index slot width read :=by
  subst c'
  subst n'
  subst d'
  cases eq_of_heq graph
  exact law

def RotorBadge {n d : ℕ} (board : NonlinearExpanders.Graph n d) (c : Config) (row : c.Data n) : Prop :=
  ∃s : ↥(roster board c.rotor.residual c.rotor.depth),
    (c.reg row 3).val=(localRank board c.rotor.residual c.rotor.depth s).val ∧
      ∀key,s.val≠.trunk false key

theorem register_relabel {n n' : ℕ} {c c' : Config} (row : c.Data n) (shape : c=c')
    (dim : n=n') (j : Fin 4) :
    (c'.reg (Config.relabel shape dim row) j).val=(c.reg row j).val:=by
  subst c'
  subst n'
  rfl

theorem RotorBadge.relabel_iff {n n' d d' : ℕ} {board : NonlinearExpanders.Graph n d}
    {after : NonlinearExpanders.Graph n' d'} {c c' : Config} (row : c.Data n)
    (config : c=c') (dim : n=n') (degree : d=d') (graph : HEq board after) :
    RotorBadge board c row ↔ RotorBadge after c' (Config.relabel config dim row) :=by
  subst c'
  subst n'
  subst d'
  cases eq_of_heq graph
  rfl

variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "cfg" => publicOperands z roots menu.payload
local notation "C" => a.successor.setup
local notation "R" => (cfg).rotor
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)
    (Y : Fin (a.successor.setup.retained.outputs*a.successor.setup.placement.shapes)→Fin a.successor.setup.placement.oldHosts→
      Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.retained.bits)
    (j : Fin a.successor.setup.retained.outputs) (blk : Fin a.successor.setup.placement.blocks)
    (h : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
    (x : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits) (arg : Fin (publicOperands z roots menu.payload).args) (node : Fin (publicOperands z roots menu.payload).nodes)
    (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val=0 → ((publicOperands z roots menu.payload).reg x 1).val=0)
    (physical : ∀hv : h.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0 →
      ((publicOperands z roots menu.payload).reg x 3).val=(a.successor.setup.placement.shape (name ⟨h.val,hv⟩)).val)
    (fresh : ∀hv : h.val<U,menu.keep (a.successor.setup.placement.shape (name ⟨h.val,hv⟩))=false)
local notation "mouth" => finProdFinEquiv (arg,node)
local notation "word" f:arg => menu.spanValue name Y j blk h g x mouth (page f) blank physical
local notation "prv" f:arg => (R).flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split node.val arg.val
   (page f).succ ((cfg).reg x)
local notation "surface" f:arg => ((cfg).column z.board (C).fieldBits (some (page f)) mouth x).val

include fresh in
theorem measured_mounted_rotor :
    MountedRotorLaw z.board cfg x node.val arg.val (C).fieldBits (fun f=>(word f).val) :=by
  intro V I H A K fv dv fi fh fa fk k unit N placement hw pay hardware key d hp fit side root actor
  dsimp only
  intro multiple gate badge ticket slots numbered depth safe seen headSeen good measured seats
    present missing sorted traffic room axis fitField
  exact menu.mounted_rotor_span name Y j blk h g x arg node blank physical fresh placement hw pay hardware
    key d hp fit side root actor multiple gate numbered badge ticket depth safe seen headSeen good measured
    seats axis fitField slots present missing sorted traffic room

include blank physical in
theorem measured_mounted_at_badge (born : RotorBadge z.board cfg x)
    (live : ((cfg).oldConfig.header ((cfg).basic x) 0).val≠0) :
    MountedRotorLaw z.board cfg x node.val arg.val (C).fieldBits (fun f=>(word f).val) :=by
  obtain ⟨badge,numbered,kind⟩:=born
  apply menu.measured_mounted_rotor name Y j blk h g x arg node blank physical
  exact menu.newborn_slot name h x physical badge live numbered kind

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
