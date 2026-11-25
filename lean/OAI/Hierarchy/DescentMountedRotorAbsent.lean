import OAI.Hierarchy.DescentMountedRotorTransport

namespace OAI
/-! # The measured rotor fields above its installed node count -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentKernelHistory DescentPhysicalSplit DescentResetGates DescentLaneGates DescentFallbackItemSelect
open DescentSIMDLookup DescentRetainedRangeDigits DescentBundleHistory DescentResetPublicOperandBook
open DescentResetOperandSetup DescentRotor DescentRouterSlots DescentBatchedNodeOrder
open DescentDenseHostOrder LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
open private transportCircuit from OAI.Hierarchy.DescentInstalledNames
open DescentChosenRouter DescentMixedRouter DescentBatchedBank DescentBaseProfile

def MountedRotorAbsentLaw {n h : ℕ} (board : NonlinearExpanders.Graph n h) (c : Config) (row : c.Data n)
    (index : ℕ) (read : Fin 3→ℕ) : Prop :=
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
    let fund:=(fit ▸ hardware : Hardware (K:=K) (C₀:=c.multiplicity) (u:=c.rotor.batches*c.grain)
      placement board hw pay) side root
    ∀(badge : ↥(roster board c.rotor.residual c.rotor.depth))
      (ticket : DescentResetHostSize.Code c.rotor.residual),
      Fintype.card prog.Node≤ index → (c.reg row 1).val=ticket.val.1+1 → (c.reg row 2).val%2=0 →
      (c.reg row 3).val=(localRank board c.rotor.residual c.rotor.depth badge).val →
      (c.oldConfig.header (c.basic row) 2).val=(localRank board c.rotor.residual c.rotor.depth badge).val →
      badge.val=.good side ((),ticket.val.2) actor →
      DescentRecordedRotorLayers.layers n c.rotor.packet c.rotor.gain ((c.reg row 0).val)=fund.layers →
      ∀axis,read axis=0

theorem MountedRotorAbsentLaw.relabel {n n' d d' : ℕ} {board : NonlinearExpanders.Graph n d}
    {after : NonlinearExpanders.Graph n' d'} {c c' : Config} {row : c.Data n} {index read}
    (law : MountedRotorAbsentLaw board c row index read)
    (config : c=c') (dim : n=n') (degree : d=d') (graph : HEq board after) :
    MountedRotorAbsentLaw after c' (Config.relabel config dim row) index read :=by
  subst c'
  subst n'
  subst d'
  cases eq_of_heq graph
  exact law

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

include blank physical in
theorem measured_mounted_absent_at_badge (born : RotorBadge z.board cfg x)
    (live : ((cfg).oldConfig.header ((cfg).basic x) 0).val≠0) :
    MountedRotorAbsentLaw z.board cfg x node.val (fun f=>(word f).val) :=by
  obtain ⟨where_,at_,kind⟩:=born
  have free:=menu.newborn_slot name h x physical where_ live at_ kind
  intro V I H A K fv dv fi fh fa fk k unit N placement hw pay hardware key d hp fit side root actor
  dsimp only
  intro badge ticket absent depth safe seen headSeen good measured axis
  have count:=Fintype.card_congr (mountedGoodNode placement z.board hw pay hardware key d
    (R).batches (cfg).grain hp fit side root actor)
  let hwSized : Hardware (K:=K) (C₀:=(cfg).multiplicity) (u:=(R).batches*(cfg).grain) placement z.board hw pay :=
    fit ▸ hardware
  let itemEnum := @Subtype.fintype I (fun e => placement.owner side (placement.contact e) = .inl root)
    (fun _ => Classical.propDecidable _) fi
  let chip := transportCircuit (b:=itemEnum) (G:=z.board) (hw:=hw) (pay:=pay) (hwSized side root)
  let sites := DescentCommonPalette.rotorSiteEquiv z.board d
    (selectedRotorLayers placement z.board hw pay hwSized side root) (cfg).multiplicity (R).packet ((R).batches*(cfg).grain)
  have placed : badge.val=.good side ((),ticket.val.2) (sites.symm (sites actor)) := by
    rw [sites.symm_apply_apply]
    exact good
  have resized := selectedRotorLayers_eq placement z.board hw pay hwSized side root
  exact menu.physical_rotor_absent name Y j blk h g x arg node blank physical free d hp placement.contact placement.input
    placement.site placement.owner placement.align side (.inl root) (head placement side root) (DescentChosenRouter.tail placement side root)
    chip key (sites actor) (count.symm.le.trans absent) badge ticket depth safe seen headSeen placed (measured.trans resized.symm) axis

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
