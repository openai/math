import OAI.Hierarchy.DescentTerminalPrimitiveSchedule
import OAI.Hierarchy.DescentTerminalNormalizedFields

namespace OAI
/-! # Semantic readback of the purchased six-field program on a true normalized branch site -/
namespace Hierarchy.DescentTerminalPrimitiveArena
open Computability.BorderVNP.Crossing DescentSixParty DescentSharedCableNames DescentKernelHistory DescentTerminalPortChart
open DescentBundleHistory DescentCompiler DescentColonies DescentLocalPrivateNames
open DescentOperandStateBanks DescentTerminalPointerDigits DescentTerminalChronologicalBooks DescentTerminalGraphPositions
open DescentTerminalPointerIssue DescentTerminalVertexFields DescentTerminalSiteShelves DescentEpochTagKeys
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentSIMDLookup
open ThreeFlat.Routing ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 600000
variable {F P J V U:Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k step p q N M K H0 n a g r:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:AtomSchedule) (ready:A.StateBounds S step)
    (homes:Stage.Host J V k↪ℕ) (coords:Function.Injective (fun s=>(A.pos s,A.block s))) (hp:0<p)
    (layout:Order W.graph H0 p) (host:Fin H0) (z:Fin (layout.site host).nodes)
    (rs:∀v:W.graph.Site,BitRecipe U (Boundary W.graph v) (boundaryWidth W.graph v))
    (sh:∀v,DescentBundleHistory.Shape p (rs v)) (old:Codec U n)
local notation "tagCount" => DescentBundleTagKeys.capacity n a g p r
local notation "code" => (DescentBundleTagKeys.codec old a g p r).store
local notation "atNode" => layout.node host z
local notation "recipe" => fun v=>(sh v).recipe hp
variable (orders:∀v,((fun v=>(sh v).recipe hp) v).Node↪ℕ) (aliases:∀v,Slot ((fun v=>(sh v).recipe hp) v)↪Fin K)
local notation "recipes" => DescentTerminalBundleRows.recipes layout (fun v=>(recipe v).restricted) hp orders code host
local notation "localNames" => DescentTerminalNormalizedFields.birth hp layout host rs sh code orders aliases
variable {hid groups blocks shops wb d0:ℕ}
    (hH:∀y,Fintype.card ((DescentTerminalBundleRows.recipes layout (fun v=>((fun v=>(sh v).recipe hp) v).restricted) hp orders ((DescentBundleTagKeys.codec old a g p r).store) host) y).Hidden≤hid) (hN:∀y,Fintype.card ((DescentTerminalBundleRows.recipes layout (fun v=>((fun v=>(sh v).recipe hp) v).restricted) hp orders ((DescentBundleTagKeys.codec old a g p r).store) host) y).Node≤N)
    (hA:∀y u,((DescentTerminalBundleRows.recipes layout (fun v=>((fun v=>(sh v).recipe hp) v).restricted) hp orders ((DescentBundleTagKeys.codec old a g p r).store) host) y).arity u≤M) (short:∀y,(layout.site host).arity y≤q)
    (port:Attached W.graph (layout.node host z)↪ℕ) (ranked:layout.operandRank (layout.node host z)=rank A native S ready homes (layout.node host z) port)
    (scale psize:ℕ) (whole:A.z*G.b=scale*p)
    (common:∀j:Attached W.graph (layout.node host z),poolBatchCount (bits j.val) p=psize)
    (t:CellInputs A.degree A.cap N M) (config:Widths) (index:ℕ→ℕ→ℕ→ℕ) (frozenBits:ℕ)
    (pages:Gather.Pages blocks A.cap M) (initial original:Memory wb)
    (raw:Fin 6→Bank) (advice start pop maskBase:ℕ) (occupied:Fin blocks→Bank)
local notation "wholeBits" => groups*span q tagCount hid N M p
local notation "ar" => actual blocks shops A.cap N M d0 wholeBits
local notation "bits6" => fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups
local notation "first" => DescentTerminalRoleTables.role bits6 raw advice
local notation "second" => DescentTerminalRoleTables.arity bits6 raw advice
local notation "warm" => DescentTerminalCombinedRole.memory first second start (ar).rows initial
local notation "chan" => (ar).channels start pop occupied
local notation "machine" => MaskAllocation.shelf (q:=q) (t:=tagCount) (H:=hid) (N:=N) (A:=M) (p:=p) (groups:=groups) chan maskBase
local notation "meas" => measured (q:=q) (t:=tagCount) (H:=hid) (N:=N) (A:=M) (w:=p) (groups:=groups) machine
local notation "f0" => publicCell (cap:=A.cap) (N:=N) (A:=M) (d:=d0) A.degree q scale psize frozenBits groups config
local notation "f7" => output A.cap N M A.degree groups d0 (Nat.clog 2 (q+hid+1)) q scale psize config index
local notation "after" => image (n:=n) (a:=a) (g:=g) (p:=p) (r:=r) (N:=N) (groups:=groups)
  (shops:=shops) (dc:=wholeBits) raw advice start pop pages f0 f7 q hid initial
variable (bound:(actual blocks shops A.cap N M d0 (groups*span q (DescentBundleTagKeys.capacity n a g p r) hid N M p)).Prior start pop occupied) (limit:(actual blocks shops A.cap N M d0 (groups*span q (DescentBundleTagKeys.capacity n a g p r) hid N M p)).finish start<2^wb)
    (inputs:∀f,(raw f).Fits wb start) (romEnd:advice+DescentTerminalRoleTables.count (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups)≤ start)
    (bounded:∀ (j:Fin (columns A.cap N M)) (b:Fin blocks),(pages.address (N:=N) j b).Fits ((actual blocks shops A.cap N M d0 (groups*span q (DescentBundleTagKeys.capacity n a g p r) hid N M p)).gather start) shops wb)
    (mounted:∀j,advice≤j→j<advice+DescentTerminalRoleTables.count (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups)→initial j=
      DescentStaticWordColumn.image advice
        (DescentTerminalRoleTables.literal (A:=a) (G:=g) (p:=p) (R:=r) (N:=N) (groups:=groups) old M)
        original (DescentTerminalRoleTables.count (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups)) j)
    (fit:(groups*span q (DescentBundleTagKeys.capacity n a g p r) hid N M p)≤wb) (b:Fin blocks) (h:Fin shops) (g₀:Fin groups)
local notation "cell" => pages.source (N:=N) (d:=d0) warm b h
local notation "rk" => rank A native S ready homes atNode port
local notation "nodeAt" => fun u=>(ordinal (orders atNode) u).castLE (hN z)
local notation "roleData" => DescentTerminalCombinedRole.observed (n:=n) (A:=a) (G:=g) (p:=p) (R:=r) (N:=N) (M:=groups)
variable (read:SourceRead config (pages.source (N:=N) (d:=d0) (DescentTerminalCombinedRole.memory (DescentTerminalRoleTables.role (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups) raw advice) (DescentTerminalRoleTables.arity (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups) raw advice) start (actual blocks shops A.cap N M d0 (groups*span q (DescentBundleTagKeys.capacity n a g p r) hid N M p)).rows initial) b h) g₀.val t)
    (prior:Origin W.graph (layout.node host z) ((fun v=>(sh v).recipe hp) (layout.node host z)) (orders (layout.node host z)) (hN z) (hA z) (aliases (layout.node host z)) (rank A native S ready homes (layout.node host z) port) port
      (reindexed t (index ((pages.source (N:=N) (d:=d0) (DescentTerminalCombinedRole.memory (DescentTerminalRoleTables.role (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups) raw advice) (DescentTerminalRoleTables.arity (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups) raw advice) start (actual blocks shops A.cap N M d0 (groups*span q (DescentBundleTagKeys.capacity n a g p r) hid N M p)).rows initial) b h) mcol).val ((pages.source (N:=N) (d:=d0) (DescentTerminalCombinedRole.memory (DescentTerminalRoleTables.role (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups) raw advice) (DescentTerminalRoleTables.arity (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups) raw advice) start (actual blocks shops A.cap N M d0 (groups*span q (DescentBundleTagKeys.capacity n a g p r) hid N M p)).rows initial) b h) fcol).val)))
    (ports:DescentTerminalFrozenRoster.length frozenBits ((pages.source (N:=N) (d:=d0) (DescentTerminalCombinedRole.memory (DescentTerminalRoleTables.role (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups) raw advice) (DescentTerminalRoleTables.arity (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups) raw advice) start (actual blocks shops A.cap N M d0 (groups*span q (DescentBundleTagKeys.capacity n a g p r) hid N M p)).rows initial) b h) fcol).val=Fintype.card (Attached W.graph (layout.node host z)))
    (chips:t.chips=Stage.signedPanel A native S ready homes (Stage.home A (layout.node host z)))
    (birthFit:∀u,old.fits ((rs (layout.node host z)).tag u))
    (printed:∀u,DescentTerminalCombinedRole.Printed old (DescentTerminalCombinedRole.fields
      (DescentTerminalCombinedRole.node ((DescentTerminalCombinedRole.observed (n:=n) (A:=a) (G:=g) (p:=p) (R:=r) (N:=N) (M:=groups)) (DescentTerminalRoleTables.role (fun f:Fin 6=>DescentTerminalCombinedRole.width n a g p r f*N*groups) raw advice) initial ((finProdFinEquiv (b,h)).val:Computability.VPVNP.BurstRAM.Word wb)) g₀ ((fun u=>(ordinal (orders (layout.node host z)) u).castLE (hN z)) u)))
        ((rs (layout.node host z)).tag u) ((sh (layout.node host z)).sliceFields u))
    (homeOf:W.graph.Site→Fin shops) (groupOf:W.graph.Site→Fin groups) (blockOf:W.graph.Site→Fin blocks)
    (here:homeOf (layout.node host z)=h ∧ groupOf (layout.node host z)=g₀ ∧ blockOf (layout.node host z)=b)
    (actorWord:initial ((occupied b).base+h.val)=((encode 1 groups (fun j=>
      (if ∃v,homeOf v=h ∧ groupOf v=j ∧ blockOf v=b then 1 else 0):Fin groups→Cell 1)).val:Computability.VPVNP.BurstRAM.Word wb))
    (populationWord:digit (Nat.clog 2 (N+1)) g₀.val (initial (pop+b.val*shops+h.val)).val=Fintype.card ((fun v=>(sh v).recipe hp) (layout.node host z)).Node)

include coords ranked short whole common bound limit inputs romEnd bounded mounted fit read prior ports chips birthFit printed here actorWord populationWord in
theorem purchased :
    PrimitiveReceipts (q:=q) (layout.site host) recipes localNames hH hN hA z
      (venueField (cellAt (meas after h) (finProdFinEquiv (g₀,b)))) := by
  have pos : 0 < (ar).columns := by
    change 0 < columns A.cap N M
    unfold columns
    omega
  have kit:=(ar).realized start pop occupied bound limit pos
  have early:=(ar).paired_fits start limit bits6 raw advice inputs romEnd
  have romRoom:advice+DescentTerminalRoleTables.count bits6<2^wb:=by have:=kit.role_first;omega
  have tables:=DescentTerminalRoleTables.persistent (A:=a) (G:=g) (p:=p) (R:=r) (N:=N) (groups:=groups)
    old M raw advice original romRoom initial mounted
  have familyFits (f:Fin 8) : familySize (q:=q) (t:=tagCount) (H:=hid) (N:=N) (A:=M) (w:=p) f*groups≤wholeBits:=by
    let widths := widthAt (q:=q) (t:=tagCount) (H:=hid) (N:=N) (A:=M) (w:=p) groups
    have le : widths f ≤ ∑ j, widths j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (widths j)) (Finset.mem_univ f)
    rw [Nat.mul_comm]
    exact le.trans_eq (DescentTerminalVertexFields.volume (q:=q) (t:=tagCount) (H:=hid) (N:=N) (A:=M) (w:=p) (V:=groups))
  have strength (f:Fin 8):familySize (q:=q) (t:=tagCount) (H:=hid) (N:=N) (A:=M) (w:=p) f*groups≤wb:=(familyFits f).trans fit
  have one:groups≤wb:=by simpa [familySize,items,itemBits] using strength 1
  have f₀:Nat.clog 2 (q+1)*groups≤wb:=by simpa [familySize,items,itemBits] using strength 0
  have f₇:Nat.clog 2 (q+hid+1)*(N*M)*groups≤wb:=by
    simpa [familySize,items,itemBits,Nat.mul_comm (N*M)] using strength 7
  have f₅:DescentTerminalCombinedRole.output n a g p r*N*groups≤wb:=by
    simpa [familySize,items,itemBits,DescentTerminalCombinedRole.output,Nat.mul_comm N] using strength 5
  have f₆:Nat.clog 2 (M+1)*N*groups≤wb:=by simpa [familySize,items,itemBits,Nat.mul_comm N] using strength 6
  have fieldBank (f : Fin 8) :
      (machine).channel (finProdFinEquiv (b,f.succ))=(chan).primitive b f :=
    MaskAllocation.Channels.primitive_at chan b f
  have issue_:=DescentTerminalNormalizedFields.primitive_from_birth
    (q:=q) (tags:=tagCount) (hid:=hid) (N:=N) (M:=M) (blocks:=blocks) (shops:=shops) (groups:=groups)
    (wb:=wb) (d0:=d0) (dCount:=wholeBits) (palette:=n) (aMax:=a) (chunks:=g) (stride:=r) A native S ready homes coords hp layout host z rs sh code
    orders aliases hH hN hA short port ranked scale psize whole common t config index frozenBits pages warm
    ((ar).gather start) chan maskBase b h g₀ bounded kit.pointer_radix kit.pointer_limit f₀ f₇ rfl rfl
    (kit.keep_family b 0) (kit.keep_family b 7) read prior ports chips ((ar).sources start pop) ((ar).counting start) ((ar).widths start)
    kit.source_room kit.count_later kit.width_limit fit (kit.from_base b) (fun f=>kit.keep_family b (DescentTerminalPrivateSourceChannels.family f))
    (fun f=>familyFits (DescentTerminalPrivateSourceChannels.family f)) rfl (kit.keep_family b 2) rfl (kit.keep_family b 4)
    rfl (kit.pointer_prior b) (kit.count_prior b) kit.phase_order.2 old first second start initial rfl (fun _=>rfl)
    early.1 early.2 kit.role_first tables.1 tables.2 rfl f₅ f₆
    (congrArg Bank.base (fieldBank 5))
    (congrArg Bank.base (fieldBank 6))
    ((kit.keep_family b 5).trans_eq (congrArg Bank.size (fieldBank 5)).symm)
    ((kit.keep_family b 6).trans_eq (congrArg Bank.size (fieldBank 6)).symm)
    birthFit printed (kit.old_actor b) (kit.old_population b) kit.phase_order.1 rfl homeOf groupOf blockOf here
    (kit.keep_actor b) one actorWord populationWord
  exact issue_.2.2.1

end
end Hierarchy.DescentTerminalPrimitiveArena

end OAI
