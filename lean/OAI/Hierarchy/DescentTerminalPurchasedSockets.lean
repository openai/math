import OAI.Hierarchy.DescentTerminalSiteControls
import OAI.Hierarchy.DescentTerminalPlacedChipInit
import OAI.Hierarchy.DescentTerminalPurchasedFields
import OAI.Hierarchy.DescentTerminalMaskedReached

namespace OAI
/-! # Original primitive field reads at the true reached row in the terminal sockets -/
namespace Hierarchy.DescentSixParty.Reached
open DescentCompiler DescentColonies DescentTerminalGraphPositions
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k age z degree wire hist p : ℕ}
    {bits : P → ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ} {σ : AtomSchedule}
    (live : Reached W G price ε σ k age z degree wire hist) (order : Order W.graph (σ.hostSize age) p)
    (same : order.home=live.home)

omit [Fintype P] in
theorem rawResident_coordinate (i : Fin (σ.hostSize age)) (v : Fin (Fintype.card (order.Nodes i))) :
    live.rawResident order same i v =
      finProdFinEquiv ((live.placement.pos (order.node i v)).1,live.placement.block (order.node i v)) := rfl

end
end Hierarchy.DescentSixParty.Reached

namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalVertexFields DescentTerminalRowArena
open DescentTerminalPrimitiveFrames
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
variable {blocks v B w : ℕ} (V : Home.Format) (S : DescentTerminalCompiledPrefix.Shape) (I : Input)
    (R : MaskAllocation.Channels blocks) (start header : ℕ)
    (short : v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
    (literal : DescentTerminalEmitter.Compact.Literals I.sources)
local notation "C" => meter V R start
local notation "O" => registers V S R start header
local notation "base" => afterMeter V S R start
local notation "L" => layout S I base O
local notation "A" => rowArena S I base

theorem original_sockets (m : Memory w) (earlier : Earlier S I base (C).layout w) (fits : last V S I R start<2^w)
    {x : ℕ} (low : x<start) :
    Suffix.sockets S L ((A).mount (input V S I R start header short literal m)) x = m x := by
  have floor : start≤base := by change start≤ start+_+_+_+_+3; omega
  exact (sockets_prior S I base O (C).layout _ (suffix_room S I base (C).layout O earlier fits) (low.trans_le floor)).trans
    (input_frame V S I R start header short literal m (.inl low))

/-- Read a whole original packed input word at the true socket date. This
works at every row, including the invalid and padded group/block positions. -/
theorem sockets_measured (m : Memory w) (earlier : Earlier S I base (C).layout w) (fits : last V S I R start<2^w)
    (below : ∀f,(R.bank f).base+(R.bank f).size≤ start) {shops : ℕ} (i : Fin shops) :
    measured (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes) («A»:=V.addresses)
      (w:=V.piece) (groups:=V.groups) (C).layout
      (Suffix.sockets S L ((A).mount (input V S I R start header short literal m))) i =
    measured (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes) («A»:=V.addresses)
      (w:=V.piece) (groups:=V.groups) (C).layout m i := by
  funext f
  have saved := bank_below m _ (R.bank f) start (below f)
    (fun _ low => original_sockets V S I R start header short literal m earlier fits low) (i.val:Computability.VPVNP.BurstRAM.Word w)
  simp only [measured,show (C).layout.channel f=R.bank f from rfl,saved]

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

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

open DescentTerminalCompiledPrefix
open DescentTerminalCompiledPrefix.AddressPlan
set_option quotPrecheck false
local notation "vfmt" => (⟨q,tagCount,hid,N,M,p,groups⟩ : Home.Format)
variable (layoutS : DescentTerminalCompiledPrefix.Shape) (I : AddressPlan.Input)
    (header : ℕ) {verts chipBits : ℕ} (oneWord : verts*span q (DescentBundleTagKeys.capacity n a g p r) hid N M p≤chipBits)
    (literal : DescentTerminalEmitter.Compact.Literals I.sources)
local notation "next" => afterMeter vfmt layoutS chan maskBase
local notation "regs" => registers vfmt layoutS chan maskBase header
local notation "terminal" => AddressPlan.layout layoutS I next regs
local notation "socketsAfter" => Suffix.sockets layoutS terminal ((rowArena layoutS I next).mount
  (input vfmt layoutS I chan maskBase header oneWord literal after))

include coords ranked short whole common bound limit inputs romEnd bounded mounted fit read prior ports chips birthFit printed here actorWord populationWord in
theorem purchased_sockets (nextStage : (ar).finish start≤ maskBase)
    (earlier : Earlier layoutS I next machine wb) (word : last vfmt layoutS I chan maskBase<2^wb) :
    PrimitiveReceipts (q:=q) (layout.site host) recipes localNames hH hN hA z
      (venueField (cellAt (meas socketsAfter h) (finProdFinEquiv (g₀,b)))) := by
  have pos : 0<(ar).columns := by
    change 0 < columns A.cap N M
    unfold columns
    omega
  have kit := (ar).realized start pop occupied bound limit pos
  have low (f : Fin (channels blocks)) : ((chan).bank f).base+((chan).bank f).size≤ maskBase := by
    obtain ⟨⟨block,field⟩,rfl⟩ := finProdFinEquiv.surjective f
    refine Fin.cases ?_ (fun field => ?_) field
    · exact (congrArg (fun row : Bank => row.base+row.size)
        (MaskAllocation.Channels.occupied_at chan block)).le.trans ((kit.live_inputs block).1.2.2.trans nextStage)
    · exact (congrArg (fun row : Bank => row.base+row.size)
        (MaskAllocation.Channels.primitive_at chan block field)).le.trans
          (((ar).live_end start pop occupied bound block field).trans nextStage)
  have moved := sockets_measured vfmt layoutS I chan maskBase header oneWord literal after earlier word low h
  have paid := purchased (q:=q) (hid:=hid) (N:=N) (M:=M) (blocks:=blocks) (shops:=shops) (groups:=groups)
    (wb:=wb) (d0:=d0) (n:=n) (a:=a) (g:=g) (r:=r)
    A native S ready homes coords hp layout host z rs sh old orders aliases hH hN hA short port ranked
    scale psize whole common t config index frozenBits pages initial original raw advice start pop maskBase occupied
    bound limit inputs romEnd bounded mounted fit b h g₀ read prior ports chips birthFit printed
    homeOf groupOf blockOf here actorWord populationWord
  exact (congrArg (fun rows => PrimitiveReceipts (q:=q) (layout.site host) recipes localNames hH hN hA z
    (venueField (cellAt rows (finProdFinEquiv (g₀,b))))) moved).mpr paid

end
end Hierarchy.DescentTerminalPrimitiveArena

end OAI
