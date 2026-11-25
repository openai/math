import OAI.Hierarchy.DescentReachedPhysicalPinJob
import OAI.Hierarchy.DescentOrdinaryBornDigits
import OAI.Hierarchy.DescentRegisteredMouthPrefix

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentPacking.PackedMatch.Local.Stage.Chooser ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentRawCablePanel
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
variable (floor : ℕ) (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
local notation "rc₀" => v.resolver
local notation "vx₀" => v.vector
local notation "bn₀" => v.bornBook
local notation "mouth₀" => v.mouthChart mat.newBlocks

local notation "Val₀" => References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes
  v.reference.capacity ((rc₀).size+2)

open DescentScalarBookReshape DescentOrdinaryBorn DescentOrdinaryMouthReturn

private theorem vals_at_pair
    (L : DescentOrdinaryMouthReturn.Layout) {nb mb : ℕ}
    (V : Fin L.B.args → Fin L.lows → L.Val nb mb)
    (chip : Fin L.B.hosts → Fin L.B.groups → Cell L.B.chipBits)
    (arg : Fin L.B.args) (field : Fin 3) (low : Fin L.lows) :
    L.vals V chip (finProdFinEquiv (arg,field)) low = (V arg low).withBirth
        (fun b slot party h g => RolePorts.value L.B.bits
          (pointerAt L.B.demand L.B.grain L.B.scale
            (chipDonor L.B.format (chip h g) (finProdFinEquiv (b.cast L.blocks_eq.symm,slot)))
            party arg.val) field) := by
  unfold DescentOrdinaryMouthReturn.Layout.vals
  rw [Equiv.symm_apply_apply]
  rfl

private theorem mouth_header_read {nb mb : ℕ} (rows : Val₀ nb mb)
    (chip : Fin (bn₀).hosts → Fin (bn₀).groups → Cell (bn₀).chipBits)
    (homes : (bn₀).hosts = (vx₀).hosts)
    (groups : (bn₀).groups = (vx₀).groups * (vx₀).radix)
    (bitsEq : (bn₀).bits = (rc₀).size + 2)
    (block : Fin (vx₀).radix) (node : Fin (rc₀).nodes) (arg : Fin (rc₀).operands)
    (field : Fin 3) (host : Fin ((vx₀).hosts * (vx₀).lows)) (groupId : Fin (vx₀).groups) :
    let j := (rc₀).index (block.cast shape.blocks.symm, node, arg)
    let sourceArg := arg.cast (shape.operands.trans mat.newArgs.symm)
    let born := fun (b : Fin (2^v.reference.k)) (s : Fin (bn₀).cap) (t : Fin 6)
        (h : Fin (bn₀).hosts) (g : Fin (bn₀).groups) =>
      RolePorts.value (bn₀).bits
        (pointerAt (bn₀).demand (bn₀).grain (bn₀).scale
          (chipDonor (bn₀).format (chip h g) (finProdFinEquiv (b.cast mat.newBlocks.symm,s)))
          t arg.val) field
    (take (((rc₀).index.symm j).2.1)
      (v.mouthHeaderValue floor A mat shape (v.headerMouthRows floor A mat rows homes groups bitsEq)
        chip homes groups j field (host.cast shape.hosts.symm) (groupId.cast shape.groups.symm))).val =
    (take node (DescentScalarBookReshape.book
      (fun l x y =>
        ((HeaderWords.reindex mat.newCap.symm homes.symm groups.symm bitsEq.symm
          (rows (v.headerMouthPage floor A mat sourceArg) l)).withBirth born).book
          (rc₀).nodes x (y.cast groups.symm)) block
      (host.cast (congrArg (·*(vx₀).lows) homes.symm)) groupId)).val := by
  dsimp only
  simp only [mouthHeaderValue, Equiv.symm_apply_apply, HeaderWords.atShape, Fin.cast_cast, Fin.cast_refl]
  let src := arg.cast (shape.operands.trans mat.newArgs.symm)
  let header := v.headerMouthRows floor A mat rows homes groups bitsEq
  have allRows := funext (vals_at_pair (v.mouthChart mat.newBlocks) header chip src field)
  exact congrArg (fun vals : Fin (vx₀).lows → (mouth₀).Val nb mb =>
    (take node (DescentScalarBookReshape.book (fun l x y => (vals l).book (rc₀).nodes x (y.cast groups.symm))
      block (host.cast (congrArg (·*(vx₀).lows) homes.symm)) groupId)).val) allRows

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

/-! The three newborn role cells sampled by the registered ordinary argument job. -/
namespace Hierarchy.DescentLocalArchiveOrder.PaddedOrigin
open DescentNetworkPartition Computability.BorderVNP.Crossing
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 650000
set_option Elab.async false
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached (n).result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "r" => BitDescription.scannedRows he T
local notation "sw" => branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c)
local notation "next" => (ticket.advance arch).bit
local notation "layout" => bestLayout sw
local notation "group" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c

local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "bound" => DescentHaloWalkRAM.breadth deg*2^k

local notation "shelf"=>2^(packExponent 20 deg)+2
local notation "raw"=>2^(k+1)*shelf
local notation "walks₀"=>DescentHaloWalkRAM.breadth deg
local notation "K"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

open DescentPaidResidentCount
variable {mb : ℕ} (tokens : Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
local notation "stock" => Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket)
  (key∘group) cap.vertex (Function.Embedding.refl _) moves tokens

local notation "OH" => Fintype.card cap.V
local notation "OG" => S.groupCount i
variable (age : i<S.length) (radix : S.radix=2^k)

variable {w : ℕ} (ports : DatePorts) (mem : Memory w) (room : DatePorts.RangeRoom ports cap arch.bit)
    (population : Fintype.card cap.V≤ports.operandHosts)
local notation "K₀" => ports.nodes
local notation "fits₀" => maxNodes_le arch.bit room.capacity
local notation "oldN" => K₀
local notation "N₀" => DescentPackedActorMask.nodes bound oldN (A).cap
variable (prior : Local arch.bit)
variable (priorCount : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell mb)
variable (old_live : ∀u,(priorCount (cap.placement.block u) (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1).val=
    Fintype.card (arch.bit.recipe u).Node)
variable (old_empty : ∀b h g,(¬∃u,cap.placement.block u=b ∧ cap.vertex (cap.placement.pos u).2=h ∧ (cap.placement.pos u).1=g)→priorCount b h g=0)

open DescentOrdinaryAtomFieldRAM DescentRetainedRangeDigits DescentOrdinaryAtomFieldRAM.ScalarOperand DescentHaloWalkRAM


open DescentKernelHistory DescentBundleHistory DescentOperandStateBanks DescentDatedPriorOperand
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentPackedOperand
open PhysicalOrdinary DescentOrdinaryRasterReturn
variable {p:ℕ}
local notation "prof" => (r).profile c
local notation "pitch₁" => (2^(k+1)-1)*shelf
local notation "NG₁" => S.groupCount (i+1)
open DescentOrdinaryBorn DescentOrdinaryMouthReturn
variable (v:PhysicalOrdinary F P) (floor:ℕ) (entry:v.ArgumentEntry) (mat:entry.Match v floor)
    (shape:v.VectorShape) (degree:v.reference.degree=cap.placement.degree) (depth:v.reference.k=k)
    (oldNodes:v.reference.oldNodes=ports.nodes) (capacity:v.reference.capacity=cap.placement.cap)
    (lo:v.vector.lows=(2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2)) (gs:v.vector.groups=S.groupCount (i+1)) (rad:v.vector.radix=2^k)
    (field:v.resolver.size+2=ports.operandBits) (hostFit:Fintype.card cap.V≤v.vector.hosts)
    (homes:v.bornBook.hosts=v.vector.hosts) (groups:v.bornBook.groups=v.vector.groups*v.vector.radix)
    (bits_:v.bornBook.bits=v.resolver.size+2)
    (V:References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
      (v.resolver.size+2) (Packed.bits ((2^(k+1)-1)*(2^(packExponent 20 cap.placement.degree)+2))) mb)
    (chip:Fin v.bornBook.hosts→Fin v.bornBook.groups→Cell v.bornBook.chipBits)
    (born₀:Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell ports.operandBits)

local notation:max "prior₀" j:arg => DatePorts.physicalHeaderSource ports cap arch.bit room population mem j 0
local notation:max "rows₀" j:arg => rangeValues ticket arch tokens age radix priorCount (prior₀ j) born₀
local notation:max "from₀" j:arg => Values.originTransport degree depth oldNodes capacity lo gs rad field (rows₀ j)
local notation:max "arg₀" j:arg fit:arg => (⟨j,fit⟩:Fin v.resolver.operands).cast (shape.operands.trans mat.newArgs.symm)
local notation:max "part₀" x:arg => (target.placement.block x)
local notation:max "host₀" x:arg => hostIndex ticket (target.vertex (target.placement.pos x).2)
local notation:max "group₀" x:arg => (target.placement.pos x).1
local notation:max "column₀" x:arg => (part₀ x).cast rad.symm
local notation:max "outer₀" x:arg => ((host₀ x).cast (congrArg (OH*·) lo.symm))
local notation:max "rh" x:arg => ((widen hostFit (outer₀ x)).cast shape.hosts.symm)
local notation:max "rg" x:arg => (((group₀ x).cast gs.symm).cast shape.groups.symm)
local notation:max "slot₀" x:arg fit:arg => (⟨(advance ticket arch prior (x).1 (x).2).val,fit⟩:Fin v.resolver.nodes)
local notation:max "job₀" x:arg fit:arg j:arg argFit:arg =>
  v.resolver.index ((column₀ (x).1).cast shape.blocks.symm,slot₀ x fit,(⟨j,argFit⟩:Fin v.resolver.operands))
local notation "mouthRows₀" => v.headerMouthRows floor entry mat V homes groups bits_
local notation:max "seed₀" b:arg seat:arg h:arg g:arg => chipDonor v.bornBook.format (chip h g)
  (finProdFinEquiv ((b).cast mat.newBlocks.symm,seat))
local notation:max "donor₀" i:arg => W.graph.src ((r).pick (i,0))
local notation:max "seat₀" i:arg => outgoingSlot A (cap.order.trans Fin.valEmbedding) S cap.valid (r).pick (fun t:(r).pairs=>(r).picked (t,0)) i
local notation:max "bankBlock₀" b:arg => (b).cast (congrArg (2^·) depth.symm)
local notation:max "bankSeat₀" s:arg => (s).cast (mat.newCap.trans capacity).symm
local notation:max "bankHost₀" h:arg => ((h).castLE hostFit).cast homes.symm
local notation:max "bankGroup₀" g:arg => (finProdFinEquiv ((S.groupDigits age radix) g)).cast
  (groups.trans (congrArg₂ Nat.mul gs rad)).symm
local notation:max "attained₀" pair:arg => seed₀ (bankBlock₀ ((A).block (donor₀ pair))) (bankSeat₀ (seat₀ pair))
  (bankHost₀ (cap.vertex ((A).pos (donor₀ pair)).2)) (bankGroup₀ ((A).pos (donor₀ pair)).1)

include old_live old_empty in
/-- Only the original page-zero W input is needed. The actual chip supplies the newborn
slot in each of the three role pages, including a mouth selected from the sibling. -/
theorem registered_born_ports {wide:ℕ} (auth:stock) (stampFits:N₀<2^wide)
    (x:NodeOrder.All next) (j:ℕ) (pair:(r).pairs) (party:Fin 6)
    (fresh:roots ticket arch x=.inr (pair,party))
    (fit:(advance ticket arch prior x.1 x.2).val<v.resolver.nodes) (argFit:j<v.resolver.operands)
    (resident:∀l,Values.Prefix hostFit (from₀ j l) (V (v.headerMouthPage floor entry mat (arg₀ j argFit)) l))
    (want:Mouth) (hit:mouth (actual G p) T.z (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (prof pair)).val
      party j=some want) (demand:v.bornBook.demand=G.b) (grain:v.bornBook.grain=p) (scale:v.bornBook.scale=T.z)
    (first:(attained₀ pair).first=true)
    (supply:∀s,((attained₀ pair).supplyUnits s).val=((prof pair).val s).val+G.k) (f:Fin 3) :
    take ((v.resolver.index.symm (job₀ x fit j argFit)).2.1)
      (v.mouthHeaderValue floor entry mat shape mouthRows₀ chip homes groups (job₀ x fit j argFit) f
        (rh x.1) (rg x.1)) = RolePorts.value v.bornBook.bits (some want) f :=by
  let issued:=fun (b:Fin (2^v.reference.k)) (s:Fin v.bornBook.cap) (t:Fin 6) (h:Fin v.bornBook.hosts)
      (g:Fin v.bornBook.groups)=>RolePorts.value v.bornBook.bits
        (pointerAt v.bornBook.demand v.bornBook.grain v.bornBook.scale (seed₀ b s h g) t j) f
  let pulled:=Values.pulledBirth depth capacity gs rad field hostFit mat.newCap homes groups bits_ issued
  let born':=fun b s t h (g:Fin OG)=>pulled b s t h (finProdFinEquiv ((S.groupDigits age radix) g))
  have read:=Values.native_birth_read degree depth oldNodes capacity lo gs rad field hostFit
    mat.newCap homes groups bits_ (rows₀ j) (V (v.headerMouthPage floor entry mat (arg₀ j argFit)))
    resident issued v.resolver.nodes (slot₀ x fit) (part₀ x.1) (host₀ x.1) (group₀ x.1)
  have changed (l) : ((rows₀ j) l).withBirth pulled =
      rangeValues ticket arch tokens age radix priorCount (prior₀ j) born' l :=by
    unfold rangeValues Values.withBirth
    congr 1
    funext b s t h g
    change pulled b s t h g = pulled b s t h (finProdFinEquiv ((S.groupDigits age radix) ((S.groupDigits age radix).symm (finProdFinEquiv.symm g))))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have rowsChanged := funext changed
  have digitChanged := congrArg (fun (vs : Fin pitch₁ → Values deg k ports.nodes (A).cap OH (NG₁*2^k) ports.operandBits (Packed.bits pitch₁) mb) =>
    (take (slot₀ x fit) (DescentScalarBookReshape.book
      (fun l h g => (vs l).book v.resolver.nodes h g) (part₀ x.1) (host₀ x.1) (group₀ x.1))).val) rowsChanged
  have selected:=range_at_born_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty
    (prior₀ j) born' auth x.1 x.2 pair party fresh stampFits fit
  have units:∀s,((attained₀ pair).supplyUnits s).val=
      (profileDigits (actual G p).capacity
        (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (prof pair)).val s).val+(actual G p).supplyOffset:=by
    intro s
    simpa only [actual,profile_read] using supply s
  have live:pointerAt v.bornBook.demand v.bornBook.grain v.bornBook.scale (attained₀ pair) party j=some want:=by
    rw [demand,grain,scale]
    exact (pointer_first (actual G p) T.z _ j party (attained₀ pair) first units).trans hit
  let site := W.graph.src ((r).pick (pair,0))
  have printed : (born' ((A).block site) (seat₀ pair) party (cap.vertex ((A).pos site).2) ((A).pos site).1).val =
      (RolePorts.value v.bornBook.bits (some want) f).val := by
    change (RolePorts.value _ (pointerAt _ _ _ (attained₀ pair) party j) f).val=_
    rw [live]
  have physical := read.trans digitChanged
  have rasterEq := range_values_returned ticket arch tokens age radix priorCount (prior₀ j) born' v.resolver.nodes (part₀ x.1)
  have located := congrArg (fun cell => (take (slot₀ x fit) cell).val)
    (congrFun (congrFun rasterEq (host₀ x.1)) (group₀ x.1))
  have below := (physical.trans located).trans ((congrArg Fin.val selected).trans printed)
  apply Fin.ext
  exact (v.mouth_header_read floor entry mat shape V chip homes groups bits_ (column₀ x.1)
    (slot₀ x fit) ⟨j,argFit⟩ f (widen hostFit (outer₀ x.1)) ((group₀ x.1).cast gs.symm)).trans below

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
