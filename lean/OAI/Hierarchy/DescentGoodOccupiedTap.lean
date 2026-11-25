import OAI.Hierarchy.DescentGoodTapIssuedWord
import OAI.Hierarchy.DescentMountedStemWord

namespace OAI
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1700000
open private transportCircuit from OAI.Hierarchy.DescentInstalledNames
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (wide : max 1 (max B.reset.width (C*B.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "installed" => reentryWorldShape split_ B.reset B.terminals birth _ hp splitEq (resetMenu B) one wide
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite



open DescentResetFreshWires DescentResetLocalNodes DescentOrderedWords
local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation "middle_" x:arg => NodeOrder.followNames B.reblock pre_ x
local notation "where_" x:arg => resetOrigin B hp whole a x

open DescentLaneGates

open DescentPhysicalSplit DescentBundleHistory DescentResetPublicOperandBook DescentRotorOperandQueryROM.Shape
variable (side : Bool) (root : B.reset.placement.Good)
local notation "R_" => B.reset.placement
local notation "bits_" => B.reset.width
local notation "sizedHardware" => (splitEq ▸ B.reset.circuit :
  Hardware (K:=F) (C₀:=C) (u:=unit*p) R_ B.reset.graph B.reset.positive B.reset.pay)
local notation "itemEnum" => @Subtype.fintype _ (fun e => (R_).owner side ((R_).contact e) = Sum.inl root)
  (fun _ => Classical.propDecidable _) inferInstance
private abbrev usualTapEnum : Fintype (Cells B.reset.placement side root) := inferInstance

local instance (priority := high) occupiedTapCellEnum : Fintype (Cells B.reset.placement side root) := itemEnum
local notation "base" => (transportCircuit (b:=itemEnum) (G:=B.reset.graph) (hw:=B.reset.positive) (pay:=B.reset.pay) (sizedHardware side root))
local notation "layers_" => selectedRotorLayers R_ B.reset.graph B.reset.positive B.reset.pay sizedHardware side root
local notation "H₀" => Physical.host B.reset.graph.arcs d layers_ C bits_ (unit*p)
local notation "sizedChoice" => selected R_ B.reset.graph B.reset.positive B.reset.pay sizedHardware side (.inl root)
local notation "trueDevice" => DescentMixedRouter.device B.reset.graph B.reset.positive (unit*p)
  (R_).contact (R_).input (R_).site (R_).owner (R_).align (D:=d) sizedChoice
local notation "sizedSite" => DescentCommonPalette.rotorSiteEquiv B.reset.graph d layers_ C bits_ (unit*p)
local notation "installedSite" => DescentCommonPalette.rotorSiteEquiv B.reset.graph d
  (selectedRotorLayers R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit side root) C bits_ B.reset.unit
local notation "src_" => (fun e : Cells R_ side root=>(DescentChosenRouter.head R_ side root) (DescentRouterSlots.root (R_).contact
  (R_).input (R_).site (R_).owner side (.inl root) (R_).align e))
local notation "dst_" => (fun e : Cells R_ side root=>(DescentChosenRouter.tail R_ side root) (DescentRouterSlots.link (R_).contact (R_).owner side (.inl root) e))
local notation "key_" => (Function.Embedding.subtype (fun e=>(R_).owner side ((R_).contact e)=.inl root)).trans birth
local notation "addr_" => DescentRotor.Ordered.orderedAddress key_ src_ dst_ B.reset.positive
local notation "legBits_" => @DescentResetGates.legBits (Cells R_ side root) F itemEnum _ d (unit*p) B.reset.n h bits_ C B.reset.graph B.reset.positive B.reset.pay _ _ base
variable (vertex : Fin (2^B.reset.n))
variable (i₀ : Fin (DescentPhysicalSplit.count (Physical.host B.reset.graph.arcs d
  (selectedRotorLayers B.reset.placement B.reset.graph B.reset.positive B.reset.pay
    (((Nat.div_mul_cancel whole).symm : B.reset.unit = (B.reset.unit / p) * p) ▸ B.reset.circuit :
      Hardware (K:=F) (C₀:=C) (u:=(B.reset.unit/p)*p) B.reset.placement B.reset.graph B.reset.positive B.reset.pay) side root)
    C B.reset.width ((B.reset.unit/p)*p)) vertex))
local notation "rawTap" => (⟨vertex,.inr i₀⟩ : (trueDevice).Site)
local notation "site_" => ((sizedSite).symm rawTap)
local notation "venue_" => (⟨(side,.inl root),installedSite site_⟩ : B.reset.bank.Site)
local notation "tapWidth" => boundaryWidth trueDevice rawTap
local notation "tapUnits" => (fun k=>tapWidth k/p)
local notation "gate_" t:arg => (mountedGoodNode R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit birth
  d unit p hp splitEq side root site_).symm (.inr t)
local notation "back_" t:arg => DescentBatchedRotor.tapLane d unit p hp (R_).contact (R_).input (R_).site (R_).owner (R_).align
  side (.inl root) B.reset.graph (DescentChosenRouter.head R_ side root) (DescentChosenRouter.tail R_ side root) base vertex i₀ true ⟨i₀,t⟩
local notation:max "ix_" t:arg slot:arg => (t).2.2.cast (congrArg legBits_ slot)
local notation:max "req_" pin:arg q:arg t:arg slot:arg digit:arg => (⟨pin,q,(t).1.val,(t).2.1.val,(ix_ t slot).val,digit⟩ : Mouth B.reset.n)
local notation:max "prior_" pin:arg q:arg t:arg slot:arg digit:arg e:arg => Config.earlierCount src_ dst_ key_ (req_ pin q t slot digit) e
local notation:max "rows_" pin:arg q:arg => DescentRotorOperandRanks.At src_ dst_ (fun z=>(if pin then z.2 else z.1)=q)
local notation:max "cfg" field:arg query:arg lanes:arg nodes:arg args:arg grain:arg => publicOperandConfig B field query lanes unit unit nodes args grain
local notation "active_" config:arg x:arg => ((config).oldConfig.header ((config).basic x) 0).val≠0
local notation "control_" config:arg x:arg node:arg arg:arg mouth:arg => (config).rotor.public_selector B.reset.graph (config).multiplicity
  (config).grain node arg ((config).reg x)=some (side,B.reset.goodLabel B.terminals root,mouth)
open DescentOrderedWords DescentOrderedReset

open private inputLayer from OAI.Hierarchy.DescentMountedStemWord

include hp pos whole in
/-- Either enumeration gives the same digit and chronological rank on each occupied cell. -/
private theorem issued_with_enum {field query lanes nodes args grain : ℕ}
    (x : (cfg field query lanes nodes args grain).Data B.reset.n) (req : Mouth B.reset.n)
    (rows : GoodTapRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes)
      (args:=args) (grain:=grain) B side root x)
    (node arg : ℕ) (active : active_ (cfg field query lanes nodes args grain) x)
    (control : control_ (cfg field query lanes nodes args grain) x node arg req)
    (enum : Fintype (Cells R_ side root)) :
    letI := enum
    ∀ firstItem : Cells R_ side root,
      ((if req.pin then dst_ firstItem else src_ firstItem)=req.vertex ∧
        inputLayer (B.reset.circuit side root) key_ firstItem=req.layer ∧
        (addr_ firstItem).2.val=req.digit) →
      req.within < min 2 (Fintype.card (rows_ req.pin req.vertex)*unit -
        (Config.earlierCount src_ dst_ key_ req firstItem*unit + req.batch)) →
      let start := Config.earlierCount src_ dst_ key_ req firstItem*unit + req.batch
      let word := start+req.within
      let count := min 2 (Fintype.card (rows_ req.pin req.vertex)*unit - start)
      ∃ donor : rows_ req.pin req.vertex, Config.earlierCount src_ dst_ key_ req donor.val=word/unit ∧
        (cfg field query lanes nodes args grain).mixed B.reset.graph node arg x=some
          (if req.pin then (cfg field query lanes nodes args grain).rotorContactAt side cap.placement.cap
              (B.reset.goodLabel B.terminals root) req.vertex
           else (cfg field query lanes nodes args grain).oldConfig.stemAt side cap.placement.cap
             ((cfg field query lanes nodes args grain).oldItem x side (publicRotorSlots B side root donor.val)),
           if req.pin then word else word%unit,count,req.pin) := by
  cases Subsingleton.elim (usualTapEnum B side root) enum
  intro e chosen inRange
  exact good_tap_issued_word B hp pos whole side root x req rows node arg active control e chosen inRange

private theorem identify_block {A : Type} {p : ℕ} {width : A → ℕ} (ref : BlockRef p width)
    (port : A) (block : ℕ) (hport : ref.port=port) (hblock : ref.block=block) :
    ∃ fits : (block+1)*p ≤ width port, ref = ⟨port, block, fits⟩ := by
  cases ref
  cases hport
  cases hblock
  exact ⟨_, rfl⟩

/-- The native GOOD tap returns the computed reference, cover and residual
at the same signed face and same p-word of the original installed program. -/
theorem good_tap_stem_issued {field query lanes nodes args grain : ℕ}
    (q₀ : Fin (2^B.reset.n)) (slot : name H₀ vertex i₀=.inl (q₀,false))
    (t : DescentLaneGates.Block layers_ unit (@DescentResetGates.tapBits (Cells R_ side root) F itemEnum _ d (unit*p) B.reset.n h bits_ C B.reset.graph B.reset.positive B.reset.pay _ _ base vertex i₀))
    (y : NodeOrder.All next_) (origin : where_ y=.inr (.inr ⟨venue_,gate_ t⟩))
    (offset : ℕ) (firstItem : Cells R_ side root)
    (selected : src_ firstItem=q₀ ∧ (base).choose (addr_ firstItem).1=t.1 ∧ (addr_ firstItem).2=ix_ t slot)
    (covered : offset< min 2 (Fintype.card (rows_ false q₀)*unit-(prior_ false q₀ t slot offset firstItem*unit+t.2.1.val)))
    (x : (cfg field query lanes nodes args grain).Data B.reset.n)
    (rows : GoodTapRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args) (grain:=grain)
      B side root x)
    (node : ℕ) (active : active_ (cfg field query lanes nodes args grain) x)
    (control : control_ (cfg field query lanes nodes args grain) x node ((back_ t).count tapUnits+offset) (req_ false q₀ t slot offset)) :
    let absolute:=prior_ false q₀ t slot offset firstItem*unit+t.2.1.val+offset
    let count:=min 2 (Fintype.card (rows_ false q₀)*unit-(prior_ false q₀ t slot offset firstItem*unit+t.2.1.val))
    ∃host number,∃out : PublicSocket B host unit (absolute%unit) false number,
      (cfg field query lanes nodes args grain).mixed B.reset.graph node ((back_ t).count tapUnits+offset) x=
        some (number,absolute%unit,count,false) ∧
      keyCable installed (middle_ y) ((back_ t).count tapUnits+offset)=some (out.face.val.1,absolute%unit) ∧
      (if out.face.val.2 then (coarse).graph.dst out.face.val.1 else (coarse).graph.src out.face.val.1)=(hop).symm y.1 :=by
  intro absolute count
  let ports:=mountedGoodPorts R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit d unit p splitEq side root site_
  have target:=B.reset.laneWidth_eq unit p splitEq venue_
  have source (w) : tapWidth w=tapUnits w*p:=by
    have same := ports.sameWidth w
    exact same.trans ((target (ports.slot w)).trans (congrArg (fun n=>n/p*p) same.symm))
  obtain ⟨ref,port,refAt,rootAt,word,read⟩:=installed_stem_word R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit birth
    d unit p hp splitEq side root vertex i₀ q₀ slot t target source offset firstItem selected covered
  have choose:=sized_focus_layer R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit birth unit p splitEq side root firstItem
  have decode := issued_with_enum B hp pos whole side root x (req_ false q₀ t slot offset) rows node
    ((back_ t).count tapUnits+offset) active control (occupiedTapCellEnum B side root) firstItem
  have layer : inputLayer (B.reset.circuit side root) key_ firstItem = t.1.val :=
    choose.trans (congrArg Fin.val selected.2.1)
  have stripe : (addr_ firstItem).2.val = (ix_ t slot).val := congrArg Fin.val selected.2.2
  obtain ⟨donor,order,issued⟩ := decode ⟨selected.1,layer,stripe⟩ covered
  obtain ⟨previous,same,rank⟩:=good_tap_stem_rank B side root (req_ false q₀ t slot offset) rfl firstItem donor.val
    selected.1 donor.property port.val rootAt
  have enumRank : _ = prior_ false q₀ t slot offset donor.val :=
    congrArg (fun en : Fintype (Cells R_ side root) => @Config.earlierCount _ en _ _ src_ dst_ key_ (req_ false q₀ t slot offset) donor.val)
      (Subsingleton.elim (usualTapEnum B side root) (occupiedTapCellEnum B side root))
  obtain ⟨fits,identification⟩ := identify_block ref (.inr port) absolute refAt word
  rw [identification] at read
  obtain ⟨out,keys,ending⟩:=good_tap_stem_socket_key (field:=field) (query:=query) (lanes:=lanes) (batches:=unit)
    (nodes:=nodes) (args:=args) (grain:=grain) B hp one pos whole wide a sh y venue_ (gate_ t) origin
    ((back_ t).count tapUnits+offset) port absolute fits read previous (rank.trans (enumRank.trans order)) x
  have sameSide : port.val.1=side:=congrArg Prod.fst rootAt
  refine ⟨_,_,out,?_,keys,ending⟩
  let stemNumber (direction : Bool) (e : (W.granular B.count (z*G.b) B.fit).graph.Edge) :=
    (cfg field query lanes nodes args grain).oldConfig.stemAt direction cap.placement.cap
      ((cfg field query lanes nodes args grain).oldItem x direction (oldRotorCell B direction (beforeStem B e)))
  have numberEq := congrArg₂ stemNumber sameSide.symm same.symm
  exact issued.trans (congrArg (fun number : ℕ => some (number,absolute%unit,count,false)) numberEq)

theorem good_tap_contact_issued {field query lanes nodes args grain : ℕ}
    (q₀ : Fin (2^B.reset.n)) (slot : name H₀ vertex i₀=.inl (q₀,true))
    (t : DescentLaneGates.Block layers_ unit (@DescentResetGates.tapBits (Cells R_ side root) F itemEnum _ d (unit*p) B.reset.n h bits_ C B.reset.graph B.reset.positive B.reset.pay _ _ base vertex i₀))
    (y : NodeOrder.All next_) (origin : where_ y=.inr (.inr ⟨venue_,gate_ t⟩))
    (offset : ℕ) (firstItem : Cells R_ side root)
    (selected : dst_ firstItem=q₀ ∧ (base).choose (addr_ firstItem).1=t.1 ∧ (addr_ firstItem).2=ix_ t slot)
    (covered : offset< min 2 (Fintype.card (rows_ true q₀)*unit-(prior_ true q₀ t slot offset firstItem*unit+t.2.1.val)))
    (x : (cfg field query lanes nodes args grain).Data B.reset.n)
    (rows : GoodTapRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args) (grain:=grain)
      B side root x)
    (node : ℕ) (active : active_ (cfg field query lanes nodes args grain) x)
    (control : control_ (cfg field query lanes nodes args grain) x node ((back_ t).count tapUnits+offset) (req_ true q₀ t slot offset)) :
    let absolute:=prior_ true q₀ t slot offset firstItem*unit+t.2.1.val+offset
    let count:=min 2 (Fintype.card (rows_ true q₀)*unit-(prior_ true q₀ t slot offset firstItem*unit+t.2.1.val))
    ∃host number,∃out : PublicSocket B host unit absolute true number,
      (cfg field query lanes nodes args grain).mixed B.reset.graph node ((back_ t).count tapUnits+offset) x=
        some (number,absolute,count,true) ∧
      keyCable installed (middle_ y) ((back_ t).count tapUnits+offset)=some (out.face.val.1,absolute) ∧
      (if out.face.val.2 then (coarse).graph.dst out.face.val.1 else (coarse).graph.src out.face.val.1)=(hop).symm y.1 :=by
  intro absolute count
  have choose:=sized_focus_layer R_ B.reset.graph B.reset.positive B.reset.pay B.reset.circuit birth unit p splitEq side root firstItem
  have decode := issued_with_enum B hp pos whole side root x (req_ true q₀ t slot offset) rows node
    ((back_ t).count tapUnits+offset) active control (occupiedTapCellEnum B side root) firstItem
  have layer : inputLayer (B.reset.circuit side root) key_ firstItem = t.1.val :=
    choose.trans (congrArg Fin.val selected.2.1)
  have stripe : (addr_ firstItem).2.val = (ix_ t slot).val := congrArg Fin.val selected.2.2
  obtain ⟨donor,order,issued⟩ := decode ⟨selected.1,layer,stripe⟩ covered
  obtain ⟨out,keys,ending⟩:=good_occupied_contact_socket_key (field:=field) (query:=query) (lanes:=lanes)
    (batches:=unit) (nodes:=nodes) (args:=args) (grain:=grain) B hp one pos whole wide a sh
    side root vertex i₀ q₀ slot t y origin offset firstItem selected covered
  refine ⟨_,_,out,?_,keys,ending⟩
  have position : DescentChosenRouter.target R_ side root firstItem = q₀ := selected.1
  exact issued.trans (congrArg (fun number : ℕ => some (number,absolute,count,true))
    (congrArg ((cfg field query lanes nodes args grain).rotorContactAt side cap.placement.cap
      (B.reset.goodLabel B.terminals root)) position.symm))

/-- Both positive arms of an installed public rotor tap. -/
theorem good_tap_socket_key {field query lanes nodes args grain : ℕ}
    (pin : Bool) (q₀ : Fin (2^B.reset.n)) (slot : name H₀ vertex i₀=.inl (q₀,pin))
    (t : DescentLaneGates.Block layers_ unit (@DescentResetGates.tapBits (Cells R_ side root) F itemEnum _ d (unit*p) B.reset.n h bits_ C B.reset.graph B.reset.positive B.reset.pay _ _ base vertex i₀))
    (y : NodeOrder.All next_) (origin : where_ y=.inr (.inr ⟨venue_,gate_ t⟩))
    (offset : ℕ) (firstItem : Cells R_ side root)
    (selected : (if pin then dst_ firstItem else src_ firstItem)=q₀ ∧ (base).choose (addr_ firstItem).1=t.1 ∧ (addr_ firstItem).2=ix_ t slot)
    (covered : offset< min 2 (Fintype.card (rows_ pin q₀)*unit-(prior_ pin q₀ t slot offset firstItem*unit+t.2.1.val)))
    (x : (cfg field query lanes nodes args grain).Data B.reset.n)
    (rows : GoodTapRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args) (grain:=grain)
      B side root x)
    (node : ℕ) (active : active_ (cfg field query lanes nodes args grain) x)
    (control : control_ (cfg field query lanes nodes args grain) x node ((back_ t).count tapUnits+offset) (req_ pin q₀ t slot offset)) :
    let absolute:=prior_ pin q₀ t slot offset firstItem*unit+t.2.1.val+offset
    let count:=min 2 (Fintype.card (rows_ pin q₀)*unit-(prior_ pin q₀ t slot offset firstItem*unit+t.2.1.val))
    let word:=if pin then absolute else absolute%unit
    ∃host number,∃out : PublicSocket B host unit word pin number,
      (cfg field query lanes nodes args grain).mixed B.reset.graph node ((back_ t).count tapUnits+offset) x=
        some (number,word,count,pin) ∧
      keyCable installed (middle_ y) ((back_ t).count tapUnits+offset)=some (out.face.val.1,word) ∧
      (if out.face.val.2 then (coarse).graph.dst out.face.val.1 else (coarse).graph.src out.face.val.1)=(hop).symm y.1 :=by
  cases pin with
  | false =>
    exact good_tap_stem_issued B hp one pos whole wide a sh side root vertex i₀ q₀ slot t y origin
      offset firstItem selected covered x rows node active control
  | true =>
    exact good_tap_contact_issued B hp one pos whole wide a sh side root vertex i₀ q₀ slot t y origin
      offset firstItem selected covered x rows node active control

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
