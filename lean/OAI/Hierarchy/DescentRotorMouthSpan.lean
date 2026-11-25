import OAI.Hierarchy.DescentRotorApertureLane
import OAI.Hierarchy.DescentRotorPublicDigits
import OAI.Hierarchy.DescentRotorPhysicalRangePrefix

namespace OAI
/-! # Every scheduled rotor mouth has its physical range, including an unused packet digit -/
namespace Hierarchy.DescentResetPublicOperandBook.Config
open DescentSIMDLookup DescentRotor DescentRouterSlots DescentBatchedNodeOrder DescentResetGates
open DescentBundleHistory DescentLaneGates DescentRetainedRangeDigits DescentBaseProfile
open DescentRotorOperandQueryROM.Shape DescentPhysicalSplit DescentResetLaneIssue DescentFallbackItemSelect
open DescentBatchedRotor DescentOrderedReset DescentKernelHistory DescentResetLocalRoster
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 800000
private theorem fixed_slot {T : Type} {w : T → ℕ} {Y grain : ℕ}
    (q : T → ℕ) (mult : ∀ a, w a = q a * grain) (hp : 0 < grain)
    (program : DescentLaneGates.Program Y grain w) (gate : program.Node)
    (back : Lane grain w) (bit : Bool)
    (physical : program.op gate = DescentLaneGates.equalOp (.wire back) (.fixed bit))
    (slot : ℕ) (outside : back.count q ≤ slot) (f : Fin 3) :
    atSlot (ofProgram q mult hp program) gate slot f = 0 := by
  apply atSlot_padding
  have codes := (lane_codes q mult hp program gate).trans (congrArg (operandCodes q) physical)
  rw [codes]
  simpa [DescentLaneGates.equalOp, operandCodes, DescentLaneGates.expectOp, List.ofFn_succ,
    DescentTerminalSliceRuns.repeatFields, laneCode] using outside

variable {I C V W K : Type} [Fintype I] [Fintype C] [Fintype V] [Fintype W] [Field K]
    (D : ℕ) (contact : I→C) (input : Bool→I→V) (site : Bool→V→W) (owner : Bool→C→W)
    (align : ∀s i,site s (input s i)=owner s (contact i)) (side : Bool) (host : W)
    {n h N : ℕ} (board : NonlinearExpanders.Graph n h) (cfg : DescentResetPublicOperandBook.Config)
    {hw : 0<cfg.packetWidth} {pay : ℝ} (first : InputId site side host↪Fin (2^n))
    (last : LinkId owner side host↪Fin (2^n)) (key : I↪Fin N) (hp : 0<cfg.grain)
local notation "p" => cfg.grain
local notation "m" => cfg.batches
local notation "u" => m*p
local notation "E" => DescentRouterSlots.Item contact owner side host
local notation "src" => (fun i : DescentRouterSlots.Item contact owner side host => first (DescentRouterSlots.root contact input site owner side host align i))
local notation "dst" => (fun i : DescentRouterSlots.Item contact owner side host => last (DescentRouterSlots.link contact owner side host i))
local notation "chron" => ((Function.Embedding.subtype (fun i : I=>owner side (contact i)=host)).trans key)
variable (P : BaseCircuit K board cfg.multiplicity cfg.packetWidth (cfg.batches*cfg.grain) hw
  (fun e : DescentRouterSlots.Item contact owner side host => first (root contact input site owner side host align e))
  (fun e : DescentRouterSlots.Item contact owner side host => last (link contact owner side host e)) pay)
local notation "H" => Physical.host board.arcs D P.layers cfg.multiplicity cfg.packetWidth u
local notation "A" => DescentGoodRouter.device (K:=K) D u contact input site owner align side host board first last P
local notation "ord" => Ordered.orderedAddress chron src dst hw
variable (x : cfg.Data n) (rootCode : DescentResetLocalRoster.code cfg.residual)
    (slot : DescentRouterSlots.Item contact owner side host ↪Fin cfg.oldConfig.count)
    (present : ∀e,cfg.endpoints side rootCode x (slot e)=some (first (DescentRouterSlots.root contact input site owner side host align e), last (DescentRouterSlots.link contact owner side host e)))
    (missing : ∀j,(¬∃e,slot e=j)→cfg.endpoints side rootCode x j=none)
    (sorted : ∀a b : DescentRouterSlots.Item contact owner side host,before (cfg.oldItem x side) (slot a) (slot b) ↔ key a.val < key b.val)
    (traffic : cfg.traffic x side rootCode=matrixOfBundles
      (fun e : DescentRouterSlots.Item contact owner side host => first (DescentRouterSlots.root contact input site owner side host align e))
      (fun e : DescentRouterSlots.Item contact owner side host => last (DescentRouterSlots.link contact owner side host e)))
    (levels : DescentRecordedRotorLayers.layers n cfg.packetWidth cfg.gain ((cfg.reg x) 0).val=P.layers)
variable (dir : Bool) (v : Fin (2^n)) (r : Fin P.layers) (k : Fin cfg.batches) (j : Fin cfg.packetWidth) (within : ℕ)
local notation "req" => (⟨dir,v,r.val,k.val,j.val,within⟩:Mouth n)
local notation "actor" => DescentPhysicalSplit.tap H (.inl (v,dir))
local notation "width" => boundaryWidth A actor
local notation "units" => fun i=>width i/p
local notation "leg" => publicTapLane (K:=K) D (cfg.batches*cfg.grain) contact input site owner align side host board first last P key
  («m»:=cfg.batches) («p»:=cfg.grain) rfl hp dir v r k j
local notation "attached" e:arg => ((if dir then dst e else src e)=v ∧ P.choose (ord e).1=r ∧ (ord e).2=j)

include present missing sorted traffic levels in
omit [Fintype V] in
theorem public_focus_range (program : DescentLaneGates.Program (2^n) p width) (gate : program.Node)
    (back : Lane p width) (physical : program.op gate=DescentLaneGates.equalOp (.wire back) leg)
    (mult : ∀a,width a=units a*p) (positive : 0< m) (node : Fin cfg.nodes) (arg : Fin cfg.args)
    (offset : arg.val=back.count units+within) (active : (cfg.oldConfig.header (cfg.basic x) 0).val≠0)
    (selected : cfg.rotor.public_selector board cfg.multiplicity p node.val arg.val (cfg.reg x)=some (side,rootCode,req))
    (outBits : ℕ) (room : 2<2^outBits) (f : Fin 3) :
    (cfg.column board outBits (some (page f)) (finProdFinEquiv (arg,node)) x).val=
      atSlot (ofProgram units mult hp program) gate arg.val f:=by
  classical
  by_cases occupied : ∃e : E,attached e
  · obtain ⟨e,hit⟩:=occupied
    obtain ⟨l,read,beg,step,span⟩:=public_lane_at D m p hp contact input site owner align side host board first last P key
      dir v r k j within e hit
    rw [read] at physical
    exact cfg.public_span board P chron x side rootCode req slot present missing sorted traffic levels hp mult program gate
      back l physical e ⟨hit.1,congrArg Fin.val hit.2.1,congrArg Fin.val hit.2.2⟩ positive beg step span node arg f outBits room offset active selected
  · obtain ⟨bit,read⟩:=public_lane_vacant D m p hp contact input site owner align side host board first last P key
      dir v r k j occupied
    rw [read] at physical
    have noItem:=cfg.carrier_empty board P chron x side rootCode req slot present missing sorted traffic levels (by
      intro e atSocket
      exact occupied ⟨e,atSocket.1,Fin.ext atSocket.2.1,Fin.ext atSocket.2.2⟩)
    have noEntry : cfg.mixed board node.val arg.val x=none:=by
      rw [cfg.public_dispatch board node.val arg.val x side rootCode req active selected]
      simp [Config.tap,noItem]
    have beyond : back.count units≤arg.val:=by omega
    calc
      _ = 0 := by simp [column,noEntry]
      _ = _ := (fixed_slot units mult hp program gate back bit physical arg.val beyond f).symm

omit [Fintype V] in
theorem leg_at_socket (l socket : Leg (P:=Physical.Pin (2^n)) H) (loc : l=socket) (target : (A).Site) (hit : DescentPhysicalSplit.tap H l=target)
    (z : Fin (legBits D u board P l)) (layer : Fin P.layers) (batch : Fin m) :
    (hit ▸ (legLane D u contact input site owner align side host board first last P key («m»:=m) («p»:=p) rfl hp l layer batch z)
      : LaneSource p (boundaryWidth A target))=
      (((congrArg (DescentPhysicalSplit.tap H) loc).symm.trans hit) ▸
        (legLane D u contact input site owner align side host board first last P key («m»:=m) («p»:=p) rfl hp socket layer batch
          (z.cast (congrArg (legBits D u board P) loc)))):=by
  cases loc
  rfl

include present missing sorted traffic levels in
omit [Fintype V] in
private theorem range_at_site (target : (A).Site) (eqn : actor=target)
    (program : DescentLaneGates.Program (2^n) p (boundaryWidth A target)) (gate : program.Node)
    (back : Lane p (boundaryWidth A target)) (physical : program.op gate=DescentLaneGates.equalOp (.wire back) (eqn ▸ leg))
    (mult : ∀a,boundaryWidth A target a=boundaryWidth A target a/p*p) (positive : 0< m)
    (node : Fin cfg.nodes) (arg : Fin cfg.args) (offset : arg.val=back.count (fun a=>boundaryWidth A target a/p)+within)
    (active : (cfg.oldConfig.header (cfg.basic x) 0).val≠0)
    (selected : cfg.rotor.public_selector board cfg.multiplicity p node.val arg.val (cfg.reg x)=some (side,rootCode,req))
    (outBits : ℕ) (room : 2<2^outBits) (f : Fin 3) :
    (cfg.column board outBits (some (page f)) (finProdFinEquiv (arg,node)) x).val=
      atSlot (ofProgram (fun a=>boundaryWidth A target a/p) mult hp program) gate arg.val f:=by
  subst target
  exact public_focus_range D contact input site owner align side host board cfg first last key hp P x rootCode slot present missing sorted traffic
    levels dir v r k j within program gate back physical mult positive node arg offset active selected outBits room f

local notation "prg" => DescentBatchedRotor.program D m p hp contact input site owner align side host board first last P key
local notation "H₀" => Physical.host board.arcs 0 0 0 0 0
local notation "nums" => cfg.rotor.subrow board cfg.multiplicity
local notation "archSlot" => bareSlot board cfg.rotor D P.layers cfg.multiplicity u
local notation "archRow" => bareSpineRow board cfg.rotor D P
local notation "nativeBits" => tapBits D u board P
local notation "gateNo" v:arg i:arg t:arg => (tapOrder P.layers m (nums v) (archSlot v i) (.inr (archRow v ⟨i,t⟩).2)).val
local notation "shapeBook" => DescentDenseHostOrder.roster board cfg.residual cfg.maxDepth
local notation "atWire" whereAt:arg => fun a=>boundaryWidth A whereAt a/p
local notation "backAt" v:arg i:arg t:arg => DescentBatchedRotor.tapLane D m p hp contact input site owner align side host board first last P v i true ⟨i,t⟩

include present missing sorted traffic levels in
omit [Fintype V] in
/-- The test takes place on the chosen tap instruction itself. The local order
is the physical mixed-radix digit. The offset is the size of its actual left
spine operand and the public header carries exactly the remaining query. -/
theorem installed_public_range (v₀ : Fin (2^n)) (i : Fin (DescentPhysicalSplit.count (P:=Physical.Pin (2^n)) H v₀))
    (t : Block P.layers m (nativeBits v₀ i)) (vertex : Fin (2^n)) (pin : Bool)
    (socket : name H v₀ i=.inl (vertex,pin)) (digit : ℕ) (arg : Fin cfg.args)
    (position : arg.val=(backAt v₀ i t).count (atWire ⟨v₀,.inr i⟩)+digit)
    (node : Fin cfg.nodes) (localId : node.val=gateNo v₀ i t)
    (mult : ∀a,boundaryWidth A ⟨v₀,.inr i⟩ a=(atWire ⟨v₀,.inr i⟩) a*p)
    (shape : ↥shapeBook) (depth : ((cfg.reg x) 1).val=rootCode.val.1+1)
    (safe : ((cfg.reg x) 2).val%2=0)
    (ranked : ((cfg.reg x) 3).val=(DescentDenseHostOrder.localRank board cfg.residual cfg.maxDepth shape).val)
    (placed : shape.val=.good side ((),rootCode.val.2) ⟨v₀,.inr (archSlot v₀ i)⟩)
    (active : (cfg.oldConfig.header (cfg.basic x) 0).val≠0) (outBits : ℕ) (room : 2<2^outBits) (f : Fin 3) :
    (cfg.column board outBits (some (page f)) (finProdFinEquiv (arg,node)) x).val=
      atSlot (ofProgram (atWire ⟨v₀,.inr i⟩) mult hp (prg ⟨v₀,.inr i⟩)) (.inr t) arg.val f:=by
  let widthEq:=congrArg (legBits D u board P) socket
  let index : Fin cfg.packetWidth:=t.2.2.cast widthEq
  let mouth : Mouth n:=⟨pin,vertex,t.1.val,t.2.1.val,index.val,digit⟩
  let place:DescentPhysicalSplit.tap H (.inl (vertex,pin))=⟨v₀,.inr i⟩:=(congrArg (DescentPhysicalSplit.tap H) socket).symm.trans (tap_named H v₀ i)
  have loc:=leg_at_socket D contact input site owner align side host board cfg first last key hp P (name H v₀ i)
    (.inl (vertex,pin)) socket ⟨v₀,.inr i⟩ (tap_named H v₀ i) t.2.2 t.1 t.2.1
  have back:=(cfg.rotor).spine_lane_count board D p hp contact input site owner align side host first last P v₀ i ⟨i,t⟩
  have same : name H v₀ i = name H₀ v₀ (archSlot v₀ i) :=
    DescentCommonPalette.rotor_name_cast board D P.layers cfg.multiplicity cfg.packetWidth u v₀ (archSlot v₀ i)
  have bareSocket := same.symm.trans socket
  have observedLayers : DescentRecordedRotorLayers.layers n cfg.rotor.packet cfg.rotor.gain ((cfg.reg x) 0).val=P.layers := levels
  have dispatch:=cfg.rotor.public_selector_at board cfg.multiplicity p node.val arg.val (cfg.reg x) side rootCode
    ⟨v₀,.inr (archSlot v₀ i)⟩ shape mouth depth safe ranked placed (by
      rw [observedLayers,localId,position]
      erw [back]
      exact cfg.rotor.public_tap_at board cfg.multiplicity P.layers p v₀ (archSlot v₀ i) (archRow v₀ ⟨i,t⟩).2 vertex pin bareSocket digit)
  refine range_at_site D contact input site owner align side host board cfg first last key hp P x rootCode slot present missing sorted traffic
    levels pin vertex t.1 t.2.1 index digit ⟨v₀,.inr i⟩ place (prg ⟨v₀,.inr i⟩) (.inr t) (backAt v₀ i t) ?_ mult
    (Nat.zero_lt_of_lt t.2.1.isLt) node arg position active dispatch outBits room f
  exact congrArg (equalOp (Y:=2^n) (.wire (backAt v₀ i t))) loc

end
end Hierarchy.DescentResetPublicOperandBook.Config

end OAI
