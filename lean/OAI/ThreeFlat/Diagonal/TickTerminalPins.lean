import OAI.ThreeFlat.Diagonal.PhysicalTerminalSource
import OAI.ThreeFlat.Diagonal.TickPackedEndpoint
import OAI.ThreeFlat.Diagonal.PhysicalProgramAssembly
import OAI.ThreeFlat.RAM.HistoryTerminalWire

namespace OAI
/-! # Installed pin addresses of every actual terminal word forest -/

set_option quotPrecheck false

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor TraceSuffix HistoryContraction RAM TickPhaseModel TickChronology TickAuxiliary
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] [Fintype F] {w p r n S base f q low : ℕ}
  (M : Machine w p r n) (t : NativeTrace.Fits M S base ((q+1)+low) f) (hF : Fintype.card F≤2^w)
  (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF t.width t.labels base f st r n d
local notation "A" => B.cursorState hk low (1+(d+d)) (G).cells
variable {period width a : ℕ} (c : Clock) (hc : c.chunks=2*(period*width))
local notation "L" => period*width*a+period*width*a
variable (extent : 2*(period*width*a+period*width*a)≤S)
local notation "U" => seedWordLayout M t hF st B hk extent
variable (R : PhysicalStage.Run F (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells))
  (J : R.Assembler (Fin (2*(period*width*a+period*width*a))→Bool))
  (N : Forest F (seedWordLayout M t hF st B hk extent).ports.form)
local notation "bits" => fun h=>(R.terminalLayer h).state.widthSum
variable (E : R.plan.Codes) (T : Buckets R.plan (fun h => (R.terminalLayer h).state.widthSum) c a (2^(q+1)) (2^low))
    (v : Plan.Terminal R.plan (fun h => (R.terminalLayer h).state.widthSum))
    (g : Fin c.groups) {cap : ℕ} (room : 1+cap+2*T.length v g.val≤a)
    (wireRoom : 1+(R.plan.write E v.1).length+(R.terminalLayer v.1).state.widthSum≤a)
    (advice nt ns np : ℕ)
local notation "PINS" => ApproximateImage.pinCount advice nt ns np a
local notation "X" => (R.terminalLayer v.1).state
local notation "K" => R.endWords v.1 J.steps U
local notation "result" => R.plan.assemble v.1 (J U) N

theorem seedWordLayout_halves : (A).OrderedHalves U := by
  refine ⟨fun _=>rfl,?_⟩
  intro z j
  exact congrArg Prod.fst (CompressorPacking.Native.ShrinkStage.Halves.portOrder_value (A).graph (A).chart z j)

theorem terminalHalves : (X).OrderedHalves K :=
  R.endWords_halves v.1 J.steps U (seedWordLayout_halves M t hF st B hk extent)

/-- External pointers use the actual ordered inherited child bits. Two
incident copies of a terminal wire use the same decoded word-bit address. -/
def terminalLocalWire (z : (X).Site) : Fin ((K).ports.form.width z)→Fin PINS :=
  (K).ports.physicalSource (fun y j=>
    let origin:=R.extAncestor v.1 J.steps U y j
    Buckets.packEndpoint c hc T v g room advice nt ns np (seedEndpoint L low origin.1 origin.2))
    (fun e j=>TickSelectedPins.wire advice nt ns np wireRoom ((X).edgeBit e j)) z

local notation "src" => terminalLocalWire M t hF st B hk c hc extent R J E T v g room wireRoom advice nt ns np

def terminalWire : ∀ root : (R.plan.finish v.1).Site,Fin ((result).1.width root)→Fin PINS :=
  PhysicalStage.transferWire (R.terminalLayer_shape v.1) (R.endWords_form v.1 J.steps U N).symm src

/-- The evaluation tick reads the proposed pairs and parsed wire suffix
straight from the incoming AUX block at the selected root's true addresses. -/
theorem terminalWire_read (leaves : ∀ lane : Lane (q+1),T.site (finFunctionFinEquiv lane)=(0,lane))
    (layout : Layout a) (histFit : (R.plan.write E v.1).length+bits v.1 ≤layout.wiresEnd-1)
    (root : (R.plan.finish v.1).Site) (own : T.group v.1 root=g)
    (D : Fin advice→Bool) (team : Fin nt→Bool) (step : Fin ns→Bool) (params : Fin np→Bool)
    (oa na oc nc : Fin a→Bool) (decoded : decode R.plan E bits layout oa=some v) :
    let reg:=TickAuxiliary.project (TickPairHeader.layout cap (T.length v g.val) room) oa
    let get:=fun pars=>PhysicalPinsInput.externalBits (TickPhysicalOrder.unpack (AlignedChunks.order c hc) (T.extend v g pars))
    let raw:=endpointPin (get (TickAuxiliary.oldPair room reg.pairs)) (get (TickAuxiliary.newPair room reg.pairs))
    ∀ j, ApproximateImage.fields D team step params oa na oc nc
      (terminalWire M t hF st B hk c hc extent R J N E T v g room wireRoom advice nt ns np root j)=
      (result).1.read root raw ((R.plan.finish v.1).graph.atVertex (R.terminalLabels v.1 v.2) root) j := by
  intro reg get raw
  apply PhysicalStage.transferWire_reads (R.terminalLayer_shape v.1) (K).ports.form (result).1
    (R.endWords_form v.1 J.steps U N).symm src _ raw ((X).boundaryBits.symm v.2) root
  intro z hz
  apply (K).ports.physicalSource_read
  · intro j
    let orig:=R.extAncestor v.1 J.steps U z j
    have dest : R.plan.destination v.1 orig.1=root := eq_of_heq
      ((R.extAncestor_destination v.1 J.steps U z j).trans hz)
    exact (seedPacked_read M t hF st B hk c hc extent R.plan T leaves v g orig.1 orig.2
      (dest.symm ▸ own) room D team step params oa na oc nc).trans (R.extAncestor_read v.1 J.steps U z j raw).symm
  · intro port j
    exact (TickSelectedPins.decoded_wire R.plan E bits layout v histFit D team step params oa na oc nc decoded
      ((X).edgeBit port.1.1 j)).trans ((X).edgeBit_read v.2 port.1.1 j)

end
end ThreeFlat.Diagonal.TraceBitHeader

namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM HistoryContraction RAM RAM.HistoryTerminalTape RAM.TickTerminalRoot
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {d l p w : ℕ} {Pins : Type} (A : State d l) (K : A.Words Pins) (z : A.Site)

theorem orderedIncidences {u a teams cap hist q nt ns np : ℕ}
    (room : 1+hist+A.widthSum≤a) (T : Root) (raw : ℕ→ℕ) (m : Memory w)
    (extPin : ∀ y,Fin (K.ext y)→Fin (ApproximateImage.pinCount q nt ns np a))
    (external : T.ext=K.ext z) (count : T.halves=K.count z)
    (endpoint : ∀ i : Fin (K.ext z),m (T.endpoints+i.val)=((2+(extPin z i).val:ℕ):Word w))
    (origin : T.wireStart=(TickPhysicalABI.mounted u a teams cap q nt ns np).oldAux+1+hist)
    (number : ∀ b : Fin (K.count z),(half T raw b.val).edge=(A.wireOrder (K.order z b).val.1).val)
    (width : ∀ b : Fin (K.count z),(half T raw b.val).width=K.ports.lengths z b)
    (start : ∀ b : Fin (K.count z),(half T raw b.val).start=
      ∑ k : Fin b.val,K.ports.lengths z (Fin.castLE b.isLt.le k))
    (pre : ∀ (i : Fin A.edgeCount) (j : Fin (A.wireWidth i)),raw (T.wirePrefix+i.val)+j.val=(A.bitAddress i j).val) :
    Incidences T raw m (K.ports.physicalSource extPin (fun e j=>TickSelectedPins.wire q nt ns np room (A.edgeBit e j)) z) := by
  let wirePin (s : Fin (K.ports.halfBits z)) :=
    let t := (finSigmaFinEquiv (n:=K.ports.lengths z)).symm s
    TickSelectedPins.wire q nt ns np room (A.edgeBit (K.order z t.1).val.1 t.2)
  constructor
  · refine Fin.addCases (fun j _=>?_) (fun j hj=>?_)
    · change m (T.endpoints+j.val) =
        ((2+(Fin.append (extPin z) wirePin (Fin.castAdd (K.ports.halfBits z) j)).val : ℕ) : Word w)
      rw [Fin.append_left (extPin z) wirePin j]
      exact endpoint j
    · rw [external] at hj
      have hi:=j.isLt
      change K.ext z+j.val<K.ext z at hj
      omega
  · refine Fin.addCases (fun j hj=>?_) (fun j _=>?_)
    · change T.ext≤j.val at hj
      rw [external] at hj
      exact (Nat.not_lt_of_ge hj (show j.val < K.ext z from j.isLt)).elim
    · obtain ⟨⟨b,idx⟩,rfl⟩:=finSigmaFinEquiv.surjective j
      have hb : b.val < K.count z := b.isLt
      refine ⟨b.val,hb.trans_eq count.symm,idx.val,idx.isLt.trans_eq (width b).symm,?_⟩
      change K.ext z+(finSigmaFinEquiv (n:=K.ports.lengths z) ⟨b,idx⟩).val =
        T.ext+(half T raw b.val).start+idx.val
      rw [external,start b,Nat.add_assoc]
      exact congrArg (K.ext z + ·) (finSigmaFinEquiv_apply ⟨b,idx⟩)
  · intro bn hb j hj k e
    let b : Fin (K.count z):=⟨bn,hb.trans_eq count⟩
    let idx : Fin (K.ports.lengths z b):=⟨j,hj.trans_eq (width b)⟩
    let i:=A.wireOrder (K.order z b).val.1
    let bit : Fin (A.wireWidth i) :=
      Fin.cast (congrArg A.width (A.wireOrder.symm_apply_apply (K.order z b).val.1).symm) idx
    have point : k=Fin.natAdd (K.ext z) (finSigmaFinEquiv (n:=K.ports.lengths z) ⟨b,idx⟩) := Fin.ext (by
      rw [e,external,start b]
      simp only [Fin.val_natAdd,finSigmaFinEquiv_apply,idx,Nat.add_assoc])
    let ordinal := finSigmaFinEquiv (n:=K.ports.lengths z) ⟨b,idx⟩
    rw [point]
    change HistoryTerminalTape.source T raw bn+j =
      2+(Fin.append (extPin z) wirePin (Fin.natAdd (K.ext z) ordinal)).val
    let portPin (t : (h : Fin (K.count z)) × Fin (K.ports.lengths z h)) :=
      TickSelectedPins.wire q nt ns np room (A.edgeBit (K.order z t.1).val.1 t.2)
    have atPort : wirePin ordinal = portPin ⟨b,idx⟩ :=
      congrArg portPin ((finSigmaFinEquiv (n:=K.ports.lengths z)).symm_apply_apply ⟨b,idx⟩)
    rw [Fin.append_right (extPin z) wirePin ordinal,atPort]
    have pos:=pre i bit
    rw [A.bitAddress_val] at pos
    exact HistoryTerminalTape.ordered_address A (u:=u) (teams:=teams) (hidden:=0) q nt ns np cap room T raw bn i bit origin (number b)
      (Nat.add_right_cancel pos)

theorem transferWire_incidences {X Y : Shape} (e : X=Y) (U : Form X Pins) (V : Form Y Pins) (form : HEq U V)
    (src : ∀u,Fin (U.width u)→Fin p) (root : Y.Site) (T : Root) (raw : ℕ→ℕ) (m : Memory w)
    (shown : ∀ z : X.Site,HEq z root→Incidences T raw m (src z)) :
    Incidences T raw m (transferWire e form src root) := by
  subst Y
  have eqv:=eq_of_heq form
  subst V
  exact shown root HEq.rfl

end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor TraceSuffix HistoryContraction RAM TickPhaseModel TickChronology TickAuxiliary
open RAM.HistoryTerminalTape RAM.TickTerminalRoot
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] [Fintype F] {w p r n S base f q low : ℕ}
  (M : Machine w p r n) (t : NativeTrace.Fits M S base ((q+1)+low) f) (hF : Fintype.card F≤2^w)
  (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF t.width t.labels base f st r n d
local notation "A" => B.cursorState hk low (1+(d+d)) (G).cells
variable {period width a : ℕ} (c : Clock) (hc : c.chunks=2*(period*width))
local notation "L" => period*width*a+period*width*a
variable (extent : 2*(period*width*a+period*width*a)≤S)
local notation "U" => seedWordLayout M t hF st B hk extent
variable (R : PhysicalStage.Run F (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells))
  (J : R.Assembler (Fin (2*(period*width*a+period*width*a))→Bool))
  (N : Forest F (seedWordLayout M t hF st B hk extent).ports.form)
local notation "bits" => fun h=>(R.terminalLayer h).state.widthSum
variable (E : R.plan.Codes) (T : Buckets R.plan (fun h => (R.terminalLayer h).state.widthSum) c a (2^(q+1)) (2^low))
    (v : Plan.Terminal R.plan (fun h => (R.terminalLayer h).state.widthSum))
    (g : Fin c.groups) {cap : ℕ} (room : 1+cap+2*T.length v g.val≤a)
    (wireRoom : 1+(R.plan.write E v.1).length+(R.terminalLayer v.1).state.widthSum≤a)
    (advice nt ns np : ℕ)
local notation "PINS" => ApproximateImage.pinCount advice nt ns np a
local notation "X" => (R.terminalLayer v.1).state
local notation "K" => R.endWords v.1 J.steps U
local notation "result" => R.plan.assemble v.1 (J U) N

local notation "P" => R.plan
local notation "orig" => fun z j=>R.extAncestor v.1 J.steps U z j

open scoped Fin.CommRing in
/-- The native translated terminal records are exactly the static pin map.
The endpoint words here contain the proposal bank address and zero-based
S5 ordinal, and the half words contain edge numbers, widths and prefixes. -/
theorem terminalWire_incidences {age teams memoryW : ℕ}
    (leaves : ∀ lane : Lane (q+1),T.site (finFunctionFinEquiv lane)=(0,lane))
    (root : ((P).finish v.1).Site) (z : (X).Site) (sameRoot : HEq z root) (own : T.group v.1 root=g)
    (tape : Root) (raw : ℕ→ℕ) (m : Memory memoryW)
    (external : tape.ext=(K).ext z) (count : tape.halves=(K).count z)
    (endpoints : ∀ j : Fin ((K).ext z),
      let e:=seedEndpoint L low (orig z j).1 (orig z j).2
      let pt:=Buckets.endpointPoint c hc (Buckets.pairIndex e)
      m (tape.endpoints+j.val)=(((TickPhysicalABI.mounted age a teams cap advice nt ns np).oldAux+1+cap+
        (if Buckets.pairSide e then T.length v g.val else 0)+(T.code v g.val pt.1 pt.2-1):ℕ):Word memoryW))
    (wireStart : tape.wireStart=(TickPhysicalABI.mounted age a teams cap advice nt ns np).oldAux+1+((P).write E v.1).length)
    (number : ∀ b : Fin ((K).count z),(half tape raw b.val).edge=((X).wireOrder ((K).order z b).val.1).val)
    (widths : ∀ b : Fin ((K).count z),(half tape raw b.val).width=(K).ports.lengths z b)
    (starts : ∀ b : Fin ((K).count z),(half tape raw b.val).start=∑ k : Fin b.val,(K).ports.lengths z (Fin.castLE b.isLt.le k))
    (pre : ∀ i : Fin (X).edgeCount,raw (tape.wirePrefix+i.val)=∑ k : Fin i.val,(X).wireWidth (Fin.castLE i.isLt.le k)) :
    Incidences tape raw m (terminalWire M t hF st B hk c hc extent R J N E T v g room wireRoom advice nt ns np root) := by
  refine PhysicalStage.transferWire_incidences (R.terminalLayer_shape v.1) (K).ports.form (result).1
    (R.endWords_form v.1 J.steps U N).symm
    (terminalLocalWire M t hF st B hk c hc extent R J E T v g room wireRoom advice nt ns np)
    root tape raw m ?_
  intro z' matchRoot
  have same : z'=z := eq_of_heq (matchRoot.trans sameRoot.symm)
  subst z'
  refine PhysicalStage.orderedIncidences (u := age) (teams := teams) (cap := cap)
    (q := advice) (nt := nt) (ns := ns) (np := np) X K z wireRoom tape raw m
    (fun y j => Buckets.packEndpoint c hc T v g room advice nt ns np
      (seedEndpoint L low (orig y j).1 (orig y j).2)) external count ?_ wireStart number widths starts
    (fun i j=>by rw [pre,(X).bitAddress_val])
  intro j
  let old:=orig z j
  let e:=seedEndpoint L low old.1 old.2
  have dest : (P).destination v.1 old.1=root:=eq_of_heq ((R.extAncestor_destination v.1 J.steps U z j).trans sameRoot)
  have group : T.group v.1 ((P).destination v.1 old.1)=g:=dest.symm ▸ own
  have home:=seedEndpoint_owner M t hF st B hk c hc extent P T leaves v g old.1 old.2 group
  have offset:=Buckets.packEndpoint_address (age:=age) (teams:=teams) (hidden:=0) c hc T v g room advice nt ns np e home
  exact (endpoints j).trans (congrArg (fun n : ℕ=>(n:Word memoryW)) offset.symm)

end
end ThreeFlat.Diagonal.TraceBitHeader

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor TraceSuffix HistoryContraction RAM TickPhaseModel TickChronology TickAuxiliary
open NavigationPass NavigationPass.RootArchive PhysicalStage
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] [Fintype F] {w p r n S base f q low : ℕ}
  (M : Machine w p r n) (t : NativeTrace.Fits M S base ((q+1)+low) f) (hF : Fintype.card F≤2^w)
  (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF t.width t.labels base f st r n d
local notation "A" => B.cursorState hk low (1+(d+d)) (G).cells
variable {period width a : ℕ} (c : Clock) (hc : c.chunks=2*(period*width))
local notation "L" => period*width*a+period*width*a
variable (extent : 2*(period*width*a+period*width*a)≤S)
local notation "U" => seedWordLayout M t hF st B hk extent
variable (R : PhysicalStage.Run F (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells))
  (J : R.Assembler (Fin (2*(period*width*a+period*width*a))→Bool))
  (N : Forest F (seedWordLayout M t hF st B hk extent).ports.form)
local notation "bits" => fun h=>(R.terminalLayer h).state.widthSum
variable (E : R.plan.Codes) (T : Buckets R.plan (fun h => (R.terminalLayer h).state.widthSum) c a (2^(q+1)) (2^low))
    (v : Plan.Terminal R.plan (fun h => (R.terminalLayer h).state.widthSum))
    (g : Fin c.groups) {cap : ℕ} (room : 1+cap+2*T.length v g.val≤a)
    (wireRoom : 1+(R.plan.write E v.1).length+(R.terminalLayer v.1).state.widthSum≤a)
    (advice nt ns np : ℕ)
local notation "PINS" => ApproximateImage.pinCount advice nt ns np a
local notation "X" => (R.terminalLayer v.1).state
local notation "K" => R.endWords v.1 J.steps U
local notation "result" => R.plan.assemble v.1 (J U) N

variable (arch : RootArchive) (C : R.Charges) (start pairs : (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells).Site → ℕ) (teams : ℕ)

/-- Values at a full pair of catalyst endpoints use the actual assembled
terminal trees and the chronological run's decoded shared boundary. -/
def terminalFactors (v : Plan.Terminal R.plan bits) (x y : Ext c a) (z : (R.plan.finish v.1).Site) : F :=
  let D:=R.plan.assemble v.1 (J U) N
  let get:=fun p=>PhysicalPinsInput.externalBits (TickPhysicalOrder.unpack (AlignedChunks.order c hc) p)
  D.1.values D.2 (endpointPin (get x) (get y)) z ((R.plan.finish v.1).graph.atVertex (R.terminalLabels v.1 v.2) z)

set_option Elab.async false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
include arch C start pairs in
theorem compiledTeam_eval (reg : GroupRegister R.plan E bits a)
    (leaves : ∀ lane : Lane (q+1),T.site (finFunctionFinEquiv lane)=(0,lane))
    (fullRoom : ∀ v g,1+reg.capacity+2*T.length v g≤a) (time : ℕ)
    (D : Fin advice→Bool) (team : Fin teams→Fin nt→Bool) (step : Fin ns→Bool) (params : Fin np→Bool)
    (oa na oc nc : Fin a→Bool) (decoded : decode R.plan E bits reg.base oa=some v) :
    let roots:=fun k : Fin teams=>arch.teamRoots R v.1 C start pairs c teams g.val (TickClockWords.values c 0 teams k.val time 3)
    let wFit : 1+(R.plan.write E v.1).length+bits v.1≤a := by
      exact (Nat.add_assoc 1 _ _).le.trans ((Nat.add_le_add_left (reg.room v.1) 1).trans reg.fits)
    let wire:=fun k (i : Fin (roots k).length)=>terminalWire M t hF st B hk c hc extent R J N E T v g
      (fullRoom v g.val) wFit advice nt ns np ((roots k).get i)
    let nets:=fun k (i : Fin (roots k).length)=>((result).2 ((roots k).get i)).compile
    let weightAt := arch.packedWeight R C start pairs c teams T
      (terminalFactors M t hF st B hk c hc extent R J N)
    (∀ k i,T.group v.1 ((roots k).get i)=g) →
    (∏ k, (TickSlotForest.network (HistoryTerminalJoin.projected (nets k) (wire k))).eval
      (ApproximateImage.fields D (team k) step params oa na oc nc)) =
      weightAt v g.val (before (T.data (R:=reg) fullRoom weightAt) v g.val oa) (after (T.data (R:=reg) fullRoom weightAt) v g.val oa) time := by
  intro roots wFit wire nets weightAt home
  let fit:=fullRoom v g.val
  let workspace:=project (TickPairHeader.layout reg.capacity (T.length v g.val) fit) oa
  let get:=fun p=>PhysicalPinsInput.externalBits (TickPhysicalOrder.unpack (AlignedChunks.order c hc) (T.extend v g p))
  let pin:=endpointPin (get (oldPair fit workspace.pairs)) (get (newPair fit workspace.pairs))
  have old : oldPair fit workspace.pairs=TickPhaseModel.before (T.data (R:=reg) fullRoom weightAt) v g.val oa := by
    funext i
    exact oldPair_pin fit oa i
  have fresh : newPair fit workspace.pairs=TickPhaseModel.after (T.data (R:=reg) fullRoom weightAt) v g.val oa := by
    funext i
    rw [newPair_pin]
    apply congrArg oa
    apply Fin.ext
    change (1+reg.capacity+T.length v g.val)+i.val=1+reg.capacity+(T.length v g.val+i.val)
    omega
  have evaluate:=arch.teamRoots_intrinsic_tick R v.1 C start pairs c teams (J U) N pin
    (R.terminalLabels v.1 v.2) g.val time (fun k=>ApproximateImage.fields D (team k) step params oa na oc nc)
    wire (fun k i=>terminalWire_read M t hF st B hk c hc extent R J N E T v g fit wFit advice nt ns np
      leaves reg.base (reg.room_layout (n:=0) (by simpa using reg.fits) v.1) ((roots k).get i) (home k i) D (team k) step params oa na oc nc decoded)
  have factors : terminalFactors M t hF st B hk c hc extent R J N v
      (T.extend v g (oldPair fit workspace.pairs)) (T.extend v g (newPair fit workspace.pairs)) =
      fun z => (result).1.values (result).2 pin z
        ((R.plan.finish v.1).graph.atVertex (R.terminalLabels v.1 v.2) z) := by
    funext z
    rfl
  rw [←old, ←fresh]
  dsimp only [weightAt]
  rw [NavigationPass.RootArchive.packedWeight, dite_eq_left g.isLt, factors]
  simpa only [nets, roots] using evaluate

end
end ThreeFlat.Diagonal.TraceBitHeader

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor TraceSuffix HistoryContraction RAM TickPhaseModel TickChronology TickAuxiliary
open RAM.HistoryTerminalTape RAM.TickTerminalRoot
open CompressorPacking.Native.ShrinkStage
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] [Fintype F] {w p r n S base f q low : ℕ}
  (M : Machine w p r n) (t : NativeTrace.Fits M S base ((q+1)+low) f) (hF : Fintype.card F≤2^w)
  (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF t.width t.labels base f st r n d
local notation "A" => B.cursorState hk low (1+(d+d)) (G).cells
variable {period width a : ℕ} (c : Clock) (hc : c.chunks=2*(period*width))
local notation "L" => period*width*a+period*width*a
variable (extent : 2*(period*width*a+period*width*a)≤S)
local notation "U" => seedWordLayout M t hF st B hk extent
variable (R : PhysicalStage.Run F (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells))
  (J : R.Assembler (Fin (2*(period*width*a+period*width*a))→Bool))
  (N : Forest F (seedWordLayout M t hF st B hk extent).ports.form)
local notation "bits" => fun h=>(R.terminalLayer h).state.widthSum
variable (E : R.plan.Codes) (T : Buckets R.plan (fun h => (R.terminalLayer h).state.widthSum) c a (2^(q+1)) (2^low))
    (v : Plan.Terminal R.plan (fun h => (R.terminalLayer h).state.widthSum))
    (g : Fin c.groups) {cap : ℕ} (room : 1+cap+2*T.length v g.val≤a)
    (wireRoom : 1+(R.plan.write E v.1).length+(R.terminalLayer v.1).state.widthSum≤a)
    (advice nt ns np : ℕ)
local notation "PINS" => ApproximateImage.pinCount advice nt ns np a
local notation "X" => (R.terminalLayer v.1).state
local notation "K" => R.endWords v.1 J.steps U
local notation "result" => R.plan.assemble v.1 (J U) N

local notation "P" => R.plan
local notation "orig" => fun z j=>R.extAncestor v.1 J.steps U z j

open scoped Fin.CommRing in
/-- Physical publication form of the incidence proof. Endpoint rows use
the actual two-plus S12 codes, S44 uses its canonical outgoing slot array,
and only the prefix addresses of occupied final wire bits are read. -/
theorem terminalWire_published {age teams W : ℕ}
    (root : ((P).finish v.1).Site) (z : (X).Site) (sameRoot : HEq z root)
    (tape : Root) (raw : ℕ→ℕ) (m : Memory W)
    (external : tape.ext=(K).ext z) (count : tape.halves=2*(R.terminalLayer v.1).degree)
    (endpoints : ∀ j : Fin ((K).ext z), let p:=orig z j
      m (tape.endpoints+j.val)=((2+(Buckets.packEndpoint c hc T v g room advice nt ns np
        (seedEndpoint L low p.1 p.2)).val:ℕ):Word W))
    (origin : tape.wireStart=(TickPhysicalABI.mounted age a teams cap advice nt ns np).oldAux+1+((P).write E v.1).length)
    (halfRows : ∀ b : Fin (2*(R.terminalLayer v.1).degree),
      let ed:=Halves.sourceHalf (X).graph ((X).chart.symm z) b
      ((half tape raw b.val).edge=Halves.edgeNumber (X).order ed ∧
        (half tape raw b.val).width=(X).width ed ∧
        (half tape raw b.val).start=Halves.prefixValue (X).graph (X).width ((X).chart.symm z) b))
    (prefixes : ∀ (i : Fin (X).edgeCount) (j : Fin ((X).wireWidth i)),raw (tape.wirePrefix+i.val)+j.val=((X).bitAddress i j).val) :
    Incidences tape raw m (terminalWire M t hF st B hk c hc extent R J N E T v g room wireRoom advice nt ns np root) := by
  refine PhysicalStage.transferWire_incidences (R.terminalLayer_shape v.1) (K).ports.form
    (result).1 (R.endWords_form v.1 J.steps U N).symm
    (terminalLocalWire M t hF st B hk c hc extent R J E T v g room wireRoom advice nt ns np)
    root tape raw m ?_
  intro z' hz
  have eqz : z'=z:=eq_of_heq (hz.trans sameRoot.symm)
  subst z'
  have sem:=terminalHalves M t hF st B hk extent R J v
  have edgeIndex (e : (X).shape.Edge) : ((X).wireOrder e).val=Halves.edgeNumber (X).order e := by
    obtain ⟨⟨a,b⟩,l⟩:=e
    exact (X).wireOrder_val a b l
  let extPin (y : (X).Site) (j : Fin ((K).ext y)) :=
    let p := R.extAncestor v.1 J.steps U y j
    Buckets.packEndpoint c hc T v g room advice nt ns np (seedEndpoint L low p.1 p.2)
  refine PhysicalStage.orderedIncidences (u := age) (teams := teams) (cap := cap)
    (q := advice) (nt := nt) (ns := ns) (np := np) X K z wireRoom tape raw m extPin
    external (count.trans (sem.count z).symm) endpoints origin ?_ ?_ ?_ prefixes
  · intro b
    rw [edgeIndex,sem.edge z b]
    exact (halfRows (b.cast (sem.count z))).1
  · intro b
    change (half tape raw b.val).width=(X).width ((K).order z b).val.1
    rw [sem.edge z b]
    exact (halfRows (b.cast (sem.count z))).2.1
  · intro b
    exact (halfRows (b.cast (sem.count z))).2.2.trans (sem.start z b)

end
end ThreeFlat.Diagonal.TraceBitHeader

end OAI
