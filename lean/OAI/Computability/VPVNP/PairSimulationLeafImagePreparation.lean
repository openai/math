import OAI.Computability.VPVNP.PairSimulationLeafImage
import OAI.Computability.VPVNP.PairSimulationLeafBootClock
import OAI.Computability.VPVNP.PairSimulationLeafIncidentArena
import OAI.Computability.VPVNP.PairSimulationLeafPhysicalInput

/-! # Running the actual finite cursor-leaf image on a stored DFS packet -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafVisit

open BurstRAM PrivateRAM CursorRouting CursorNetwork LeafHandler LeafStartup DFS
open NodeArguments LocalHistory TraversalRows PrimedCounter.GuessWord
open scoped Fin.CommRing

set_option synthInstance.maxSize 10000

variable {w p r k : ℕ} {A : PrimedInputRAM.Lengths} {n a H s : ℕ}
    {Q : PrimedInputRAM.Layout A n a H w} (D : PrimedCounter.Data Q s)
    {b l e degree pad endAddr : ℕ} [NeZero (b+l)]
    (hD : 1 < b+l) (hd : 2+pad = 2^degree) (budget : ProcessorBudget n (b+l) e w)
    (R : LeafArena.Regions) (cap : ℕ)
    (fit : R.stackBase + Fintype.card ScalarPort*n^40 < 2^w)

/-- The auxiliary stack layout in the leaf's private arena, assigning capacity n^40 to each
port in the fixed port order. -/
noncomputable abbrev storage := R.layout portOrder.symm.toEmbedding (n^40) fit

/-- The whole deterministic prefix, including the seven operand-transfer
instructions on a cursor-zero visit. -/
noncomputable def trace (m : Memory w) (fields : LeafAddress.Field → Word w)
    (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) : List (Event w) :=
  LeafFront.trace m fields v e w ++
    if v.1 = 0 then List.replicate (7+LeafBoot.ticks D budget.tags budget.capFits v.2 buf) .tick else []

/-- Decode the node and its private buffers into a leaf handler input, including the prefix
trace and the initialized auxiliary scratch for a cursor-zero visit. -/
noncomputable def loaded (fields : LeafAddress.Field → Word w) (m : Memory w)
    (node : Word w) (saved : Scratch w endAddr) : Input (b+l) e w w endAddr :=
  let v := physicalPosition (b+l) fields node
  let buf := physicalBuffers (b+l) (2^e) w R.arguments node saved
  let bank := auxiliaryBank D budget.tags budget.capFits v buf
  ⟨v,buf,trace D budget m fields v buf,
    if v.1 = 0 then LeafLoadedBank.scratch (storage R fit) bank saved else saved⟩

/-- The static words cached for the leaf initializer, giving the cursor dimension, word width,
bucket size, auxiliary fuel, and public operands. -/
def cacheWords (d e : ℕ) : LeafSourceLoad.Static 34 → Word w
  | .d => d | .width => w | .bucket => ((2^e : ℕ) : Word w) | .fuel => D.fuel | .operand i => D.pub i

private theorem cache_eq {d : ℕ} (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
    (v : Position d) (buf : Buffers d (2^e) w) :
    (fun j : LeafSourceLoad.Static 34 => LeafRegisterBank.sourceWord (auxiliary D hw hc v buf) D.pub j.dest) =
      cacheWords D d e := by
  funext i; cases i <;> rfl

/-- Data actually stored by the parent node and the final-site cache writer.
The buffers need no compatibility condition across distinct wires. -/
def Domain (fields : LeafAddress.Field → Word w) (node : Word w) (saved : Scratch w endAddr) : Prop :=
  node.val < R.nodes ∧ LeafSourceLoad.Cached R.cacheBase (rawScratch saved) (cacheWords D (b+l) e) ∧
    ∃ (v : Position (b+l))
      (z : (LeafArguments.state hD hd (2^e) w).network.Half (lanePositions (cursorCoordinateLabels b l) v)),
      node.val = (sitePointers cap (fields .base).val (siteOrder (LeafArguments.state hD hd (2^e) w))
        (lanePositions (cursorCoordinateLabels b l) v)).1 ∧
      (cursorPacket hD hd node.val v z).Fits R.arguments w endAddr ∧
      (cursorPacket hD hd node.val v z).Stored R.arguments saved

include fit in
private theorem cache_actual {endAddr : ℕ} (lo : endAddr ≤ R.arguments.start)
    (m : Word w → Word w) (vals : LeafSourceLoad.Static 34 → Word w)
    (cached : LeafSourceLoad.Cached R.cacheBase (rawScratch (scratch endAddr m)) vals) :
    LeafSourceLoad.Cached R.cacheBase m vals := by
  intro i
  have jlt : i.offset < 38 := by cases i <;> simp [LeafSourceLoad.Static.offset]; omega
  have upper : R.cacheBase + i.offset < 2^w :=
    (R.cache_before ⟨_,jlt⟩).trans ((Nat.le_add_right _ _).trans_lt fit)
  have low : endAddr ≤ R.cacheBase := by
    unfold LeafArena.Regions.cacheBase LeafArena.Regions.histBase Arena.base; omega
  have lower : endAddr ≤ ((R.cacheBase+i.offset : ℕ) : Word w).val := by
    rw [Fin.val_natCast,Nat.mod_eq_of_lt upper]; omega
  have h := cached i
  simpa only [rawScratch,lower,↓reduceDIte,scratch] using h

private theorem bits_ticks (n : ℕ) : choiceBits (List.replicate n (.tick : Event w)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,choiceBits] using ih

theorem trace_bits (m : Memory w) (fields : LeafAddress.Field → Word w)
    (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) : choiceBits (trace D budget m fields v buf) = [] := by
  rw [trace,PrimedInputRAM.Flow.choiceBits_append,(LeafFront.trace_cost m fields v e w).2,List.nil_append]
  split <;> first | exact bits_ticks _ | rfl

variable {M : Machine w p r k} (pc : LeafImage.Label → Fin p) (reg : LeafImage.Reg ↪ Fin r)
    (pub : LeafImage.Pub → Fin k) (ret : Fin p) (m : Memory w)

/-- Read the address decoder's public operands from the linked machine through the leaf's port
assignment. -/
abbrev fields := M.publicData ∘ pub ∘ LeafImage.Pub.address

set_option maxHeartbeats 1600000 in
/-- Every row of the concrete finite leaf image executes the deterministic
prefix required by the DFS hook, including the malformed-route exit. -/
theorem preparation (link : LeafImage.Linked pc reg pub ret M)
    (op : LeafFront.Operands (LeafImage.front pc reg pub ret) M m D R b l cap)
    (hsize : M.publicData (pub .size) = (n : Word w)) (lo : endAddr ≤ R.arguments.start)
    (room : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length ≤ n^40) :
    Preparation (endAddr := endAddr) D budget.tags budget.capFits (storage R fit) (loaded D budget R fit (fields (M := M) pub) m)
      (Domain (e := e) D hD hd R cap (fields (M := M) pub)) M (pc (.address 0)) ret (LeafImage.dfsReg reg)
      (LeafImage.stackPC pc) (LeafBoot.stack (LeafImage.bootReg reg)) m := by
  let P := LeafImage.front pc reg pub ret
  let f := fields (M := M) pub
  let L := storage R fit
  let boot := LeafImage.bootReg reg
  have hW := (RouteSchedule.hostFits budget (le_refl w)).1.le
  have actual (node : Word w) (c : Config w p r) (dom : Domain (e := e) D hD hd R cap f node (scratch endAddr c.privateMem))
      (hc : c.pc = pc (.address 0)) (hn : c.reg (LeafImage.dfsReg reg 7) = node) :
      ∃ (v : Position (b+l)) (z : (LeafArguments.state hD hd (2^e) w).network.Half
        (lanePositions (cursorCoordinateLabels b l) v)),
        let buf := LeafArguments.buffers hD hd v z
        let x := loaded D budget R fit f m node (scratch endAddr c.privateMem)
        x = ⟨v,buf,trace D budget m f v buf,if v.1 = 0 then
          LeafLoadedBank.scratch L (auxiliaryBank D budget.tags budget.capFits v buf) (scratch endAddr c.privateMem)
          else scratch endAddr c.privateMem⟩ ∧
        (cursorPacket hD hd node.val v z).Fits R.arguments w endAddr ∧
        (cursorPacket hD hd node.val v z).Stored R.arguments (scratch endAddr c.privateMem) ∧
        LeafSourceLoad.Cached R.cacheBase c.privateMem (cacheWords D (b+l) e) ∧
        (routeAccept (2^e) w v (readBuffer buf) = true → ∃ q, LeafFront.Result P D v c q ∧
          ∀ fuel bits, execute M.program (fuel+(LeafFront.trace m f v e w).length) c m bits =
          (execute M.program fuel q m bits).map fun x => ⟨LeafFront.trace m f v e w++x.events,x.result⟩) ∧
        (routeAccept (2^e) w v (readBuffer buf) = false → ∀ bs, ¬Returns M c m bs) := by
    obtain ⟨_,hc',v,z,row,space,stored⟩ := dom
    have cache := cache_actual R fit lo c.privateMem (cacheWords D (b+l) e) hc'
    have cache3 := LeafFront.Cache.of_cached cache (show cacheWords D (b+l) e .d = _ from rfl)
      (show cacheWords D (b+l) e .width = _ from rfl) (show cacheWords D (b+l) e .bucket = _ from rfl)
    have pf := LeafFront.native link.front m D R cap op hD hd budget (le_refl _) node v z c hc hn
      row cache3 space stored
    refine ⟨v,z,?_,space,stored,cache,pf⟩
    unfold loaded
    rw [physicalPosition_eq hD hd f node cap v hW op.stride op.radixB op.radixL row,
      physicalBuffers_eq hD hd R.arguments node _ v z (by omega) space stored]
  constructor
  · intro node saved _
    exact trace_bits D budget m f _ _
  · intro node c top pending dom hc hn hs hend _ _ _
    obtain ⟨v,z,eq,space,stored,cache,good,_⟩ := actual node c dom hc hn
    let buf := LeafArguments.buffers hD hd v z
    intro x hr
    have hx : x = _ := eq
    rw [hx] at hr ⊢
    obtain ⟨q,qres,qr⟩ := good hr
    have qframe (i : Fin 9) := qres.frame _ (LeafImage.dfs_preserved reg i) (LeafImage.dfs_ne_route reg i)
    by_cases zero : v.1 = 0
    · have zv : v = (0,v.2) := Prod.ext zero rfl
      let root := v.2
      obtain ⟨a',ha,ap,site,header,cp,bp,memA,pstA,regA⟩ :=
        LeafBootHandoff.run M (pc ∘ LeafImage.Label.handoff) boot (LeafImage.leafReg reg) (pub ∘ LeafImage.Pub.arena)
          (LeafImage.bootPC pc (.pre 0)) link.handoff (LeafImage.leaf_ne_boot reg .header _)
          (LeafImage.dfs_not_written reg 7) R node.val (root.val : Word w) (D.initial root.val) q
          (by change q.pc = pc (.handoff 0); exact qres.pc.trans (ite_eq_left zero))
          (Fin.ext (qres.site.trans (Nat.mod_eq_of_lt (qres.site ▸ (q.reg (P.leaf .site)).isLt)).symm))
          (Fin.ext qres.header) (by change q.reg (P.leaf .node) = (node.val : Word w); rw [qres.node, show c.reg (P.leaf .node) = node from hn]; simp)
          op.cacheBase op.arenaStride op.arenaStart
      have old : a'.privateMem = c.privateMem := memA.trans qres.memory
      have hlen : (cursorPacket hD hd node.val v z).bits.length = 4*ramPayloadWidth (b+l) (2^e) w :=
        LeafArguments.packed_length_four hD hd _ z
      have before : R.arguments.base node.val + 4*ramPayloadWidth (b+l) (2^e) w ≤ R.stackBase := by
        have h₁ := R.node_before dom.1
        have h₂ := hlen ▸ space.2.1
        unfold LeafArena.Regions.stackBase LeafArena.Regions.cacheBase; omega
      have incident : LeafIncidentLoad.Stored
          (LeafIncidentMachine.base (R.arguments.base node.val) (ramPayloadWidth (b+l) (2^e) w)) buf a'.privateMem := by
        intro port j
        have res := RoutePrepare.resident_cursorPacket hD hd R.arguments node v z c space stored port j
        rw [old]
        change c.privateMem (LeafFieldCopy.word w (_ + j.val)) = _
        change c.privateMem (((LeafHandler.portBase R.arguments node.val _ port : ℕ) : Word w) + _) = _ at res
        rw [← Nat.cast_add] at res
        have eqBit (x : Bool) : (x.toNat : Word w) = PrivateFields.bitValue w x := by cases x <;> rfl
        rw [eqBit] at res
        cases port with | outgoing side | incoming side =>
          cases side <;> simpa [LeafFieldCopy.word,LeafIncidentMachine.base,LeafHandler.portBase,LeafArguments.portNumber,buf] using res
      obtain ⟨out,run,outpc,rep,pst,regs,_,pendingOk,scratchOk⟩ :=
        LeafBoot.run D budget.tags budget.capFits root buf M (LeafImage.bootPC pc) boot (pub .size)
          (LeafImage.stackPC pc auxiliaryEntry 0) link.boot R (R.arguments.base node.val) fit before a' ap
          bp cp hsize site header (by rw [old,cache_eq]; exact cache) incident
          (room (0,root) buf) pending hend (old ▸ hs) lo
      have sf : scratch endAddr a'.privateMem = scratch endAddr c.privateMem := congrArg (scratch endAddr) old
      have zz : auxiliaryBank D budget.tags budget.capFits v buf = auxiliaryBank D budget.tags budget.capFits (0,root) buf :=
        congrArg (fun v => auxiliaryBank D budget.tags budget.capFits v buf) zv
      refine ⟨out,?_,pst.trans (pstA.trans qres.persistent),fun i _ =>
        (regs _ (LeafImage.dfs_offBoot reg i)).trans ((regA _ (LeafImage.dfs_not_written reg i)).trans (qframe i)),
        pendingOk,?_,fun _ => ?_,?_⟩
      · simpa only [zero,↓reduceIte] using outpc
      · rw [ite_eq_left zero]
        change scratch endAddr out.privateMem =
          LeafLoadedBank.scratch L (auxiliaryBank D budget.tags budget.capFits v buf) (scratch endAddr c.privateMem)
        rw [zz,←sf]
        exact scratchOk
      · change StackMachine.Represents L (LeafBoot.stack boot) out (auxiliaryBank D budget.tags budget.capFits v buf)
        rw [zz]
        exact rep
      · intro fuel bits
        let g := LeafFront.trace m f v e w
        let t := LeafBoot.ticks D budget.tags budget.capFits root buf
        have tail := ha.append run
        change Prefix M q (List.replicate 7 .tick ++ List.replicate t .tick) out at tail
        rw [← List.replicate_add] at tail
        have htail := tail.execute fuel m bits
        simp only [List.length_replicate,bits_ticks,List.nil_append] at htail
        change execute M.program (fuel+(trace D budget m f v buf).length) c m bits = _
        simp only [trace,zero,↓reduceIte,List.length_append,List.length_replicate]
        rw [show fuel+((LeafFront.trace m f v e w).length+(7+t))=(fuel+(7+t))+g.length by dsimp [g]; omega,
          qr,htail]
        simp only [Option.map_map,Function.comp_def,List.append_assoc]; rfl
    · refine ⟨q,?_,qres.persistent,fun i _ => qframe i,qres.memory ▸ hs,?_,fun hz => (zero hz).elim,?_⟩
      · simpa only [zero,↓reduceIte,P,LeafImage.front] using qres.pc
      · simp only [zero,↓reduceIte,qres.memory]
      · intro fuel bits
        simpa only [trace,zero,↓reduceIte,List.append_nil] using qr fuel bits
  · intro node c top pending dom hc hn _ _ _ _ _ hr
    obtain ⟨v,z,eq,_,_,_,_,reject⟩ := actual node c dom hc hn
    rw [eq] at hr
    exact reject (Bool.eq_false_iff.mpr hr)

end PairSimulation.LeafVisit

end VPVNP
end Computability
end OAI
