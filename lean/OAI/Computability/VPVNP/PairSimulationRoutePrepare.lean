import OAI.Computability.VPVNP.PairSimulationLeafArena
import OAI.Computability.VPVNP.PairSimulationLeafPhysicalInput
import OAI.Computability.VPVNP.PairSimulationLeafIncidentGeometry
import OAI.Computability.VPVNP.PairSimulationRouteSchedule

/-!
# Preparing the routing checker from the private DFS arguments

A leaf enters with a decoded cursor, site and descriptor address. Fourteen
instructions copy the coordinates, compute the descriptor's argument base,
and read the three geometry words in the operand cache. Fifteen arithmetic
instructions compute the successor and sorting widths and the four buffer
bases. Every instruction contributes one tick.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RoutePrepare

open BurstRAM PrivateRAM PrimedCounter.GuessWord CursorRouting CursorNetwork RAMLayout
open NodeArguments
open LeafIncidentGeometry (Line)
open scoped Fin.CommRing

variable {D H w W p r k : ℕ}

/-- Public pointers to the argument arena and the private geometry cache. -/
inductive Field where
  | start | stride | cache
  deriving DecidableEq

instance : Fintype Field :=
  ⟨{.start,.stride,.cache}, fun i => by cases i <;> decide⟩

/-- The labels of the operand fetches and the arithmetic sequence. -/
abbrev Stage := Fin 14 ⊕ Fin 15

/-- Number of native private instructions before the first route test. -/
def ticks : ℕ := 29

/-- Host-word address of the first bit of a stored half-wire. -/
def portBase (A : Arena) (node D H w : ℕ) (port : LocalPort) : Word W :=
  (LeafHandler.portBase A node (ramPayloadWidth D H w) port : Word W)

private def fetch (pc : Fin 14 → Fin p) (reg : Fin 32 ↪ Fin r) (leaf : LeafAddress.Reg ↪ Fin r)
    (pub : Field → Fin k) (next : Fin p) : Fin 14 → Instr W p r k :=
  ![.copy (reg 0) (leaf .cursor) (pc 1),
    .copy (reg 1) (leaf .site) (pc 2),
    .publicWord (reg 7) (pub .stride) (pc 3),
    .binary .mul (reg 12) (leaf .node) (reg 7) (pc 4),
    .publicWord (reg 7) (pub .start) (pc 5),
    .binary .add (reg 12) (reg 7) (reg 12) (pc 6),
    .publicWord (reg 7) (pub .cache) (pc 7),
    .loadPrivate (reg 2) (reg 7) (pc 8),
    .constant (reg 23) 1 (pc 9),
    .binary .add (reg 7) (reg 7) (reg 23) (pc 10),
    .loadPrivate (reg 8) (reg 7) (pc 11),
    .binary .add (reg 7) (reg 7) (reg 23) (pc 12),
    .loadPrivate (reg 29) (reg 7) (pc 13),
    .constant (reg 17) 0 next]

private def rows : List Line :=
  [(7,.literal 8), (21,.binary .mul 7 8),
   (7,.literal 20), (29,.binary .mul 7 29), (29,.binary .mul 29 8),
   (7,.binary .add 2 23), (7,.binary .mul 7 2), (8,.literal 2), (7,.binary .div 7 8),
   (7,.binary .mul 7 29), (8,.binary .mul 2 21), (7,.binary .add 8 7),
   (13,.binary .add 12 7), (14,.binary .add 13 7), (15,.binary .add 14 7)]

private def arithmeticRegs (reg : Fin 32 ↪ Fin r) : Fin 30 ↪ Fin r :=
  (Fin.castLEEmb (by decide)).trans reg

private def target (pc : Stage → Fin p) (done : Fin p) (i : Fin (rows.length + 1)) : Fin p :=
  if h : i.val < 15 then pc (.inr ⟨i.val,h⟩) else done

/-- The leaf, route and public banks can be embedded at any host indices. -/
def instruction (pc : Stage → Fin p) (reg : Fin 32 ↪ Fin r) (leaf : LeafAddress.Reg ↪ Fin r)
    (pub : Field → Fin k) (done : Fin p) : Stage → Instr W p r k
  | .inl i => fetch (pc ∘ Sum.inl) reg leaf pub (pc (.inr 0)) i
  | .inr i => LeafIncidentGeometry.emit (arithmeticRegs reg) (target pc done i.succ) rows[i]

theorem resize_instruction (pc : Stage → Fin p) (reg : Fin 32 ↪ Fin r)
    (leaf : LeafAddress.Reg ↪ Fin r) (pub : Field → Fin k) (done : Fin p) (i : Stage) :
    (instruction (W := 5) pc reg leaf pub done i).resize W =
      instruction pc reg leaf pub done i := by
  cases i with
  | inl i => fin_cases i <;> rfl
  | inr i => fin_cases i <;> rfl

/-- Every setup instruction is present at its designated machine label. -/
def Linked (M : Machine W p r k) (pc : Stage → Fin p) (reg : Fin 32 ↪ Fin r)
    (leaf : LeafAddress.Reg ↪ Fin r) (pub : Field → Fin k) (done : Fin p) : Prop :=
  ∀ i, M.code (pc i) = instruction pc reg leaf pub done i

/-- Native operands at entry, after the leaf address decoder. -/
structure Ready (M : Machine W p r k) (leaf : LeafAddress.Reg ↪ Fin r) (pub : Field → Fin k)
    (R : LeafArena.Regions) (node H w : ℕ) (v : Position D) (c : Config W p r) : Prop where
  cursor : c.reg (leaf .cursor) = (v.1.val : Word W)
  site : c.reg (leaf .site) = (v.2.val : Word W)
  address : c.reg (leaf .node) = (node : Word W)
  start : M.publicData (pub .start) = (R.arguments.start : Word W)
  stride : M.publicData (pub .stride) = (R.arguments.stride : Word W)
  cacheBase : M.publicData (pub .cache) = (R.cacheBase : Word W)
  dimension : c.privateMem (R.cacheBase : Word W) = (D : Word W)
  width : c.privateMem ((R.cacheBase+1 : ℕ) : Word W) = (w : Word W)
  bucket : c.privateMem ((R.cacheBase+2 : ℕ) : Word W) = (H : Word W)

variable {M : Machine W p r k} {pc : Stage → Fin p} {reg : Fin 32 ↪ Fin r}
  {leaf : LeafAddress.Reg ↪ Fin r} {pub : Field → Fin k} {done : Fin p}
  {R : LeafArena.Regions} {node : ℕ} {v : Position D}

private structure Fetched (bank : Fin 30 → Word W) (R : LeafArena.Regions) (node H w : ℕ)
    (v : Position D) : Prop where
  cursor : bank 0 = (v.1.val : Word W)
  site : bank 1 = (v.2.val : Word W)
  dimension : bank 2 = (D : Word W)
  width : bank 8 = (w : Word W)
  arena : bank 12 = (R.arguments.base node : Word W)
  zero : bank 17 = 0
  one : bank 23 = 1
  bucket : bank 29 = (H : Word W)

private theorem fetch_run (link : Linked M pc reg leaf pub done) (apart : ∀ j i, leaf j ≠ reg i)
    (c : Config W p r) (entry : c.pc = pc (.inl 0)) (h : Ready M leaf pub R node H w v c) :
    ∃ q, Prefix M c (List.replicate 14 .tick) q ∧ q.pc = pc (.inr 0) ∧
      Fetched (q.reg ∘ arithmeticRegs reg) R node H w v ∧ q.privateMem = c.privateMem ∧
      q.persistent = c.persistent ∧ ∀ j, (∀ i, j ≠ reg i) → q.reg j = c.reg j := by
  have step (i : Fin 14) {d : Config W p r} (hi : d.pc = pc (.inl i)) :
      M.program.step d =
        (fetch (pc ∘ Sum.inl) reg leaf pub (pc (.inr 0)) i).run M.publicData d := by
    change (M.code d.pc).run _ _ = _
    rw [hi,link]; rfl
  refine ⟨_, .tick (step 0 entry) (.tick (step 1 rfl) (.tick (step 2 rfl) (.tick (step 3 rfl)
    (.tick (step 4 rfl) (.tick (step 5 rfl) (.tick (step 6 rfl) (.tick (step 7 rfl)
    (.tick (step 8 rfl) (.tick (step 9 rfl) (.tick (step 10 rfl) (.tick (step 11 rfl)
    (.tick (step 12 rfl) (.tick (step 13 rfl) (.nil _)))))))))))))), rfl, ?_, rfl, rfl, ?_⟩
  · have width : c.privateMem ((R.cacheBase : Word W)+1) = (w : Word W) := by
      simpa only [Nat.cast_add,Nat.cast_one] using h.width
    have bucket : c.privateMem ((R.cacheBase : Word W)+1+1) = (H : Word W) := by
      rw [show (R.cacheBase : Word W)+1+1 = ((R.cacheBase+2 : ℕ) : Word W) by push_cast; ring]
      exact h.bucket
    constructor <;> simp (config := {decide := true}) [arithmeticRegs, Config.put,
      reg.injective.eq_iff, apart, BinaryOp.eval, h.cursor, h.site,
      h.address, h.start, h.stride, h.cacheBase, h.dimension, width, bucket, Arena.base]
  · intro j hj
    simp only [Config.put, Function.update_of_ne (hj _)]

open private sequence assign_at assign_frame layers eval_add eval_mul from
  OAI.Computability.VPVNP.PairSimulationLeafIncidentGeometry

private structure Calculated (bank : Fin 30 → Word W) (R : LeafArena.Regions) (node H w : ℕ)
    (v : Position D) : Prop where
  cursor : bank 0 = (v.1.val : Word W)
  site : bank 1 = (v.2.val : Word W)
  dimension : bank 2 = (D : Word W)
  base₀ : bank 12 = portBase R.arguments node D H w (.outgoing false)
  base₁ : bank 13 = portBase R.arguments node D H w (.outgoing true)
  base₂ : bank 14 = portBase R.arguments node D H w (.incoming false)
  base₃ : bank 15 = portBase R.arguments node D H w (.incoming true)
  zero : bank 17 = 0
  successor : bank 21 = ((8*w : ℕ) : Word W)
  one : bank 23 = 1
  sorting : bank 29 = (blockBits H w : Word W)

private theorem calculated (bank : Fin 30 → Word W) (h : Fetched bank R node H w v) (hw : D < W) :
    Calculated (rows.foldl (fun b l => Function.update b l.1 (l.2.eval b)) bank) R node H w v := by
  have tri := layers D hw (by have := v.1.isLt; omega)
  constructor <;> simp (config := {decide := true}) [rows, LeafIncidentGeometry.Operand.eval,
    Function.update, eval_add, eval_mul, h.cursor, h.site, h.dimension, h.arena, h.zero,
    h.one, h.width, h.bucket, tri, portBase, LeafHandler.portBase, LeafArguments.portNumber,
    ramPayloadWidth, blockBits] <;> ring

/-- Word addresses used by the checker read the four consecutive packet intervals. -/
theorem resident_of_stored {buf : Buffers D H w} {A : Arena} {c : Config W p r}
    (stored : LeafIncidentLoad.Stored (LeafHandler.portBase A node (ramPayloadWidth D H w))
      buf c.privateMem) : RouteCall.Resident c (portBase A node D H w) buf := by
  intro port i
  have h := stored port i
  let start := LeafHandler.portBase A node (ramPayloadWidth D H w) port
  change c.privateMem ((start + i.val : ℕ) : Word W) = _ at h
  change c.privateMem ((start : Word W) + _) = _
  rw [← Nat.cast_add,h]
  cases buf port i <;> rfl

/-- After a stored DFS packet, the checker reads its independently supplied
half-wire bits. The DFS stack below the scratch boundary can have arbitrary contents. -/
theorem resident_cursorPacket {b l a pad endAddr : ℕ} [NeZero (b + l)]
    (hD : 1 < b + l) (hd : 2 + pad = 2 ^ a) (A : Arena) (addr : Word W)
    (v : Position (b + l))
    (z : (LeafArguments.state hD hd H w).network.Half
      (lanePositions (cursorCoordinateLabels b l) v)) (c : Config W p r)
    (fit : (LeafHandler.cursorPacket hD hd addr.val v z).Fits A W endAddr)
    (stored : (LeafHandler.cursorPacket hD hd addr.val v z).Stored A
      (DFS.scratch endAddr c.privateMem)) :
    RouteCall.Resident c (portBase A addr.val (b + l) H w) (LeafArguments.buffers hD hd v z) := by
  apply resident_of_stored
  intro port i
  have bits := LeafHandler.physicalStored hD hd A addr _ v z fit stored port i
  let size := ramPayloadWidth (b + l) H w
  let offset := LeafHandler.portBase A addr.val size port + i.val
  have lower : A.base addr.val ≤ offset := by
    cases port <;> simp only [offset,LeafHandler.portBase] <;> omega
  have upper : offset < A.base addr.val + 4*size := by
    have hi : i.val < size := i.isLt
    cases port with | outgoing side | incoming side =>
      cases side <;> simp [offset,LeafHandler.portBase,LeafArguments.portNumber] <;> omega
  have len : (LeafHandler.cursorPacket hD hd addr.val v z).bits.length = 4*size :=
    LeafArguments.packed_length_four hD hd _ z
  have small : offset < 2^W := upper.trans_le (len ▸ fit.2.2)
  have inScratch : endAddr ≤ ((offset : Word W)).val := by
    change endAddr ≤ offset % 2^W
    rw [Nat.mod_eq_of_lt small]
    exact fit.1.trans lower
  change rawScratch (DFS.scratch endAddr c.privateMem) (offset : Word W) = _ at bits
  have read := (dite_eq_left inScratch :
    rawScratch (DFS.scratch endAddr c.privateMem) (offset : Word W) = _)
  exact read.symm.trans bits

/-- The linked code enters the scheduler with all coordinates, widths and
private bases initialized and preserves every register outside its routing bank. -/
theorem run (link : Linked M pc reg leaf pub done) (apart : ∀ j i, leaf j ≠ reg i)
    (c : Config W p r) (entry : c.pc = pc (.inl 0)) (h : Ready M leaf pub R node H w v c)
    (hw : D < W) {buf : Buffers D H w}
    (resident : RouteCall.Resident c (portBase R.arguments node D H w) buf) :
    ∃ d, Prefix M c (List.replicate ticks .tick) d ∧ d.pc = done ∧
      RouteSchedule.Inputs reg v buf (portBase R.arguments node D H w) d ∧
      d.reg (reg 21) = ((8*w : ℕ) : Word W) ∧ d.privateMem = c.privateMem ∧
      d.persistent = c.persistent ∧ ∀ j, (∀ i, j ≠ reg i) → d.reg j = c.reg j := by
  obtain ⟨q,pre,hpc,hq,mem,per,frame⟩ := fetch_run link apart c entry h
  let regs := arithmeticRegs reg
  have tail := sequence M regs rows (target pc done) (fun i => by
    have atPC : target pc done i.castSucc = pc (.inr i) := by
      simp [target,show i.val < 15 from i.isLt]; congr 1
    rw [atPC]; exact link (.inr i)) q (by simpa [target] using hpc)
  have last : target pc done (Fin.last rows.length) = done := rfl
  rw [last] at tail
  have combined : Prefix M c (List.replicate ticks .tick) _ := pre.append tail
  refine ⟨_, combined, rfl, ?_⟩
  · have result := calculated (q.reg ∘ regs) hq hw
    rw [← assign_at] at result
    refine ⟨⟨result.cursor, result.site, result.dimension, ?_, ?_, result.zero, result.one,
      result.sorting, ?_⟩,
      result.successor,mem,per,?_⟩
    · intro b; cases b with | false => exact result.base₀ | true => exact result.base₁
    · intro b; cases b with | false => exact result.base₂ | true => exact result.base₃
    · intro port i
      change q.privateMem _ = _
      rw [mem]; exact resident port i
    · intro j hj
      exact (assign_frame regs rows q.reg j (fun l _ => hj _)).trans (frame j hj)

end PairSimulation.RoutePrepare

end VPVNP
end Computability
end OAI
