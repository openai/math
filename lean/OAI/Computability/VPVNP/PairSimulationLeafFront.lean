import OAI.Computability.VPVNP.PairSimulationRoutePrepare
import OAI.Computability.VPVNP.PairSimulationLeafCachedSources
import OAI.Computability.VPVNP.RAMProcessorReportPrefix
import OAI.Computability.VPVNP.PairSimulationLeafRouteFork

/-!
# The deterministic front of a physical cursor leaf

The descriptor pointer determines the cursor, site and shadow header. The
setup then reads the cached virtual dimensions and the four fields of the
stored packet. A passed route enters the private validator at cursor zero
and returns at a transit cursor. An inconsistent route rejects in this call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafFront

open BurstRAM PrivateRAM PrimedCounter.GuessWord CursorRouting CursorNetwork RAMLayout
open PrimedInputRAM Compression LocalHistory TraversalRows DFS
open scoped Fin.CommRing

variable {W p r k : ℕ}

/-- Labels and operand allocations for the decoded-address and routing prefix. -/
structure Program (p r k : ℕ) where
  /-- Leaf-address decode and translated header read. -/
  addressPC : Fin 20 → Fin p
  /-- The address-reader registers, including the persistent input node slot. -/
  leaf : LeafAddress.Reg ↪ Fin r
  /-- The public address-reader operands. -/
  addressPub : LeafAddress.Field → Fin k
  /-- The 29 setup instructions after either address-reader exit. -/
  preparePC : RoutePrepare.Stage → Fin p
  /-- The public arena and cache pointers. -/
  preparePub : RoutePrepare.Field → Fin k
  /-- The complete route scan. -/
  route : RouteSchedule.Program p r
  /-- Entry to the cursor-zero validator initialization. -/
  init : Fin p
  /-- Return to the caller at a transit cursor. -/
  transit : Fin p
  apart : ∀ j i, leaf j ≠ route.reg i

variable (P : Program p r k)

/-- Both address-reader exits join the setup before the routing test. -/
structure Program.Linked (M : Machine W p r k) : Prop where
  address : LeafAddress.Linked M P.addressPC P.leaf P.addressPub
    (P.preparePC (.inl 0)) (P.preparePC (.inl 0))
  prepare : RoutePrepare.Linked M P.preparePC P.route.reg P.leaf P.preparePub (P.route.pc 0)
  route : P.route.Linked M
  pass : M.code P.route.yes = .jumpEq (P.route.reg 0) (P.route.reg 17) P.init P.transit
  fail : M.code P.route.no = .reject

variable {D e w : ℕ} [NeZero D]

/-- Exact event list on a passed route. Only the header access may probe
external memory, and the complete list consumes no branch bits. -/
def trace (m : Memory W) (pub : LeafAddress.Field → Word W) (v : Position D) (e w : ℕ) :
    List (Event W) :=
  LeafAddress.events m (pub .shadow) (pub .span) (v.2.val : Word W) ++
    List.replicate (RoutePrepare.ticks + (RouteSchedule.routeTicks W v (2 ^ e) w + 1)) .tick

private theorem tick_bits (n : ℕ) : choiceBits (List.replicate n (.tick : Event W)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, choiceBits, ih]

theorem trace_cost (m : Memory W) (pub : LeafAddress.Field → Word W) (v : Position D) (e w : ℕ) :
    (trace m pub v e w).length =
      19 + (RoutePrepare.ticks + (RouteSchedule.routeTicks W v (2 ^ e) w + 1)) ∧
      choiceBits (trace m pub v e w) = [] := by
  have h := LeafAddress.cost m (pub .shadow) (pub .span) (v.2.val : Word W)
  exact ⟨by simp [trace, h.1], by simp [trace, Flow.choiceBits_append, h.2.2, tick_bits]⟩

/-- The only external probe in the front is the translated header read, exactly
when the site's address is within the prepared shadow region. -/
theorem trace_probes (m : Memory W) (pub : LeafAddress.Field → Word W) (v : Position D) (e w : ℕ) :
    countProbes (trace m pub v e w) = (decide ((v.2.val : Word W) < pub .span)).toNat := by
  have ticks (n : ℕ) : countProbes (List.replicate n (.tick : Event W)) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, countProbes, ih]
  rw [trace, countProbes_append, ticks, Nat.add_zero]
  exact (LeafAddress.cost m (pub .shadow) (pub .span) (v.2.val : Word W)).2.1

variable {L : Lengths} {n a H s b l t pad : ℕ} {Q : Layout L n a H w}
variable [NeZero (b + l)]

/-- Fixed arena pointers, cursor dimensions and prepared translated shadow
header, all read by the physical prefix. -/
structure Operands (P : Program p r k) (M : Machine W p r k) (m : Memory W)
    (data : PrimedCounter.Data Q s) (R : LeafArena.Regions) (b l cap : ℕ) : Prop where
  stride : (M.publicData (P.addressPub .stride)).val = cap + 2
  radixB : (M.publicData (P.addressPub .radixB)).val = 2 ^ b
  radixL : (M.publicData (P.addressPub .radixL)).val = 2 ^ l
  span : (M.publicData (P.addressPub .span)).val = LiveAuxiliaryHeaders.span L data.hist.length
  fits : (M.publicData (P.addressPub .shadow)).val + (M.publicData (P.addressPub .span)).val ≤ 2 ^ W
  header : ∀ i < (M.publicData (P.addressPub .span)).val,
    (m ((M.publicData (P.addressPub .shadow)).val + i)).val = (data.initial i).val
  arenaStart : M.publicData (P.preparePub .start) = (R.arguments.start : Word W)
  arenaStride : M.publicData (P.preparePub .stride) = (R.arguments.stride : Word W)
  cacheBase : M.publicData (P.preparePub .cache) = (R.cacheBase : Word W)

/-- Geometry words placed in the private operand cache by the enclosing
final-site call. -/
structure Cache (R : LeafArena.Regions) (d w H : ℕ) (mem : Word W → Word W) : Prop where
  dimension : mem (R.cacheBase : Word W) = (d : Word W)
  width : mem ((R.cacheBase + 1 : ℕ) : Word W) = (w : Word W)
  bucket : mem ((R.cacheBase + 2 : ℕ) : Word W) = (H : Word W)

/-- Recover the three geometry operands from the final-site private cache. -/
theorem Cache.of_cached {R : LeafArena.Regions} {mem : Word W → Word W} {d w H : ℕ}
    {vals : LeafSourceLoad.Static k → Word W} (cached : LeafSourceLoad.Cached R.cacheBase mem vals)
    (hd : vals .d = (d : Word W)) (hw : vals .width = (w : Word W))
    (hH : vals .bucket = (H : Word W)) : Cache R d w H mem :=
  ⟨(cached .d).trans hd, (cached .width).trans hw, (cached .bucket).trans hH⟩

/-- Successful native return data needed by the stack initializer and the DFS caller. -/
structure Result (P : Program p r k) (data : PrimedCounter.Data Q s) (v : Position (b + l))
    (c out : Config W p r) : Prop where
  pc : out.pc = (if v.1 = 0 then P.init else P.transit)
  cursor : (out.reg (P.leaf .cursor)).val = v.1.val
  site : (out.reg (P.leaf .site)).val = v.2.val
  header : (out.reg (P.leaf .header)).val = (data.initial v.2.val).val
  node : out.reg (P.leaf .node) = c.reg (P.leaf .node)
  frame : ∀ j, LeafAddress.Preserved P.leaf j → (∀ i, j ≠ P.route.reg i) → out.reg j = c.reg j
  memory : out.privateMem = c.privateMem
  persistent : out.persistent = c.persistent

private theorem off_bank {reg : Fin 32 ↪ Fin r} {j : Fin r} (h : ∀ i, j ≠ reg i) :
    RouteSchedule.Keep reg j :=
  ⟨⟨⟨fun i _ ↦ h i,h 4,h 16⟩,h 3,h 28⟩,h 21⟩

private theorem word_of_val {x : Word W} {a : ℕ} (h : x.val = a) : x = (a : Word W) :=
  Fin.ext (h.trans (Nat.mod_eq_of_lt (h ▸ x.isLt)).symm)

open private returns_prefix from OAI.Computability.VPVNP.PairSimulationDFSDecode

variable {P}

/-- The three linked stages implement the physical leaf front on every fitted
stored cursor packet. A failed route cannot return on any branch suffix. -/
theorem native {M : Machine W p r k} (hl : P.Linked M) (m : Memory W)
    (data : PrimedCounter.Data Q s) (R : LeafArena.Regions) (cap : ℕ)
    (op : Operands P M m data R b l cap) (hD : 1 < b + l) (hd : 2 + pad = 2 ^ t)
    (budget : ProcessorBudget n (b + l) e w) (host : w ≤ W)
    (node : Word W) (v : Position (b + l))
    (z : (LeafArguments.state hD hd (2 ^ e) w).network.Half
      (lanePositions (cursorCoordinateLabels b l) v))
    (c : Config W p r) (entry : c.pc = P.addressPC 0) (nodeReg : c.reg (P.leaf .node) = node)
    (row : node.val = (sitePointers cap (M.publicData (P.addressPub .base)).val
      (siteOrder (LeafArguments.state hD hd (2 ^ e) w))
      (lanePositions (cursorCoordinateLabels b l) v)).1)
    (cached : Cache R (b + l) w (2 ^ e) c.privateMem) {endAddr : ℕ}
    (fit : (LeafHandler.cursorPacket hD hd node.val v z).Fits R.arguments W endAddr)
    (stored : (LeafHandler.cursorPacket hD hd node.val v z).Stored R.arguments
      (scratch endAddr c.privateMem)) :
    let buf := LeafArguments.buffers hD hd v z
    let es := trace m (M.publicData ∘ P.addressPub) v e w
    (routeAccept (2 ^ e) w v (readBuffer buf) = true →
      ∃ out, Result P data v c out ∧ ∀ fuel bs, execute M.program (fuel + es.length) c m bs =
        (execute M.program fuel out m bs).map fun rep ↦ ⟨es ++ rep.events, rep.result⟩) ∧
    (routeAccept (2 ^ e) w v (readBuffer buf) = false → ∀ bs, ¬ Returns M c m bs) := by
  intro buf es
  let pub := M.publicData ∘ P.addressPub
  let tailCost := RoutePrepare.ticks + (RouteSchedule.routeTicks W v (2 ^ e) w + 1)
  obtain ⟨hW, _, _⟩ := RouteSchedule.hostFits budget host
  obtain ⟨q, hq, qcursor, qsite, qheader, qframe, qmem, qper, addrRun⟩ :=
    LeafAddress.leaf_native hl.address m c entry data hD hd (ramFieldBits (2 ^ e) w) cap v hW.le
      op.stride op.radixB op.radixL (nodeReg ▸ row) op.span op.fits op.header
  have qnode := (qframe _ (LeafAddress.preserved_node _)).trans nodeReg
  have prep : RoutePrepare.Ready M P.leaf P.preparePub R node.val (2 ^ e) w v q :=
    ⟨word_of_val qcursor, word_of_val qsite, qnode.trans (word_of_val rfl),
      op.arenaStart, op.arenaStride, op.cacheBase, qmem ▸ cached.dimension,
      qmem ▸ cached.width, qmem ▸ cached.bucket⟩
  let base := RoutePrepare.portBase (W := W) R.arguments node.val (b + l) (2 ^ e) w
  have resident : RouteCall.Resident q base buf := by
    intro port i
    rw [qmem]
    exact RoutePrepare.resident_cursorPacket hD hd R.arguments node v z c fit stored port i
  obtain ⟨u, setup, hu, inputs, width, umem, uper, uframe⟩ :=
    RoutePrepare.run hl.prepare P.apart q (by simpa using hq) prep hW resident
  obtain ⟨passed, failed⟩ :=
    LeafRouteFork.native budget host hl.route v buf base hu inputs width hl.pass hl.fail
  constructor
  · intro good
    obtain ⟨out, scan, ho, oframe⟩ := passed good
    have regKeep (j : Fin r) (hj : ∀ i, j ≠ P.route.reg i) : out.reg j = q.reg j :=
      (oframe.regs _ (off_bank hj)).trans (uframe j hj)
    have rleaf (j : LeafAddress.Reg) := regKeep (P.leaf j) (P.apart j)
    refine ⟨out, ⟨ho, (congrArg Fin.val (rleaf .cursor)).trans qcursor,
      (congrArg Fin.val (rleaf .site)).trans qsite,
      (congrArg Fin.val (rleaf .header)).trans qheader,
      (rleaf .node).trans (qframe _ (LeafAddress.preserved_node _)),
      fun j h₁ h₂ ↦ (regKeep j h₂).trans (qframe j h₁), oframe.memory.trans (umem.trans qmem),
      oframe.persistent.trans (uper.trans qper)⟩, ?_⟩
    have both : Prefix M q (List.replicate tailCost .tick) out := by
      rw [show tailCost = RoutePrepare.ticks + (RouteSchedule.routeTicks W v (2 ^ e) w + 1)
        from rfl, List.replicate_add]
      exact setup.append scan
    intro fuel bs
    have hlen : es.length = 19 + tailCost := (trace_cost m pub v e w).1
    have ht := both.execute fuel m bs
    simp only [List.length_replicate, tick_bits, List.nil_append] at ht
    rw [hlen, show fuel + (19 + tailCost) = (fuel + tailCost) + 19 by omega, addrRun, ht]
    simp [es, trace, tailCost, Option.map_map, Function.comp_def, List.append_assoc]
  · intro bad bs hret
    have afterAddr := (returns_prefix (fun fuel ↦ addrRun fuel bs)).mp hret
    have afterPrep : Returns M u m bs := (returns_prefix (n := RoutePrepare.ticks) (fun fuel ↦ by
      simpa only [List.length_replicate, tick_bits, List.nil_append] using
        setup.execute fuel m bs)).mp afterAddr
    exact failed bad m bs afterPrep

end PairSimulation.LeafFront

end VPVNP
end Computability
end OAI
