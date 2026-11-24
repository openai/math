import OAI.Computability.VPVNP.PairNodeChildScanCost
import OAI.Computability.VPVNP.PairNodeChildHeader
import OAI.Computability.VPVNP.PairTypedVertexJobs

/-!
# The complete child argument stage of a native parent visit

The header loads the actual list and the old layer's incidence directory. The
fixed child loop consumes precisely the placed old halves before entering the
local kernel routine. The same computation preserves the remaining tape,
stack cells, and packets already prepared for other pending sites.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildScan

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords DFS LocalHistory NetworkKernel
open TraversalRows
open scoped Fin.CommRing

variable {w p r k a g : ℕ} {M : Machine w p r k} {s : Sites a p} {reg : Fin 16 ↪ Fin r}
variable {source : ChildSlots.Names (2 ^ a) r k} {port : Fin (2 ^ a) → Fin k}
variable {ret : Fin p} {m : Memory w} {X : State a g}
variable {T : IncidenceDirectory w} {A : Arena} {older cap : ℕ} {header : Fin 17 → Fin p}

/-- Runtime layout data read from the chosen physical level. -/
def directory (a older cap : ℕ) (A : Arena) (T : IncidenceDirectory w) : ChildHeader.Fields w :=
  ⟨(older : Word w), ((cap + 2 : ℕ) : Word w), ((2 ^ a : ℕ) : Word w), (A.start : Word w),
    (A.stride : Word w), T.actualIn, T.width⟩

private theorem header_params {c d : Config w p r} {src count : ℕ}
    (h : ChildHeader.Ready reg (s.guard 0) c d (directory a older cap A T) src count) :
    Params reg a older cap A T d :=
  ⟨h.one, h.actualIn, h.width, h.olderBase, h.stride, h.degree, h.argumentStart, h.argumentStride⟩

/-- The ordered packets passed to the old-argument kernel reader are exactly
the child coordinates produced by the native scan of the same fiber. -/
theorem children_packets {R L : Type} [CommRing R] [Fintype L] {κ : L → R} {t : Term R X.network}
    (r : TermParsers κ t) (hp : ∀ u h, r.halfBits u h = packed X u h) (older cap : ℕ)
    (v : t.output.Site) (h : Placed t.place X.network.Half v) :
    (children X v (r.order.children v) h).map (Child.packet X older cap) =
      r.childPackets (childNode X older cap) v h := by
  simp only [children, List.map_ofFn, Function.comp_def, TermParsers.childPackets, Child.packet,
    Child.payload_ofHalf, hp]
  rfl

/-- The pointer at each old-argument position is the precise absolute node
stored in the selected traversal layer, in the parser's child order. -/
theorem children_words {R L : Type} [CommRing R] [Fintype L] {κ : L → R} {t : Term R X.network}
    (r : TermParsers κ t) (next : Order t.output.Site) (older cap : ℕ) (v : t.output.Site)
    (h : Placed t.place X.network.Half v) :
    (children X v (r.order.children v) h).map (fun x => (childNode X older cap x.site : Word w)) =
      childWords w cap older (stepLayer (siteOrder X) next r) (next.entries.symm v) := by
  obtain ⟨j, rfl⟩ := next.entries.surjective v
  rw [Equiv.symm_apply_apply]
  simp only [children, childWords, stepLayer, Child.ofHalf, childNode, sitePointers, List.map_ofFn,
    Function.comp_def]

private theorem header_entry (hh : ChildHeader.Linked M header reg (s.guard 0))
    (c : Config w p r) (hc : c.pc = header 0)
    (stored : (directory a older cap A T).Stored m (c.reg (reg 8)))
    (xs : List (Child X)) (src : ℕ)
    (row : Row m (c.reg (reg 7)).val src
      (xs.map fun x => (childNode X older cap x.site : Word w))) :
    ∃ d, ChildHeader.Ready reg (s.guard 0) c d (directory a older cap A T) src xs.length ∧
      Prefix M m c d [] (ChildHeader.events m (c.reg (reg 7)) (c.reg (reg 8))) := by
  obtain ⟨d, ready, prefixRun⟩ := ChildHeader.native hh m c hc _ stored src _ row
  refine ⟨d, by simpa using ready, fun fuel tail => ?_⟩
  simpa only [List.nil_append, (ChildHeader.cost m (c.reg (reg 7)) (c.reg (reg 8))).2.1] using
    prefixRun fuel tail

private theorem names_after_header {c d : Config w p r} (valid : source.Valid M c)
    (apart : source.Apart reg) {src count : ℕ}
    (h : ChildHeader.Ready reg (s.guard 0) c d (directory a older cap A T) src count) :
    source.Valid M d :=
  valid.transfer apart fun i hi => h.frame i fun j _ => hi j

/-- The whole stage consumes the old argument bits and executes the kernel
continuation on the suffix with the logical packets stored in scratch. -/
theorem native_stageWith (hh : ChildHeader.Linked M header reg (s.guard 0))
    (hl : LinkedWith M s reg source ret)
    (apart : source.Apart reg) (rep : T.ActualColumns X m)
    (xs : List (Child X)) (src : ℕ) (c : Config w p r) (names : source.Valid M c)
    (hc : c.pc = header 0)
    (stored : (directory a older cap A T).Stored m (c.reg (reg 8)))
    (row : Row m (c.reg (reg 7)).val src (xs.map fun x => (childNode X older cap x.site : Word w)))
    (strideFit : cap + 2 < 2 ^ w) (nodes : ∀ x ∈ xs, childNode X older cap x.site < 2 ^ w)
    (packets : ∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w) :
    let qs := xs.map (Child.packet X older cap)
    let es := ChildHeader.events m (c.reg (reg 7)) (c.reg (reg 8)) ++ events X T m src xs
    ∃ d, d.pc = ret ∧ d.persistent = c.persistent ∧ d.privateMem = storePackets A qs c.privateMem ∧
      (∀ endAddr, scratch endAddr d.privateMem = writePackets A qs (scratch endAddr c.privateMem)) ∧
      (∀ i, ChildHeader.Preserved reg i → i ∉ mutableRegs reg → d.reg i = c.reg i) ∧
      Prefix M m c d (qs.flatMap Packet.bits) es := by
  intro qs es
  obtain ⟨mid, init, pre⟩ := header_entry hh c hc stored xs src row
  have h := ready_of_row row strideFit nodes packets
  obtain ⟨d, hd, memory, state, frame, body⟩ := scanWith hl apart rep src xs h mid
    (names_after_header names apart init) init.pc init.source
    init.count (header_params init)
  have mem : d.privateMem = storePackets A qs c.privateMem :=
    memory.trans (congrArg _ init.privateMem)
  exact ⟨d, hd, state.trans init.persistent, mem, fun n => mem ▸ scratch_storePackets A qs _,
    fun i hi hmut => (frame i hmut).trans (init.frame i hi), pre.trans body⟩

theorem native_stage (hh : ChildHeader.Linked M header reg (s.guard 0))
    (hl : Linked M s reg port ret)
    (names : ∀ j, M.publicData (port j) = (j.val : Word w)) (rep : T.ActualColumns X m)
    (xs : List (Child X)) (src : ℕ) (c : Config w p r) (hc : c.pc = header 0)
    (stored : (directory a older cap A T).Stored m (c.reg (reg 8)))
    (row : Row m (c.reg (reg 7)).val src (xs.map fun x => (childNode X older cap x.site : Word w)))
    (strideFit : cap + 2 < 2 ^ w) (nodes : ∀ x ∈ xs, childNode X older cap x.site < 2 ^ w)
    (packets : ∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w) :
    let qs := xs.map (Child.packet X older cap)
    let es := ChildHeader.events m (c.reg (reg 7)) (c.reg (reg 8)) ++ events X T m src xs
    ∃ d, d.pc = ret ∧ d.persistent = c.persistent ∧ d.privateMem = storePackets A qs c.privateMem ∧
      (∀ endAddr, scratch endAddr d.privateMem = writePackets A qs (scratch endAddr c.privateMem)) ∧
      (∀ i, ChildHeader.Preserved reg i → i ∉ mutableRegs reg → d.reg i = c.reg i) ∧
      Prefix M m c d (qs.flatMap Packet.bits) es :=
  native_stageWith hh hl.toLinkedWith trivial rep xs src c names hc stored row
    strideFit nodes packets

/-- Rejection from the same full entry, including reads of the actual parent
header and directory. No accepting suffix exists for a short argument stream. -/
theorem reject_stageWith (hh : ChildHeader.Linked M header reg (s.guard 0))
    (hl : LinkedWith M s reg source ret)
    (apart : source.Apart reg) (rep : T.ActualColumns X m)
    (xs : List (Child X)) (src : ℕ) (c : Config w p r) (names : source.Valid M c)
    (hc : c.pc = header 0)
    (stored : (directory a older cap A T).Stored m (c.reg (reg 8)))
    (row : Row m (c.reg (reg 7)).val src (xs.map fun x => (childNode X older cap x.site : Word w)))
    (strideFit : cap + 2 < 2 ^ w) (nodes : ∀ x ∈ xs, childNode X older cap x.site < 2 ^ w)
    (packets : ∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w)
    (bs : List Bool) (short : bs.length < (xs.flatMap (Child.payload X)).length) :
    ¬ Returns M c m bs := by
  obtain ⟨mid, init, pre⟩ := header_entry hh c hc stored xs src row
  have h := ready_of_row row strideFit nodes packets
  exact fun accepted => reject_shortWith hl apart rep src xs h mid
    (names_after_header names apart init) init.pc init.source init.count
    (header_params init) bs short ((pre.returns bs).mp accepted)

theorem reject_stage (hh : ChildHeader.Linked M header reg (s.guard 0))
    (hl : Linked M s reg port ret)
    (names : ∀ j, M.publicData (port j) = (j.val : Word w)) (rep : T.ActualColumns X m)
    (xs : List (Child X)) (src : ℕ) (c : Config w p r) (hc : c.pc = header 0)
    (stored : (directory a older cap A T).Stored m (c.reg (reg 8)))
    (row : Row m (c.reg (reg 7)).val src (xs.map fun x => (childNode X older cap x.site : Word w)))
    (strideFit : cap + 2 < 2 ^ w) (nodes : ∀ x ∈ xs, childNode X older cap x.site < 2 ^ w)
    (packets : ∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w)
    (bs : List Bool) (short : bs.length < (xs.flatMap (Child.payload X)).length) :
    ¬ Returns M c m bs :=
  reject_stageWith hh hl.toLinkedWith trivial rep xs src c names hc stored row
    strideFit nodes packets bs short

/-- All native stores remain above the protected stack boundary, including
when the remaining stack contains pending siblings. -/
theorem storePackets_below (A : Arena) (qs : List Packet) (priv : Word w → Word w)
    (endAddr : ℕ) (fits : ∀ q ∈ qs, q.Fits A w endAddr) (x : Word w) (hx : x.val < endAddr) :
    storePackets A qs priv x = priv x := by
  induction qs generalizing priv with
  | nil => rfl
  | cons q qs ih =>
    have hf := fits q List.mem_cons_self
    apply (ih _ (fun z hz => fits z (List.mem_cons_of_mem _ hz))).trans
    exact PrivateFields.storeBits_outside _ _ _ x hf.2.2 (Or.inl (hx.trans_le hf.1))

end PairSimulation.NodeArguments.ChildScan

end VPVNP
end Computability
end OAI
