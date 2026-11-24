import OAI.Computability.VPVNP.PairNodeChildLoop
import OAI.Computability.VPVNP.PairNodeChildPackets
import OAI.Computability.VPVNP.PairNodeChildAddress

/-!
# Scanning a parent's actual descriptor children

The same guard, address calculation and slot routine run once per child,
independent of the row length. The pointer comes from external memory and
determines both the child's old incidence ordinal and its private buffer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildScan

open BurstRAM BurstRAM.PrivateRAM Compression LocalHistory CompressorRecords DFS
open scoped Fin.CommRing

variable {w p r k a g : ℕ}

/-- Program counters shared across iterations of a parent’s child scan, together with the
setup, width lookup and guess counters for each directed slot. -/
structure Sites (a p : ℕ) where
  /-- Locations of the three child-count instructions that either exit the scan or decrement
  the count and enter the address block. -/
  guard : Fin 3 → Fin p
  /-- Locations of the seven instructions that fetch the child descriptor pointer, advance the
  source and calculate the first port and private argument address. -/
  address : Fin 7 → Fin p
  /-- Instruction locations for processing each of the 2^a outgoing and 2^a incoming half-wire
  fields once the child address is known. -/
  slots : ChildSlots.Sites (2 ^ a) p

/-- The entire body links back to the same guard after all slots of one child. -/
structure LinkedWith (M : Machine w p r k) (s : Sites a p) (reg : Fin 16 ↪ Fin r)
    (source : ChildSlots.Names (2 ^ a) r k) (ret : Fin p) : Prop where
  guard : GuardLinked M s.guard reg (s.address 0) ret
  address : ChildAddress.Linked M s.address reg
    (ChildSlots.first s.slots (s.guard 0) (ChildSlots.slots (2 ^ a)))
  slots : ChildSlots.LinkedWith M s.slots (slotRegs reg) source (s.guard 0)
    (ChildSlots.slots (2 ^ a))

/-- The linkage interface for public slot-ordinal operands. -/
structure Linked (M : Machine w p r k) (s : Sites a p) (reg : Fin 16 ↪ Fin r)
    (port : Fin (2 ^ a) → Fin k) (ret : Fin p) : Prop where
  guard : GuardLinked M s.guard reg (s.address 0) ret
  address : ChildAddress.Linked M s.address reg
    (ChildSlots.first s.slots (s.guard 0) (ChildSlots.slots (2 ^ a)))
  slots : ChildSlots.Linked M s.slots (slotRegs reg) port (s.guard 0) (ChildSlots.slots (2 ^ a))

theorem Linked.toLinkedWith {M : Machine w p r k} {s : Sites a p} {reg : Fin 16 ↪ Fin r}
    {port : Fin (2 ^ a) → Fin k} {ret : Fin p} (h : Linked M s reg port ret) :
    LinkedWith M s reg (.operand port) ret := ⟨h.guard, h.address, h.slots⟩

/-- Register contents common to all children of the parent. -/
structure Params (reg : Fin 16 ↪ Fin r) (a older cap : ℕ) (A : Arena) (T : IncidenceDirectory w)
    (c : Config w p r) : Prop where
  one : c.reg (reg 3) = 1
  incoming : c.reg (reg 6) = T.actualIn
  widths : c.reg (reg 7) = T.width
  olderBase : c.reg (reg 11) = (older : Word w)
  rowStride : c.reg (reg 12) = ((cap + 2 : ℕ) : Word w)
  degree : c.reg (reg 13) = ((2 ^ a : ℕ) : Word w)
  start : c.reg (reg 14) = (A.start : Word w)
  stride : c.reg (reg 15) = (A.stride : Word w)

/-- Only the slot temporaries, child address operands and loop counters may change. -/
def mutableRegs (reg : Fin 16 ↪ Fin r) : Finset (Fin r) :=
  {reg 0, reg 1, reg 2, reg 4, reg 5, reg 8, reg 9, reg 10}

/-- Register preservation across a child scan outside its eight mutable registers. In
particular the common incidence, row-layout and argument-arena parameters carry into the
next iteration. -/
def Frame (reg : Fin 16 ↪ Fin r) (c d : Config w p r) : Prop :=
  ∀ i, i ∉ mutableRegs reg → d.reg i = c.reg i

private theorem Params.transfer {reg : Fin 16 ↪ Fin r} {a older cap : ℕ} {A : Arena}
    {T : IncidenceDirectory w} {c d : Config w p r} (h : Params reg a older cap A T c)
    (frame : Frame reg c d) : Params reg a older cap A T d := by
  constructor <;> first
    | exact (frame _ (by simp [mutableRegs])).trans h.one
    | exact (frame _ (by simp [mutableRegs])).trans h.incoming
    | exact (frame _ (by simp [mutableRegs])).trans h.widths
    | exact (frame _ (by simp [mutableRegs])).trans h.olderBase
    | exact (frame _ (by simp [mutableRegs])).trans h.rowStride
    | exact (frame _ (by simp [mutableRegs])).trans h.degree
    | exact (frame _ (by simp [mutableRegs])).trans h.start
    | exact (frame _ (by simp [mutableRegs])).trans h.stride

variable {M : Machine w p r k} {s : Sites a p} {reg : Fin 16 ↪ Fin r}
variable {source : ChildSlots.Names (2 ^ a) r k} {port : Fin (2 ^ a) → Fin k}
variable {ret : Fin p} {m : Memory w}
variable {X : State a g} {T : IncidenceDirectory w} {A : Arena} {older cap : ℕ}

/-- The source row, all old node pointers, and all destination fields fit in the word arena. -/
structure Ready (m : Memory w) (X : State a g) (A : Arena) (older cap src : ℕ)
    (xs : List (Child X)) : Prop where
  endFit : src + xs.length < 2 ^ w
  strideFit : cap + 2 < 2 ^ w
  cells : ∀ i : Fin xs.length, m (src + i.val) = (childNode X older cap xs[i].site : Word w)
  nodes : ∀ x ∈ xs, childNode X older cap x.site < 2 ^ w
  packets : ∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w

private theorem Ready.tail {x : Child X} {xs : List (Child X)} {src : ℕ}
    (h : Ready m X A older cap src (x :: xs)) : Ready m X A older cap (src + 1) xs := by
  refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1] using h.endFit, h.strideFit, fun i => ?_,
    fun v hv => h.nodes v (List.mem_cons_of_mem _ hv),
    fun v hv => h.packets v (List.mem_cons_of_mem _ hv)⟩
  simpa only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1]
    using h.cells i.succ

/-- Specialize the bounds to the actual DFS row read by the parent. -/
theorem ready_of_row {xs : List (Child X)} {node src : ℕ}
    (hr : Row m node src (xs.map fun x => (childNode X older cap x.site : Word w)))
    (strideFit : cap + 2 < 2 ^ w) (nodes : ∀ x ∈ xs, childNode X older cap x.site < 2 ^ w)
    (packets : ∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w) :
    Ready m X A older cap src xs := by
  refine ⟨by simpa using hr.2.1, strideFit, fun i => ?_, nodes, packets⟩
  simpa using hr.2.2.2.2 ⟨i.val, by simp⟩

/-- Trace before the first slot of a live child. Three guard ticks precede the external read at
src and the six ticks of address arithmetic. -/
def setupEvents (m : Memory w) (src : ℕ) : List (Event w) :=
  [.tick, .tick, .tick] ++ ChildAddress.events m (src : Word w)

/-- Execute the guard and actual directory-pointer calculation for one live child. -/
private theorem enter {x : Child X} {xs : List (Child X)} {src : ℕ}
    (hl : LinkedWith M s reg source ret)
    (h : Ready m X A older cap src (x :: xs)) (c : Config w p r) (hc : c.pc = s.guard 0)
    (hp : c.reg (reg 9) = (src : Word w)) (hn : c.reg (reg 10) = ((xs.length + 1 : ℕ) : Word w))
    (par : Params reg a older cap A T c) :
    let node := childNode X older cap x.site
    ∃ d, d.pc = ChildSlots.first s.slots (s.guard 0) (ChildSlots.slots (2 ^ a)) ∧
      d.reg (reg 2) = (A.base node : Word w) ∧
      d.reg (reg 8) = IncidenceDirectory.actualPort X (x.site, 0) ∧
      d.reg (reg 9) = ((src + 1 : ℕ) : Word w) ∧ d.reg (reg 10) = (xs.length : Word w) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧ Frame reg c d ∧
      Prefix M m c d [] (setupEvents m src) := by
  intro node
  have srcFit : src < 2 ^ w := (Nat.le_add_right _ _).trans_lt h.endFit
  have countFit : xs.length + 1 < 2 ^ w := (Nat.le_add_left _ _).trans_lt h.endFit
  obtain ⟨c₁, pc₁, mem₁, state₁, n₁, keep₁, pre₁⟩ := guard_cons hl.guard c hc xs.length
    countFit hn par.one m
  have frame₁ : Frame reg c c₁ := by
    intro i hi
    simp only [mutableRegs, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact keep₁ i hi.1 hi.2.2.2.2.2.2.2
  have par₁ := par.transfer frame₁
  have ptr₁ : c₁.reg (reg 9) = (src : Word w) :=
    (keep₁ _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))).trans hp
  obtain ⟨d, pc₂, dst, first, ptr₂, keep₂, mem₂, state₂, pre₂⟩ := ChildAddress.native hl.address m
    c₁ pc₁ par₁.one
  have stored : m (c₁.reg (reg 9)).val = (node : Word w) := by
    rw [ptr₁, Fin.val_natCast, Nat.mod_eq_of_lt srcFit]
    simpa [node] using h.cells ⟨0, Nat.zero_lt_succ _⟩
  have nodeFit := h.nodes x List.mem_cons_self
  have olderFit : older < 2 ^ w := (Nat.le_add_right older _).trans_lt nodeFit
  have numeric : (node : Word w).val = (older : Word w).val +
      ((cap + 2 : ℕ) : Word w).val * ((siteOrder X).entries.symm x.site).val := by
    rw [Fin.val_natCast, Nat.mod_eq_of_lt nodeFit, Fin.val_natCast, Nat.mod_eq_of_lt olderFit,
      Fin.val_natCast, Nat.mod_eq_of_lt h.strideFit]
    rfl
  have rowPos : 0 < ((cap + 2 : ℕ) : Word w).val := by
    rw [Fin.val_natCast, Nat.mod_eq_of_lt h.strideFit]
    omega
  refine ⟨d, pc₂, ?_, ?_, ?_, (keep₂ _ (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
    (reg.injective.ne (by decide))).trans n₁, mem₂.trans mem₁, state₂.trans state₁, ?_, ?_⟩
  · rw [dst, stored, par₁.start, par₁.stride]
    simp only [Arena.base, Nat.cast_add, Nat.cast_mul]
  · rw [first, stored, par₁.olderBase, par₁.rowStride, par₁.degree]
    exact ChildAddress.firstPort_eq X x.site _ _ _ numeric rowPos
  · rw [ptr₂, ptr₁, Nat.cast_add, Nat.cast_one]
  · intro i hi
    have notMem := hi
    simp only [mutableRegs, Finset.mem_insert, Finset.mem_singleton, not_or] at notMem
    exact (keep₂ i notMem.2.2.1 notMem.2.2.2.2.2.1 notMem.2.2.2.2.2.2.1).trans (frame₁ i hi)
  · have h₂ : Prefix M m c₁ d [] (ChildAddress.events m (src : Word w)) := by
      intro fuel bs
      simpa only [ptr₁, List.nil_append, ChildAddress.events, List.length_cons, List.length_nil]
        using pre₂ fuel bs
    exact pre₁.trans h₂

private theorem names_frame {c d : Config w p r} (valid : source.Valid M c)
    (apart : source.Apart reg) (frame : Frame reg c d) : source.Valid M d :=
  valid.transfer apart fun i hi => frame i (by
    simp only [mutableRegs, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hi 0, hi 1, hi 2, hi 4, hi 5, hi 8, hi 9, hi 10⟩)

private theorem slots_apart (h : source.Apart reg) : source.Apart (slotRegs reg) := by
  cases source with
  | operand => trivial
  | bank b => exact fun i j => h i (j.castAdd 7)

/-- One complete child, with its outgoing slots followed by its incoming slots. -/
noncomputable def childEvents (X : State a g) (T : IncidenceDirectory w) (m : Memory w)
    (src : ℕ) (x : Child X) : List (Event w) :=
  setupEvents m src ++ ChildSlots.events X x.site T m x.data (ChildSlots.slots (2 ^ a))

private theorem step {x : Child X} {xs : List (Child X)} {src : ℕ}
    (hl : LinkedWith M s reg source ret)
    (apart : source.Apart reg) (rep : T.ActualColumns X m)
    (h : Ready m X A older cap src (x :: xs)) (c : Config w p r) (names : source.Valid M c)
    (hc : c.pc = s.guard 0)
    (hp : c.reg (reg 9) = (src : Word w)) (hn : c.reg (reg 10) = ((xs.length + 1 : ℕ) : Word w))
    (par : Params reg a older cap A T c) :
    ∃ d, d.pc = s.guard 0 ∧ d.reg (reg 9) = ((src + 1 : ℕ) : Word w) ∧
      d.reg (reg 10) = (xs.length : Word w) ∧
      d.privateMem = PrivateFields.storeBits (A.base (childNode X older cap x.site))
        (x.payload X) c.privateMem ∧ d.persistent = c.persistent ∧ Frame reg c d ∧
      Prefix M m c d (x.payload X) (childEvents X T m src x) := by
  obtain ⟨d, hd, dst, first, ptr, count, mem, state, keep, pre⟩ := enter hl h c hc hp hn par
  have par' := par.transfer keep
  have fit := h.packets x List.mem_cons_self
  rw [Child.payload_length] at fit
  obtain ⟨out, ho, memory, persistent, _, frame, run⟩ := ChildSlots.scanWith _ hl.slots
    (slots_apart apart) rep x.data _ fit d (names_frame names apart keep) hd dst par'.one
    par'.incoming par'.widths first
  have keeps (i : Fin 16) (h₀ : i ≠ 0) (h₁ : i ≠ 1) (h₂ : i ≠ 2) (h₄ : i ≠ 4) (h₅ : i ≠ 5) :
      out.reg (reg i) = d.reg (reg i) :=
    frame _ (reg.injective.ne h₀) (reg.injective.ne h₁) (reg.injective.ne h₂)
      (reg.injective.ne h₄) (reg.injective.ne h₅)
  refine ⟨out, ho, (keeps 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ptr,
    (keeps 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans count,
    memory.trans (congrArg _ mem), persistent.trans state, ?_, pre.trans run⟩
  intro i hi
  have hnot := hi
  simp only [mutableRegs, Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
  exact (frame i hnot.1 hnot.2.1 hnot.2.2.1 hnot.2.2.2.1 hnot.2.2.2.2.1).trans (keep i hi)

/-- The chosen local instruction trace includes one empty-row exit. -/
noncomputable def events (X : State a g) (T : IncidenceDirectory w) (m : Memory w) :
    ℕ → List (Child X) → List (Event w)
  | _, [] => [.tick, .tick]
  | src, x :: xs => childEvents X T m src x ++ events X T m (src + 1) xs

/-- Execute the full native row, preserving the continuation's entire choice
suffix and preparing precisely the logical ordered list of argument packets. -/
theorem scanWith (hl : LinkedWith M s reg source ret) (apart : source.Apart reg)
    (rep : T.ActualColumns X m) (src : ℕ) (xs : List (Child X)) (h : Ready m X A older cap src xs)
    (c : Config w p r) (names : source.Valid M c)
    (hc : c.pc = s.guard 0) (hp : c.reg (reg 9) = (src : Word w))
    (hn : c.reg (reg 10) = (xs.length : Word w)) (par : Params reg a older cap A T c) :
    let qs := xs.map (Child.packet X older cap)
    ∃ d, d.pc = ret ∧ d.privateMem = storePackets A qs c.privateMem ∧ d.persistent = c.persistent ∧
      Frame reg c d ∧ Prefix M m c d (qs.flatMap Packet.bits) (events X T m src xs) := by
  induction xs generalizing c src with
  | nil =>
    obtain ⟨d, hd, mem, state, keep, pre⟩ := guard_empty hl.guard c hc (by simpa using hn) m
    exact ⟨d, hd, mem, state, fun i hi => keep i (fun eqn => hi (by simp [mutableRegs, eqn])), pre⟩
  | cons x xs ih =>
    obtain ⟨mid, hm, ptr, count, mem, state, keep, pre⟩ := step hl apart rep h c names hc hp hn par
    obtain ⟨d, hd, mem', state', keep', more⟩ := ih (src + 1) h.tail mid
      (names_frame names apart keep) hm ptr count (par.transfer keep)
    refine ⟨d, hd, mem'.trans (congrArg _ mem), state'.trans state, fun i hi =>
      (keep' i hi).trans (keep i hi), pre.trans more⟩

theorem scan (hl : Linked M s reg port ret) (names : ∀ j, M.publicData (port j) = (j.val : Word w))
    (rep : T.ActualColumns X m) (src : ℕ) (xs : List (Child X)) (h : Ready m X A older cap src xs)
    (c : Config w p r) (hc : c.pc = s.guard 0) (hp : c.reg (reg 9) = (src : Word w))
    (hn : c.reg (reg 10) = (xs.length : Word w)) (par : Params reg a older cap A T c) :
    let qs := xs.map (Child.packet X older cap)
    ∃ d, d.pc = ret ∧ d.privateMem = storePackets A qs c.privateMem ∧ d.persistent = c.persistent ∧
      Frame reg c d ∧ Prefix M m c d (qs.flatMap Packet.bits) (events X T m src xs) :=
  scanWith hl.toLinkedWith trivial rep src xs h c names hc hp hn par

private theorem Ready.replace {x z : Child X} {xs : List (Child X)} {src : ℕ}
    (h : Ready m X A older cap src (x :: xs)) (hz : z.site = x.site) :
    Ready m X A older cap src (z :: xs) := by
  refine ⟨h.endFit, h.strideFit, fun i => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · cases i using Fin.cases with
    | zero => simpa [hz] using h.cells ⟨0, Nat.zero_lt_succ _⟩
    | succ j => exact h.cells j.succ
  · rcases List.mem_cons.mp hj with rfl | hm
    · simpa [hz] using h.nodes x List.mem_cons_self
    · exact h.nodes j (List.mem_cons_of_mem _ hm)
  · rcases List.mem_cons.mp hj with rfl | hm
    · simpa only [Child.payload_length, hz] using h.packets x List.mem_cons_self
    · exact h.packets j (List.mem_cons_of_mem _ hm)

/-- An incomplete argument tape cannot return. This includes a short field
in a later child after all earlier guessed packets have been written. -/
theorem reject_shortWith (hl : LinkedWith M s reg source ret)
    (apart : source.Apart reg) (rep : T.ActualColumns X m)
    (src : ℕ) (xs : List (Child X)) (h : Ready m X A older cap src xs)
    (c : Config w p r) (names : source.Valid M c)
    (hc : c.pc = s.guard 0) (hp : c.reg (reg 9) = (src : Word w))
    (hn : c.reg (reg 10) = (xs.length : Word w)) (par : Params reg a older cap A T c)
    (bs : List Bool) (short : bs.length < (xs.flatMap (Child.payload X)).length) :
    ¬ Returns M c m bs := by
  induction xs generalizing c src bs with
  | nil => simp at short
  | cons x xs ih =>
    let n := (x.payload X).length
    have hl' : bs.length < n + (xs.flatMap (Child.payload X)).length := by simpa [n] using short
    by_cases full : n ≤ bs.length
    · obtain ⟨v, hv, tape⟩ := choose_payload X x.site bs ((Child.payload_length X x) ▸ full)
      obtain ⟨mid, hm, ptr, count, _, _, keep, run⟩ :=
        step hl apart rep (h.replace hv) c names hc hp hn par
      have len : (v.payload X).length = n := by simp [n, Child.payload_length, hv]
      have later := ih (src + 1) h.tail mid (names_frame names apart keep) hm ptr count
        (par.transfer keep) (bs.drop n) (by simp only [List.length_drop]; omega)
      intro accepted
      rw [← tape] at accepted
      exact later (len ▸ (run.returns _).mp accepted)
    · obtain ⟨mid, hm, dst, first, _, _, _, _, keep, run⟩ := enter hl h c hc hp hn par
      have par' := par.transfer keep
      have fit := h.packets x List.mem_cons_self
      rw [Child.payload_length] at fit
      have short' := (Nat.lt_of_not_ge full).trans_eq (Child.payload_length X x)
      exact fun accept => ChildSlots.reject_shortWith _ hl.slots (slots_apart apart) rep _ fit
        mid (names_frame names apart keep) hm dst par'.one par'.incoming par'.widths first
        bs short' ((run.returns bs).mp accept)

theorem reject_short (hl : Linked M s reg port ret)
    (names : ∀ j, M.publicData (port j) = (j.val : Word w)) (rep : T.ActualColumns X m)
    (src : ℕ) (xs : List (Child X)) (h : Ready m X A older cap src xs)
    (c : Config w p r) (hc : c.pc = s.guard 0) (hp : c.reg (reg 9) = (src : Word w))
    (hn : c.reg (reg 10) = (xs.length : Word w)) (par : Params reg a older cap A T c)
    (bs : List Bool) (short : bs.length < (xs.flatMap (Child.payload X)).length) :
    ¬ Returns M c m bs :=
  reject_shortWith hl.toLinkedWith trivial rep src xs h c names hc hp hn par bs short

end PairSimulation.NodeArguments.ChildScan

end VPVNP
end Computability
end OAI
