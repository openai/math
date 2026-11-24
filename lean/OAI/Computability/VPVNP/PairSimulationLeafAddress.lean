import OAI.Computability.VPVNP.LiveAuxiliaryHeaderPreparation
import OAI.Computability.VPVNP.PrimedCounterData
import OAI.Computability.VPVNP.PrimedCounterGuessWord
import OAI.Computability.VPVNP.PairSimulationLeafCoordinates

/-!
# The native leaf address and auxiliary header reader

The descriptor address on the depth-first stack identifies a row in the initial
cursor layout. The reader divides out the row stride, recovers the cursor and
the two blocks of address bits, and reads the complete auxiliary header word.
Beyond the prepared shadow region it supplies zero without probing memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafAddress

open BurstRAM PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Registers for dividing a DFS node address into its row index, cursor and site, then loading
the site's auxiliary header word. -/
inductive Reg where
  | node | tmp | idx | low | site | cursor | addr | zero | header
  deriving DecidableEq

instance : Fintype Reg :=
  ⟨{.node,.tmp,.idx,.low,.site,.cursor,.addr,.zero,.header}, fun i => by cases i <;> decide⟩

/-- The row base and stride, two coordinate radices, and shadow base and span consumed by the
leaf address decoder. -/
inductive Field where
  | base | stride | radixB | radixL | shadow | span
  deriving DecidableEq

instance : Fintype Field :=
  ⟨{.base,.stride,.radixB,.radixL,.shadow,.span}, fun i => by cases i <;> decide⟩

/-- Decode the two coordinates with the arithmetic of the host's word width. -/
def decode (node base stride radixB radixL : Word w) : Word w × Word w :=
  let idx := BinaryOp.div.eval (node-base) stride
  let high := BinaryOp.mod.eval idx radixL
  let cb := BinaryOp.div.eval idx radixL
  let low := BinaryOp.mod.eval cb radixB
  let cursor := BinaryOp.div.eval cb radixB
  (cursor, low+high*radixB)

theorem decode_packed {w : ℕ} (node base stride radixB radixL : Word w)
    {cursor low high : ℕ}
    (hnode : base.val + stride.val * ((cursor * radixB.val + low) * radixL.val + high) = node.val)
    (hs : 0 < stride.val) (hb : low < radixB.val) (hl : high < radixL.val)
    (hsite : low + high * radixB.val < 2^w) :
    (decode node base stride radixB radixL).1.val = cursor ∧
      (decode node base stride radixB radixL).2.val = low + high * radixB.val := by
  have divVal (x y : Word w) : (BinaryOp.div.eval x y).val = x.val / y.val :=
    Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)
  have modVal (x y : Word w) : (BinaryOp.mod.eval x y).val = x.val % y.val :=
    Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)
  have divPacked (q : ℕ) {d t : ℕ} (ht : t < d) : (q * d + t) / d = q := by
    rw [Nat.mul_comm q, Nat.mul_add_div ((Nat.zero_le t).trans_lt ht), Nat.div_eq_of_lt ht, Nat.add_zero]
  have hbase : base ≤ node := show base.val ≤ node.val by omega
  have hidx : (node - base).val / stride.val = (cursor * radixB.val + low) * radixL.val + high := by
    rw [Fin.sub_val_of_le hbase, ← hnode, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hs]
  simp only [decode, divVal, modVal, hidx, divPacked _ hl, divPacked _ hb,
    Nat.mul_add_mod_of_lt hl, Nat.mul_add_mod_of_lt hb, Fin.val_add, Fin.val_mul,
    Nat.mod_eq_of_lt (show high * radixB.val < 2^w by omega), Nat.mod_eq_of_lt hsite, and_self]

section Geometry

open CursorNetwork CursorRouting Compression LocalHistory TraversalRows

/-- The native word decoder recovers both coordinates of the auxiliary processor
from the physical address of its initial traversal row. -/
theorem decode_leaf_row {W b l a p : ℕ} {S : Type} [Fintype S]
    (hD : 1 < b + l) (hd : 2 + p = 2^a) (bits : S → ℕ) (cap : ℕ) (v : Position (b+l))
    (node base stride radixB radixL : Word W) (hwidth : b+l ≤ W)
    (hs : stride.val = cap+2) (hb : radixB.val = 2^b) (hl : radixL.val = 2^l)
    (hnode : node.val = (sitePointers cap base.val
      (siteOrder (cursorState (cursorCoordinateLabels b l) hD hd bits))
      (lanePositions (cursorCoordinateLabels b l) v)).1) :
    (decode node base stride radixB radixL).1.val = v.1.val ∧
      (decode node base stride radixB radixL).2.val = v.2.val := by
  let u := lanePositions (cursorCoordinateLabels b l) v
  let low := (bitWordFinEquiv b u.1.2).val
  let high := (bitWordFinEquiv l u.2).val
  obtain ⟨hrow, hsite⟩ := LeafCoordinates.leaf_row hD hd bits base.val cap v
  have ha : base.val + stride.val * ((v.1.val * radixB.val + low) * radixL.val + high) = node.val := by
    rw [hnode, hs, hb, hl]
    exact hrow.symm
  have hv : low + high * radixB.val = v.2.val := by
    rw [hb, Nat.mul_comm, Nat.add_comm]
    exact hsite.symm
  have pair := decode_packed node base stride radixB radixL ha (by omega)
    (hb ▸ (bitWordFinEquiv b u.1.2).isLt) (hl ▸ (bitWordFinEquiv l u.2).isLt)
    (hv ▸ v.2.isLt.trans_le (Nat.pow_le_pow_right (by decide) hwidth))
  exact ⟨pair.1, pair.2.trans hv⟩

end Geometry

/-- Both exits receive the cursor, site, and header. The node register is read-only. -/
def instruction (pc : Fin 20 → Fin p) (reg : Reg ↪ Fin r) (pub : Field → Fin k)
    (launch transit : Fin p) : Fin 20 → Instr w p r k :=
  ![.publicWord (reg .tmp) (pub .base) (pc 1),
    .binary .sub (reg .idx) (reg .node) (reg .tmp) (pc 2),
    .publicWord (reg .tmp) (pub .stride) (pc 3),
    .binary .div (reg .idx) (reg .idx) (reg .tmp) (pc 4),
    .publicWord (reg .tmp) (pub .radixL) (pc 5),
    .binary .mod (reg .site) (reg .idx) (reg .tmp) (pc 6),
    .binary .div (reg .idx) (reg .idx) (reg .tmp) (pc 7),
    .publicWord (reg .tmp) (pub .radixB) (pc 8),
    .binary .mod (reg .low) (reg .idx) (reg .tmp) (pc 9),
    .binary .div (reg .cursor) (reg .idx) (reg .tmp) (pc 10),
    .binary .mul (reg .site) (reg .site) (reg .tmp) (pc 11),
    .binary .add (reg .site) (reg .low) (reg .site) (pc 12),
    .publicWord (reg .tmp) (pub .shadow) (pc 13),
    .binary .add (reg .addr) (reg .tmp) (reg .site) (pc 14),
    .publicWord (reg .tmp) (pub .span) (pc 15),
    .constant (reg .zero) 0 (pc 16),
    .jumpLt (reg .site) (reg .tmp) (pc 17) (pc 18),
    .readExternal (reg .header) (reg .addr) (pc 19),
    .constant (reg .header) 0 (pc 19),
    .jumpEq (reg .cursor) (reg .zero) launch transit]

theorem resize_instruction (pc : Fin 20 → Fin p) (reg : Reg ↪ Fin r) (pub : Field → Fin k)
    (launch transit : Fin p) (i : Fin 20) :
    (instruction (w := 1) pc reg pub launch transit i).resize w =
      instruction pc reg pub launch transit i := by fin_cases i <;> rfl

/-- The machine contains all 20 decoder instructions at the assigned labels, with the specified
register placement, operands, and launch and transit continuations. -/
def Linked (M : Machine w p r k) (pc : Fin 20 → Fin p) (reg : Reg ↪ Fin r) (pub : Field → Fin k)
    (launch transit : Fin p) : Prop := ∀ i, M.code (pc i) = instruction pc reg pub launch transit i

/-- Every register except the eight scratch slots is preserved, including the DFS node. -/
def Preserved (reg : Reg ↪ Fin r) (a : Fin r) : Prop := ∀ i, i ≠ .node → a ≠ reg i

theorem preserved_node (reg : Reg ↪ Fin r) : Preserved reg (reg .node) :=
  fun _ h => reg.injective.ne h.symm

variable {M : Machine w p r k} {pc : Fin 20 → Fin p} {reg : Reg ↪ Fin r} {pub : Field → Fin k}
  {launch transit : Fin p}

private theorem step_at (hl : Linked M pc reg pub launch transit) (i : Fin 20) {c : Config w p r}
    (hc : c.pc = pc i) :
    M.program.step c = (instruction pc reg pub launch transit i).run M.publicData c := by
  change (M.code c.pc).run _ _ = _
  rw [hc,hl]

/-- The address arithmetic, including the bounds-test operands, occupies the first sixteen slots. -/
private theorem head_native (hl : Linked M pc reg pub launch transit)
    (c : Config w p r) (entry : c.pc = pc 0) :
    let f := M.publicData ∘ pub
    let coord := decode (c.reg (reg .node)) (f .base) (f .stride) (f .radixB) (f .radixL)
    ∃ q, Prefix M c (List.replicate 16 .tick) q ∧ q.pc = pc 16 ∧
      q.reg (reg .cursor) = coord.1 ∧ q.reg (reg .site) = coord.2 ∧
      q.reg (reg .addr) = f .shadow + coord.2 ∧ q.reg (reg .tmp) = f .span ∧ q.reg (reg .zero) = 0 ∧
      (∀ a, Preserved reg a → q.reg a = c.reg a) ∧ q.privateMem = c.privateMem ∧ q.persistent = c.persistent := by
  dsimp only
  refine ⟨_, .tick (step_at hl 0 entry) (.tick (step_at hl 1 rfl) (.tick (step_at hl 2 rfl)
    (.tick (step_at hl 3 rfl) (.tick (step_at hl 4 rfl) (.tick (step_at hl 5 rfl)
    (.tick (step_at hl 6 rfl) (.tick (step_at hl 7 rfl) (.tick (step_at hl 8 rfl)
    (.tick (step_at hl 9 rfl) (.tick (step_at hl 10 rfl) (.tick (step_at hl 11 rfl)
    (.tick (step_at hl 12 rfl) (.tick (step_at hl 13 rfl) (.tick (step_at hl 14 rfl)
    (.tick (step_at hl 15 rfl) (.nil _)))))))))))))))), rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  all_goals first | (solve | simp [Config.put, decode, Function.update_apply, reg.injective.eq_iff, BinaryOp.eval]) | skip
  intro a ha
  simp [Config.put, Function.update_of_ne (ha .tmp (by decide)),
    Function.update_of_ne (ha .idx (by decide)), Function.update_of_ne (ha .site (by decide)),
    Function.update_of_ne (ha .low (by decide)), Function.update_of_ne (ha .cursor (by decide)),
    Function.update_of_ne (ha .addr (by decide)), Function.update_of_ne (ha .zero (by decide))]

/-- The sole possible probe is issued at the translated physical address. -/
def events (m : Memory w) (shadow span site : Word w) : List (Event w) :=
  let a := shadow+site
  List.replicate 17 .tick ++ [if site < span then .read a (m a.val) else .tick, .tick]

/-- Read the site's word at the shadow base plus its index. Return zero when the index reaches
or exceeds the prepared span. -/
def header (m : Memory w) (shadow span site : Word w) : Word w :=
  if site < span then m (shadow+site).val else 0

theorem cost (m : Memory w) (shadow span site : Word w) :
    (events m shadow span site).length = 19 ∧
      countProbes (events m shadow span site) = (decide (site < span)).toNat ∧
      choiceBits (events m shadow span site) = [] := by
  by_cases h : site < span <;> simp only [events, h, decide_true, decide_false, ↓reduceIte] <;>
    exact ⟨rfl,rfl,rfl⟩

/-- Every continuation receives the original bit suffix and external memory, the decoded
coordinates and the complete word, after the nineteen indicated instructions. -/
theorem native (hl : Linked M pc reg pub launch transit) (m : Memory w)
    (c : Config w p r) (entry : c.pc = pc 0) :
    let f := M.publicData ∘ pub
    let coord := decode (c.reg (reg .node)) (f .base) (f .stride) (f .radixB) (f .radixL)
    ∃ d, d.pc = (if coord.1 = 0 then launch else transit) ∧
      d.reg (reg .cursor) = coord.1 ∧ d.reg (reg .site) = coord.2 ∧
      d.reg (reg .header) = header m (f .shadow) (f .span) coord.2 ∧
      (∀ a, Preserved reg a → d.reg a = c.reg a) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      ∀ fuel bs, execute M.program (fuel + 19) c m bs =
        (execute M.program fuel d m bs).map fun t => ⟨events m (f .shadow) (f .span) coord.2 ++ t.events,t.result⟩ := by
  intro f coord
  obtain ⟨q, pre, hpc, hcur, hsite, haddr, hspan, hzero, frame, mem, per⟩ := head_native hl c entry
  let atLoad := {q with pc := if coord.2 < f .span then pc 17 else pc 18}
  let value := header m (f .shadow) (f .span) coord.2
  let loaded := atLoad.put (pc 19) (reg .header) value
  let d := {loaded with pc := if coord.1 = 0 then launch else transit}
  have bounds : M.program.step q = .localStep atLoad := by
    rw [step_at hl 16 hpc]
    change CallAction.localStep {q with pc := if q.reg (reg .site) < q.reg (reg .tmp) then _ else _} = _
    rw [hsite,hspan]
  have dispatch : M.program.step loaded = .localStep d := by
    rw [step_at hl 19 rfl]
    change CallAction.localStep {loaded with pc := if loaded.reg (reg .cursor) = loaded.reg (reg .zero) then _ else _} = _
    simp [loaded, atLoad, d, Config.put, hcur, hzero, coord, f]
  refine ⟨d,rfl,?_,?_,by simp [d,loaded,value],?_,mem,per,?_⟩
  · simpa [d,loaded,atLoad,Config.put,coord,f] using hcur
  · simpa [d,loaded,atLoad,Config.put,coord,f] using hsite
  · intro a ha
    simpa [d,loaded,atLoad,Config.put,Function.update_of_ne (ha .header (by decide))] using frame a ha
  · intro fuel bs
    have headRun := pre.execute (fuel+3) m bs
    change execute M.program ((fuel+3)+16) c m bs = _ at headRun
    rw [show fuel+19 = (fuel+3)+16 by omega, headRun]
    by_cases h : coord.2 < f .span
    · have read : M.program.step atLoad =
          .read (f .shadow+coord.2) (fun x => atLoad.put (pc 19) (reg .header) x) := by
        rw [step_at hl 17 (by simp [atLoad,h])]
        change CallAction.read (q.reg (reg .addr)) _ = _
        rw [haddr]
      have put : atLoad.put (pc 19) (reg .header) (m (f .shadow+coord.2).val) = loaded := by
        simp [loaded,value,header,h]
      simp only [execute, bounds, read, put, dispatch, Option.map_map, Function.comp_def, events, h, ↓reduceIte]
      rfl
    · have lit : M.program.step atLoad = .localStep loaded := by
        rw [step_at hl 18 (by simp [atLoad,h])]
        change CallAction.localStep (atLoad.put _ _ 0) = _
        simp [loaded,value,header,h]
      simp only [execute, bounds, lit, dispatch, Option.map_map, Function.comp_def, events, h, ↓reduceIte]
      rfl


section Header

open PrimedInputRAM

/-- The auxiliary header at physical width `W` returns the widened virtual word,
including the complete nominated histogram and the zero padding. -/
theorem headerMemory_widen {L : Lengths} {n r H w W s : ℕ} {Q : Layout L n r H w}
    (D : PrimedCounter.Data Q s) (hw : 0 < w) (hwidth : w ≤ W) (j : ℕ) :
    (headerMemory L D.header (D.hist.map (fun x => (x.val : Word W))) j).val = (D.initial j).val := by
  have hbit (b : Bool) : encodeBit W b = ((encodeBit w b).val : Word W) := by
    cases b <;> simp [encodeBit, Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')]
  have hcut (i : Fin 3) : Fin.ofNat (2^W) (cutLength L i) = ((Fin.ofNat (2^w) (cutLength L i)).val : Word W) := by
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt (Q.cutLength_lt i), Fin.ofNat_eq_cast]
  have eqWord : headerMemory L D.header (D.hist.map (fun x => (x.val : Word W))) j =
      ((D.initial j).val : Word W) := by
    unfold PrimedCounter.Data.initial headerMemory
    dsimp only
    split_ifs <;> first | apply hcut | apply hbit | simp [List.getElem?_map]
    cases D.hist[j-Header.count L]? <;> rfl
  rw [eqWord, Fin.val_natCast, Nat.mod_eq_of_lt ((D.initial j).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) hwidth))]

/-- Running the live descriptor and copy calls establishes the shadow-memory
hypothesis used by the leaf reader, including when the virtual width is smaller. -/
theorem prepare_initial {L : Lengths} {n a H u s : ℕ} {Q : Layout L n a H u}
    (D : PrimedCounter.Data Q s) (hu : 0 < u) (width : u ≤ w)
    (src : Fin 7 → Word w) (table shadow : Word w) (m : Memory w)
    (areas : LiveAuxiliaryHeaders.Areas table shadow L D.hist.length src)
    (inputs : LiveAuxiliaryHeaders.InputArrays L D.header (D.hist.map (fun x => (x.val : Word w))) src m)
    (fresh : ∀ a < LiveAuxiliaryHeaders.span L D.hist.length, m (shadow.val+a) = 0) :
    let init := (LiveAuxiliaryHeaders.initTable.instantiate w
      (LiveAuxiliaryHeaders.initData L D.hist.length shadow table src)).program
    let ncopy := LiveAuxiliaryHeaders.populated L D.hist.length
    ∃ es rs, execute init 79 (init.start 0) m [] = some ⟨es,none⟩ ∧
      runSegment (LiveHeaderCopyDispatch.program table) 64 (some 0)
        (after m es) (List.replicate ncopy []) = some rs ∧
      ∀ a < LiveAuxiliaryHeaders.span L D.hist.length,
        (after (after m es) (eventLog rs) (shadow.val+a)).val = (D.initial a).val := by
  let hist := D.hist.map (fun x => (x.val : Word w))
  have len : hist.length = D.hist.length := List.length_map _
  obtain ⟨es,rs,he,hr,_,_,hm,_⟩ := LiveAuxiliaryHeaders.prepare_native L D.header hist
    src table shadow m (len ▸ areas) inputs (len ▸ fresh)
  refine ⟨es,rs,by simpa only [len] using he,by simpa only [len] using hr,?_⟩
  intro a ha
  rw [hm _ (len ▸ ha)]
  exact headerMemory_widen D hu width a

end Header

section Geometry

open PrimedInputRAM CursorNetwork CursorRouting Compression LocalHistory TraversalRows

variable {L : Lengths} {n a H u s b l t j : ℕ} {Q : Layout L n a H u}
variable {S : Type} [Fintype S]

/-- The translated read agrees with the virtual auxiliary RAM at every address,
including addresses beyond the histogram. -/
theorem header_initial (D : PrimedCounter.Data Q s) (m : Memory w) (shadow limit site : Word w)
    (hlimit : limit.val = LiveAuxiliaryHeaders.span L D.hist.length)
    (fits : shadow.val + limit.val ≤ 2^w)
    (prepared : ∀ i < limit.val, (m (shadow.val+i)).val = (D.initial i).val) :
    (header m shadow limit site).val = (D.initial site.val).val := by
  by_cases h : site < limit
  · have less : site.val < limit.val := h
    rw [header, ite_eq_left h, Fin.val_add, Nat.mod_eq_of_lt (by omega)]
    exact prepared _ less
  · have le : limit.val ≤ site.val := Nat.le_of_not_gt h
    rw [header, ite_eq_right h, PrimedCounter.Data.initial,
      LiveAuxiliaryHeaders.headerMemory_past_end _ _ _ (hlimit ▸ le)]
    rfl

/-- On the descriptor emitted for this cursor processor, the fixed native table
enters the matching validator or transit routine with the entire auxiliary word.
The shadow hypothesis is the memory postcondition of header preparation. -/
theorem leaf_native (hl : Linked M pc reg pub launch transit) (m : Memory w)
    (c : Config w p r) (entry : c.pc = pc 0) (D : PrimedCounter.Data Q s)
    (hD : 1 < b+l) (hd : 2+j = 2^t) (bits : S → ℕ) (cap : ℕ) (v : Position (b+l))
    (hwidth : b+l ≤ w) :
    let f := M.publicData ∘ pub
    (f .stride).val = cap+2 → (f .radixB).val = 2^b → (f .radixL).val = 2^l →
    (c.reg (reg .node)).val = (sitePointers cap (f .base).val
      (siteOrder (cursorState (cursorCoordinateLabels b l) hD hd bits))
      (lanePositions (cursorCoordinateLabels b l) v)).1 →
    (f .span).val = LiveAuxiliaryHeaders.span L D.hist.length →
    (f .shadow).val + (f .span).val ≤ 2^w →
    (∀ i < (f .span).val, (m ((f .shadow).val+i)).val = (D.initial i).val) →
    ∃ d, d.pc = (if v.1.val = 0 then launch else transit) ∧
      (d.reg (reg .cursor)).val = v.1.val ∧ (d.reg (reg .site)).val = v.2.val ∧
      (d.reg (reg .header)).val = (D.initial v.2.val).val ∧
      (∀ a, Preserved reg a → d.reg a = c.reg a) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      ∀ fuel bs, execute M.program (fuel + 19) c m bs =
        (execute M.program fuel d m bs).map fun z =>
          ⟨events m (f .shadow) (f .span) (v.2.val : Word w) ++ z.events,z.result⟩ := by
  intro f hs hb hL hnode hspan fits ready
  let coord := decode (c.reg (reg .node)) (f .base) (f .stride) (f .radixB) (f .radixL)
  obtain ⟨hcur, hsite⟩ := decode_leaf_row hD hd bits cap v _ _ _ _ _ hwidth hs hb hL hnode
  change coord.1.val = v.1.val at hcur
  change coord.2.val = v.2.val at hsite
  have heq : coord.1 = 0 ↔ v.1.val = 0 := by rw [Fin.ext_iff, Fin.val_zero,hcur]
  have he : coord.2 = (v.2.val : Word w) := Fin.ext (hsite.trans (Nat.mod_eq_of_lt (hsite ▸ coord.2.isLt)).symm)
  obtain ⟨d, hpc, hc, hv, hw, frame, mem, per, run⟩ := native hl m c entry
  change d.pc = (if coord.1 = 0 then launch else transit) at hpc
  change d.reg (reg .header) = header m (f .shadow) (f .span) coord.2 at hw
  refine ⟨d,by simpa only [heq] using hpc, (congrArg Fin.val hc).trans hcur,
    (congrArg Fin.val hv).trans hsite, ?_,frame,mem,per,?_⟩
  · rw [hw, header_initial D _ _ _ _ hspan fits ready, hsite]
  · intro fuel bs
    rw [← he]
    exact run fuel bs

end Geometry

end PairSimulation.LeafAddress

end VPVNP
end Computability
end OAI
