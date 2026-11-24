import OAI.Computability.VPVNP.CompressorFormulaRow
import OAI.Computability.VPVNP.CompressorDescriptorSpace
import OAI.Computability.VPVNP.CompressorRecordsCursorParameters
import OAI.Computability.VPVNP.CompressorLevelCounts

/-!
# Publishing the six level scalars for the online compressor

A header describes the current graph and the fixed pass that will consume it.
The initial burst reads the generated cursor parameter frame. Each subsequent
burst reads the preceding level header. Its vertex count grows by the tag radix
for a shrink and by the old degree for a refresh. Its lane count is the preceding
residual radix. The destination address is the worker's first public operand.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DescriptorSpace.Scalars

open BurstRAM BurstRAM.PrivateRAM PhaseRecipe Compression
open scoped Fin.CommRing

/-- The input and output indices are degree exponents. A terminal level spends
no lanes and records its current degree as the output degree. -/
inductive Pass : ℕ → ℕ → Type
  | shrink (a b : ℕ) : Pass a b
  | refresh (a b expanderExponent : ℕ) : Pass a b
  | terminal (a : ℕ) : Pass a a

variable {a b c w : ℕ}

/-- Number of binary lane coordinates consumed by this pass, with zero consumption at a
terminal level. -/
def Pass.spent : Pass a b → ℕ
  | .shrink _ _ => packingLaneBits a 0
  | .refresh _ _ _ => a
  | .terminal _ => 0

/-- Multiplier for the input base-vertex count when publishing the successor header. Shrinking
uses the tag radix and refresh uses the old degree. -/
def Pass.baseFactor : Pass a b → ℕ
  | .shrink _ _ => 2 ^ packingTagBits (2^a)
  | .refresh _ _ _ => 2^a
  | .terminal _ => 1

/-- Expander degree published for a refresh, with zero in the corresponding header field for
other passes. -/
def Pass.expanderDegree : Pass a b → ℕ
  | .refresh _ _ e => 2^e
  | _ => 0

/-- Vertex count, degree, lane radix, residual radix, output degree, expander degree. -/
def values (p : Pass a b) (vertices laneBits : ℕ) : Fin 6 → ℕ :=
  ![vertices, 2^a, 2^laneBits, 2^(laneBits-p.spent), 2^b, p.expanderDegree]

/-- All six scalar values for this pass and input size fit in words of width `w`. -/
def Fits (p : Pass a b) (vertices laneBits w : ℕ) : Prop :=
  ∀ j, values p vertices laneBits j < 2^w

/-- Each scalar can be recovered by its ordinary header load without truncation. -/
def Present (p : Pass a b) (vertices laneBits : ℕ) (src : Word w) (m : Memory w) : Prop :=
  ∀ j : Fin 6, (headerCell m src j.val).val = values p vertices laneBits j

private def fields (p : Pass a b) (vertices degree lanes : Expr) : Fin 6 → Expr :=
  ![vertices, degree, lanes, lanes.div (.lit (2^p.spent)), .lit (2^b), .lit p.expanderDegree]

/-- The source state points at the eight-word frame installed by the cursor
parameter program. Frame cells 3, 4 and 5 are the cursor count and the two radices. -/
def initialRow (p : Pass a b) : FormulaRow 3 where
  dest := .publicWord 0
  fields := fields p ((Expr.header 3).mul (.header 4)) (.header 2) (.header 5)

private def nextVertices : Pass a b → Expr
  | .shrink _ _ => (Expr.header 0).mul (.lit (2^packingTagBits (2^a)))
  | .refresh _ _ _ => (Expr.header 0).mul (.header 1)
  | .terminal _ => .header 0

/-- Read old header cells 0, 1, 3 and 4 as needed. In particular the old
output degree is the new input degree. -/
def advanceRow (p : Pass a b) (q : Pass b c) : FormulaRow 3 where
  dest := .publicWord 0
  fields := fields q (nextVertices p) (.header 4) (.header 3)

private theorem word_of_val {z : Word w} {n : ℕ} (h : z.val = n) : z = (n : Word w) := by
  subst n
  exact Fin.ext (Nat.mod_eq_of_lt z.isLt).symm

private theorem eval_fields (p : Pass a b) (V l : ℕ) (vertices degree lanes : Expr)
    (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (hv : vertices.eval pub s m = (V : Word w)) (hd : degree.eval pub s m = ((2^a : ℕ) : Word w))
    (hl : lanes.eval pub s m = ((2^l : ℕ) : Word w)) (spent : p.spent ≤ l)
    (laneFit : 2^l < 2^w) (j : Fin 6) :
    (fields p vertices degree lanes j).eval pub s m = (values p V l j : Word w) := by
  have divisor : 2^p.spent < 2^w := (Nat.pow_le_pow_right (by decide) spent).trans_lt laneFit
  have quot : 2^l / 2^p.spent = 2^(l-p.spent) := by
    conv_lhs => rw [← Nat.sub_add_cancel spent, pow_add]
    exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)
  fin_cases j
  · exact hv
  · exact hd
  · exact hl
  · change Fin.ofNat _ ((lanes.eval pub s m).val / ((2^p.spent : ℕ) : Word w).val) = _
    rw [hl, Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt laneFit, Nat.mod_eq_of_lt divisor, quot]
    rfl
  · rfl
  · rfl

theorem initial_fields (p : Pass a b) (pub : Fin 5 → Word w) (src : Word w) (m : Memory w)
    {row tag : Word w} {low l W start : ℕ}
    (frame : Frame.data src m = CursorRAM.ScheduleInit.inputs row tag low l a W start)
    (spent : p.spent ≤ l) (laneFit : 2^l < 2^w) (j : Fin 6) :
    ((initialRow p).fields j).eval pub src m = (values p ((low+l)*2^low) l j : Word w) := by
  have read (i : Fin 8) : (Expr.header i.val).eval pub src m =
      CursorRAM.ScheduleInit.inputs row tag low l a W start i := congrFun frame i
  apply eval_fields p _ l _ _ _ pub src m _ _ _ spent laneFit j
  · change (Expr.header 3).eval pub src m * (Expr.header 4).eval pub src m = _
    change (Expr.header (3 : Fin 8).val).eval pub src m * (Expr.header (4 : Fin 8).val).eval pub src m = _
    rw [read, read, Nat.cast_mul]
    rfl
  · exact read (2 : Fin 8)
  · exact read (5 : Fin 8)

theorem advance_fields (p : Pass a b) (q : Pass b c) (pub : Fin 5 → Word w) (src : Word w)
    (m : Memory w) {V l : ℕ} (input : Present p V l src m) (spent : q.spent ≤ l-p.spent)
    (j : Fin 6) : ((advanceRow p q).fields j).eval pub src m =
      (values q (V*p.baseFactor) (l-p.spent) j : Word w) := by
  have read (i : Fin 6) : (Expr.header i.val).eval pub src m = (values p V l i : Word w) :=
    word_of_val (input i)
  have laneFit : values p V l 3 < 2^w := by rw [← input]; exact Fin.isLt _
  apply eval_fields q _ _ _ _ _ pub src m _ _ _ spent laneFit j
  · cases p with
    | shrink b =>
      change (Expr.header 0).eval pub src m * ((2^packingTagBits (2^a) : ℕ) : Word w) = _
      change (Expr.header (0 : Fin 6).val).eval pub src m * _ = _
      rw [read, Nat.cast_mul]
      rfl
    | refresh b e =>
      change (Expr.header 0).eval pub src m * (Expr.header 1).eval pub src m = _
      change (Expr.header (0 : Fin 6).val).eval pub src m * (Expr.header (1 : Fin 6).val).eval pub src m = _
      rw [read, read, Nat.cast_mul]
      rfl
    | terminal =>
      change (Expr.header 0).eval pub src m = ((V*1 : ℕ) : Word w)
      rw [Nat.mul_one]
      exact read (0 : Fin 6)
  · exact read (4 : Fin 6)
  · exact read (3 : Fin 6)

/-- Link the natural scalar count to the mathematical state selected by a real
kernel. The growth of the base is independent of all term choices. -/
def ofOrigin {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
    {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f} {l g : ℕ}
    {X : State a l} {pass : StatePass R X b g} : PassOrigin B f hf pass → Pass a b
  | .shrink i _ _ => .shrink (S.degreeExponent i.castSucc) (S.degreeExponent i.succ)
  | .refresh _ => .refresh S.portExponent (S.degreeExponent 0) S.expanderExponent

theorem origin_counts {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
    {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f} {l g : ℕ}
    {X : State a l} {pass : StatePass R X b g} (o : PassOrigin B f hf pass)
    (term : pass.step.Choice) :
    l = (ofOrigin o).spent+g ∧ Fintype.card (pass.next term).Base =
      Fintype.card X.Base * (ofOrigin o).baseFactor := by
  cases o with
  | shrink i h X =>
    subst h
    refine ⟨by simp only [ofOrigin, Pass.spent, packingLaneBits]; omega, ?_⟩
    change Fintype.card (X.Base × BitWord (packingTagBits (2^S.degreeExponent i.castSucc))) = _
    rw [Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv _), Fintype.card_fin]
    rfl
  | refresh X =>
    refine ⟨rfl, ?_⟩
    change Fintype.card (X.Base × Fin (2^S.portExponent)) = _
    rw [Fintype.card_prod, Fintype.card_fin]
    rfl

/-- Scalar fields occupy the first six words of the persistent level header. -/
def fieldIndex (L : Layout) (six : 6 ≤ L.shape.scalarFields) (i : Fin 6) : Fin L.shape.scalarFields :=
  i.castLE six

private theorem headerRoom (L : Layout) {i : Fin L.levels} (six : 6 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) : levelStart L i.val+6 ≤ 2^w := by
  have h := level_room L fit i
  have hstep : levelStart L (i.val+1) = levelStart L i.val + levelWords L := by
    simp only [levelStart, Nat.succ_mul, Nat.add_assoc]
  rw [hstep] at h
  have hhead : 6 ≤ levelWords L := by unfold levelWords levelHeaderWords; omega
  omega

/-- Complete normal-entry specification, including the six natural values,
the frame for the next pass, and preservation of all other addresses. -/
def Publishes (L : Layout) (i : Fin L.levels) (six : 6 ≤ L.shape.scalarFields)
    (row : FormulaRow 3) (p : Pass a b) (V l : ℕ) (pub : Fin 5 → Word w)
    (src : Word w) (m : Memory w) : Prop :=
  let M := row.recipe.table.instantiate w pub
  let rep := row.recipe.report pub src m
  let out := after m rep.events
  BurstRAM.execute M.program (row.recipe.code.length+1) (M.program.start src) m [] = some rep ∧
    rep.result = some (src+1) ∧
    (∀ j : Fin 6, (out (scalarHead L i (fieldIndex L six j))).val = values p V l j) ∧
    Present p V l (pub 0) out ∧
    (∀ address, address < levelStart L i ∨ levelStart L i + 6 ≤ address → out address = m address) ∧
    rep.events.length = row.recipe.code.length ∧ rep.probes = row.recipe.reads+6 ∧ choiceBits rep.events = []

private theorem publish (L : Layout) (i : Fin L.levels) (six : 6 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (row : FormulaRow 3) (p : Pass a b) (V l : ℕ)
    (pub : Fin 5 → Word w) (src : Word w) (m : Memory w)
    (dst : (pub 0).val = levelStart L i) (address : row.dest = .publicWord 0)
    (words : ∀ j, (row.fields j).eval pub src m = (values p V l j : Word w))
    (fits : Fits p V l w) : Publishes L i six row p V l pub src m := by
  have room := headerRoom L (i := i) six fit
  have atDst : (row.dest.eval pub src m).val = levelStart L i := by rw [address]; exact dst
  obtain ⟨run,ret,fields,outside,cost⟩ := row.execute pub src m (by rw [atDst]; exact room)
  rw [atDst] at fields outside
  let out := after m (row.recipe.report pub src m).events
  have read (j : Fin 6) : (out (levelStart L i+j.val)).val = values p V l j := by
    rw [show out (levelStart L i+j.val) = _ from fields j, words j, Fin.val_natCast, Nat.mod_eq_of_lt (fits j)]
  refine ⟨run,ret,read,?_,outside,cost⟩
  intro j
  have hj := j.isLt
  change (out ((pub 0)+(j.val : Word w)).val).val = _
  rw [Fin.val_add, dst, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : j.val < 2^w),
    Nat.mod_eq_of_lt (by omega : levelStart L i+j.val < 2^w)]
  exact read j

theorem initialize_level (L : Layout) (levels : 0 < L.levels) (six : 6 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (p : Pass a b) (pub : Fin 5 → Word w) (src : Word w)
    (m : Memory w) {row tag : Word w} {low l W start : ℕ}
    (dst : (pub 0).val = levelStart L 0)
    (frame : Frame.data src m = CursorRAM.ScheduleInit.inputs row tag low l a W start)
    (spent : p.spent ≤ l) (fits : Fits p ((low+l)*2^low) l w) :
    Publishes L ⟨0,levels⟩ six (initialRow p) p ((low+l)*2^low) l pub src m :=
  publish L ⟨0,levels⟩ six fit _ p _ l pub src m dst rfl
    (initial_fields p pub src m frame spent (fits 2)) fits

theorem advance (L : Layout) (i : Fin L.levels) (six : 6 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (p : Pass a b) (q : Pass b c) (pub : Fin 5 → Word w)
    (src : Word w) (m : Memory w) {V l : ℕ} (dst : (pub 0).val = levelStart L i)
    (input : Present p V l src m) (spent : q.spent ≤ l-p.spent)
    (fits : Fits q (V*p.baseFactor) (l-p.spent) w) :
    Publishes L i six (advanceRow p q) q (V*p.baseFactor) (l-p.spent) pub src m :=
  publish L i six fit _ q _ _ pub src m dst rfl (advance_fields p q pub src m input spent) fits

/-- The fixed pass's scalars fit whenever the current graph and the two
degree bounds fit. No condition on the remaining lane length is needed. -/
theorem fits_state (p : Pass a b) {l : ℕ} (X : State a l)
    (sites : X.positions < 2^w) (degree : 2^a < 2^w) (nextDegree : 2^b < 2^w)
    (expander : p.expanderDegree < 2^w) : Fits p (Fintype.card X.Base) l w := by
  have pos : X.positions = Fintype.card X.Base * 2^l := by
    rw [State.positions, Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv l), Fintype.card_fin]
  have lanes : 2^l < 2^w := (Nat.le_mul_of_pos_left _ Fintype.card_pos).trans_lt (pos ▸ sites)
  intro j
  fin_cases j
  · exact (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos l)).trans_lt (pos ▸ sites)
  · exact degree
  · exact lanes
  · exact (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans_lt lanes
  · exact nextDegree
  · exact expander

/-- Every selected input level fits under the schedule's common maximum degree. -/
theorem fits_selected {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
    {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
    (v : SelectedLevel B f hf) (sites : v.input.positions < 2^w) (slots : slotDegree S < 2^w) :
    Fits (ofOrigin v.origin) (Fintype.card v.input.Base) v.inputLanes w := by
  apply fits_state _ _ sites (v.oldDegree_le.trans_lt slots) (v.outputDegree_le.trans_lt slots)
  obtain ⟨a,l,b,g,X,p,o,term,selector⟩ := v
  cases o with
  | shrink => exact Nat.two_pow_pos _
  | refresh =>
    exact ((Nat.le_of_succ_le S.degree_bounds.2).trans_lt
      (Finset.le_sup (f := fun j : Fin (S.steps+1) ↦ 2^S.degreeExponent j) (Finset.mem_univ 0)
        |>.trans (le_max_right _ _) |>.trans_lt slots))

/-- The cursor generator supplies the scalar publisher directly from its real
normal-entry report. Both calls use the external memory produced by their
predecessor. -/
theorem initialize_from_parameters (L : Layout) (levels : 0 < L.levels)
    (six : 6 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (p : Pass a b) (pub : Fin 5 → Word w) (params : Fin 8 → Word w)
    (state : Word w) (m : Memory w) {B n l : ℕ} (hB : 1 ≤ B) (hn : 2 ≤ n)
    (hw : w = CursorBounds.wordBits B n) (hpN : (params 0).val = n)
    (hpR : (params 1).val = CursorBounds.addressBits B n) (hpA : (params 2).val = a)
    (hpL : (params 3).val = l) (ha : a < w) (hl : l ≤ CursorBounds.virtualBits B n)
    (frameRoom : (params 7).val+8 ≤ 2^w) (dst : (pub 0).val = levelStart L 0)
    (spent : p.spent ≤ l)
    (fits : Fits p (CursorBounds.virtualBits B n * 2^(CursorBounds.virtualBits B n-l)) l w) :
    let low := CursorBounds.virtualBits B n-l
    let fields := CursorRAM.ScheduleInit.inputs (params 4) (params 5) low l a
      (CursorBounds.initialWidth B n) (params 6).val
    let es := CursorRAM.ParametersInit.events n (params 7) fields
    let M := (CursorRAM.ParametersInit.program.template (some 9)).instantiate w params
    BurstRAM.execute M.program (VirtualParameters.ticks n+43) (M.program.start state) m [] =
        some ⟨es,some (state+1)⟩ ∧
      Publishes L ⟨0,levels⟩ six (initialRow p) p
        (CursorBounds.virtualBits B n*2^low) l pub (params 7) (after m es) := by
  intro low fields es M
  have hlow : low+l = CursorBounds.virtualBits B n := Nat.sub_add_cancel hl
  refine ⟨CursorRAM.ParametersInit.native state m hB hn hw hpN hpR hpA hpL ha hl, ?_⟩
  have hframe := (CursorRAM.ParametersInit.frame_ready m n (params 7) fields frameRoom).1
  exact hlow ▸ initialize_level L levels six fit p pub (params 7) (after m es) dst
    hframe spent (hlow ▸ fits)

/-- The next published vertex count is the base cardinality of the actual
output state, even when its topology and widths depend on the selected term. -/
theorem advance_selected {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
    {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
    {a b l g : ℕ} {X : State a l} {pass : StatePass R X b g} (o : PassOrigin B f hf pass)
    (term : pass.step.Choice) (q : Pass b c) (L : Layout) (i : Fin L.levels)
    (six : 6 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (pub : Fin 5 → Word w) (src : Word w) (m : Memory w)
    (dst : (pub 0).val = levelStart L i) (input : Present (ofOrigin o) (Fintype.card X.Base) l src m)
    (spent : q.spent ≤ g) (fits : Fits q (Fintype.card (pass.next term).Base) g w) :
    Publishes L i six (advanceRow (ofOrigin o) q) q (Fintype.card (pass.next term).Base)
      g pub src m := by
  obtain ⟨hg,hv⟩ := origin_counts o term
  have rem : l-(ofOrigin o).spent = g := by omega
  rw [hv] at fits ⊢
  have h := advance L i six fit _ q pub src m dst input (by rwa [rem]) (by rwa [rem])
  rwa [rem] at h

end CompressorRecords.DescriptorSpace.Scalars

end VPVNP
end Computability
end OAI
