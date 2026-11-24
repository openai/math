import OAI.Computability.VPVNP.PairSimulationMapCallArg
import OAI.Computability.VPVNP.PairSimulationMapExecutable
import OAI.Computability.VPVNP.PairSimulationMapDirectoryInit
import OAI.Computability.VPVNP.PairSimulationMapInitCompiler

/-!
# Computing initial map registers from the private call descriptor

The caller supplies the live widths, one base per endpoint, the copy count, and
the directory, selector-array, label-array and histogram bases. The fixed register
recipes compute all derived bounds from these words. Reads access private memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapCallSetup

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifEntry MapLookup
open MapEntryTable MapPortAgreement MapResidentAgreement
open BurstRAM.PrivateRAM PrimedCounter.GuessWord
open CompressorRecords CompressorRecords.PhaseRecipe
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {r k p w t u : ℕ} (A : Allocation B z j r k)

variable (args : Arg D E ≃ Fin (Fintype.card (Arg D E)))
  (anchorField : LabelField D E)

/-- Expression that loads a map-call operand from the private descriptor at the offset assigned
by `args`. -/
def arg (a : Arg D E) : Expr := .header (args a).val

private def endLength (src dst : D → J) (G : Supply J E) (j : J) : LabelField D E → Expr
  | .inl (false, e) => if j = src e then arg args (.demand e) else .lit 0
  | .inl (true, e) => if j = dst e then arg args (.demand e) else .lit 0
  | .inr (false, e) => if j = G.src e then arg args (.payload e) else .lit 0
  | .inr (true, e) => if j = G.dst e then arg args (.payload e) else .lit 0

/-- Expression for each register, including unused scratch registers initialized to zero. -/
noncomputable def recipe : Register D E → Expr :=
  let read := arg args
  let tagWidth := (read .copies).mul (.lit B.selectorBits)
  let anchor := (read (.base anchorField)).add (read (.payload (edge (anchorPort G j))))
  let high := anchor.add tagWidth
  let sourceEnd := (read .source).add (read .copies)
  let targetEnd := (read .target).add (read .copies)
  fun
  | .inl (.inl a) =>
    ![.lit 0, .lit 0, .lit 0, .lit 1, .lit 0, .lit 0, .lit 0, read .directory,
      (read .directory).add (.lit (ports G j A.edgeOrder).length), anchor, tagWidth] a
  | .inl (.inr a) =>
    ![.lit 0, high, .lit 0, high, .lit 1, .lit 0, sourceEnd, read .source,
      .lit B.selectorBits] a
  | .inr (.inl (.inl a)) => ![read .source, sourceEnd, read .target, .lit 1, .lit 0, .lit 0] a
  | .inr (.inl (.inr (.base f))) => read (.base f)
  | .inr (.inl (.inr (.dataEnd f))) => (read (.base f)).add (endLength args src dst G j f)
  | .inr (.inl (.inr .one)) => .lit 1
  | .inr (.inl (.inr _)) => .lit 0
  | .inr (.inr (.inl e)) => read (.payload e)
  | .inr (.inr (.inr a)) => ![read .target, targetEnd, read .hist, .lit 1, .lit 0, .lit 0] a

variable (slots : Register D E ≃ Fin (Fintype.card (Register D E)))

/-- Index the initial register expressions by the compiler's numerical output slots, using
`slots.symm` to recover each logical map register. -/
noncomputable def recipes (i : Fin (Fintype.card (Register D E))) : Expr :=
  recipe A args anchorField (slots.symm i)

/-- One private load in a compiled expression reads the designated descriptor word. -/
theorem eval_arg (values : Arg D E → BurstRAM.Word w) (c : Config w p r) (ptr : Fin r)
    (h : ∀ a, c.privateMem (c.reg ptr + ((args a).val : BurstRAM.Word w)) = values a)
    (a : Arg D E) :
    (arg args a).eval (fun _ ↦ c.reg ptr) (c.reg ptr) (MapInitCompiler.memory c.privateMem) =
      values a := by
  simpa [arg, Expr.header, Expr.headerAddress, Expr.add, Expr.eval, BinaryOp.eval,
    MapInitCompiler.memory] using h a

variable (loc : A.Address → Fin p) {demand : D → ℕ} {v : E → ℕ}
  {d : DemandBits src dst demand j} {x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j}
  (X : MapEntry.Program.Workspace (A.program loc) demand v d x t w)

/-- The natural data supplied by the caller, converted to machine words. -/
noncomputable def values : Arg D E → BurstRAM.Word w
  | .base f => (X.base f : BurstRAM.Word w)
  | .demand e => (demand e : BurstRAM.Word w)
  | .payload e => (v e : BurstRAM.Word w)
  | .copies => (u : BurstRAM.Word w)
  | .directory => X.directory
  | .source => (X.source : BurstRAM.Word w)
  | .target => (X.target : BurstRAM.Word w)
  | .hist => (X.hist : BurstRAM.Word w)

private theorem len_eq (θ : Fin u → Selector B) (f : LabelField D E)
    (mem : BurstRAM.Memory w) (pub : Fin 5 → BurstRAM.Word w) (st : BurstRAM.Word w)
    (he : ∀ a, (arg args a).eval pub st mem = values A loc X a) :
    (endLength args src dst G j f).eval pub st mem =
      ((MapRowLoop.buffers B z j demand v d x X.base θ 0).len f : BurstRAM.Word w) := by
  rcases f with ⟨b, e⟩ | ⟨b, e⟩
  all_goals cases b
  · by_cases h : j = src e <;> simp [MapRowLoop.buffers, MapRow.endpoint, endLength, h, he,
      values, Expr.eval]
  · by_cases h : j = dst e <;> simp [MapRowLoop.buffers, MapRow.endpoint, endLength, h, he,
      values, Expr.eval]
  · by_cases h : j = G.src e <;> simp [MapRowLoop.buffers, MapRow.endpoint, endLength, h, he,
      values, Expr.eval]
  · by_cases h : j = G.dst e <;> simp [MapRowLoop.buffers, MapRow.endpoint, endLength, h, he,
      values, Expr.eval]

/-- Exact native setup prefix before directory construction. Its outputs are the
map's allocated registers, and its fixed length is independent of all live widths. -/
theorem load (vm : Fin (RegisterSetup.regCount (recipes A args anchorField slots)) ↪ Fin r)
    (place : ∀ a, vm (RegisterSetup.output (recipes A args anchorField slots) (slots a)) = A.reg a)
    (ptr : Fin r) (safe : ∀ i, vm i ≠ ptr) (M : Machine w p r k) (pc : ℕ → Fin p)
    (link : MapInitCompiler.Linked vm ptr M pc
      (RegisterSetup.lines (recipes A args anchorField slots)))
    (c : Config w p r) (hc : c.pc = pc 0) :
    ∃ out, Prefix M c
        (List.replicate (RegisterSetup.lines (recipes A args anchorField slots)).length .tick) out ∧
      out.pc = pc (RegisterSetup.lines (recipes A args anchorField slots)).length ∧
      (∀ a, out.reg (A.reg a) =
        (recipe A args anchorField a).eval (fun _ ↦ c.reg ptr) (c.reg ptr)
          (MapInitCompiler.memory c.privateMem)) ∧ out.privateMem = c.privateMem ∧
      out.persistent = c.persistent ∧ ∀ q, (∀ i, q ≠ vm i) → out.reg q = c.reg q := by
  obtain ⟨out, pre, hd, outputs, rest, hm, hp⟩ :=
    MapInitCompiler.native (recipes A args anchorField slots) vm ptr safe M pc link c hc
  exact ⟨out, pre, hd, fun a ↦ by simpa [place, recipes] using outputs (slots a),
    hm, hp, rest⟩


/-- Combine the computed register formulas with the actual incident bit cells and
the newly installed directory. All remaining assumptions refer to the call operands. -/
theorem ready_of_registers (out : Config w p r)
    (start : out.pc = (A.program loc).selector.scan 0)
    (anchor : X.portBase (anchorPort G j) = (X.base anchorField : BurstRAM.Word w))
    (hv : ∀ e, v e < 2 ^ w) (mem : BurstRAM.Memory w) (pub : Fin 5 → BurstRAM.Word w)
    (st : BurstRAM.Word w) (he : ∀ a, (arg args a).eval pub st mem = values A loc X a)
    (regs : ∀ a, out.reg (A.reg a) = (recipe A args anchorField a).eval pub st mem)
    (resident : MapResidentAgreement.Resident A.edgeOrder x X.portBase out.privateMem X.directory)
    (bits : ∀ (θ : Fin u → Selector B) f
      (l : Fin ((MapRowLoop.buffers B z j demand v d x X.base θ 0).len f)),
      out.privateMem ((X.base f + l.val : ℕ) : BurstRAM.Word w) =
        PrimedInputRAM.encodeBit w ((MapRowLoop.buffers B z j demand v d x X.base θ 0).bits f l)) :
    (A.program loc).Ready X out := by
  have atSlot (a) := regs a
  constructor
  · refine ⟨start, ?_, ?_, ?_, ?_, ?_, ?_, resident, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (atSlot (.inl (.inl 7))).trans (he .directory)
    · apply (atSlot (.inl (.inl 8))).trans
      simp [recipe, Expr.add, Expr.eval, BinaryOp.eval, he, values,
        MapEntryTable.Allocation.program]
    · apply (atSlot (.inl (.inl 9))).trans
      simp [recipe, Expr.add, Expr.eval, BinaryOp.eval, he, values, selectorStart, anchor]
    · apply (atSlot (.inl (.inl 10))).trans
      simp [recipe, Expr.mul, Expr.eval, BinaryOp.eval, he, values]
    · exact (atSlot (.inl (.inl 3))).trans rfl
    · exact (atSlot (.inl (.inl 4))).trans rfl
    · apply (atSlot (.inl (.inr 3))).trans
      simp [recipe, Expr.add, Expr.mul, Expr.eval, BinaryOp.eval, he, values, anchor, add_assoc]
    · exact (atSlot (.inl (.inr 1))).trans (atSlot (.inl (.inr 3))).symm
    · exact (atSlot (.inl (.inr 4))).trans rfl
    · apply (atSlot (.inl (.inr 6))).trans
      simp [recipe, Expr.add, Expr.eval, BinaryOp.eval, he, values]
    · exact (atSlot (.inl (.inr 7))).trans (he .source)
    · exact (atSlot (.inl (.inr 8))).trans rfl
  · intro θ
    constructor
    · exact (atSlot (.inr (.inl (.inr .one)))).trans rfl
    · exact fun f ↦ (atSlot (.inr (.inl (.inr (.base f))))).trans (he (.base f))
    · intro f
      apply (atSlot (.inr (.inl (.inr (.dataEnd f))))).trans
      simp [recipe, Expr.add, Expr.eval, BinaryOp.eval, he, values,
        len_eq A args loc X θ f mem pub st he, MapRowLoop.buffers]
    · intro g
      apply (atSlot (.inr (.inl (.inr (.offset g))))).trans
      cases g <;> simp [recipe, Expr.eval, MapRowLoop.buffers]
    · exact bits θ
  · exact (atSlot (.inr (.inl (.inl 0)))).trans (he .source)
  · apply (atSlot (.inr (.inl (.inl 1)))).trans
    simp [recipe, Expr.add, Expr.eval, BinaryOp.eval, he, values]
  · exact (atSlot (.inr (.inl (.inl 2)))).trans (he .target)
  · exact (atSlot (.inr (.inl (.inl 3)))).trans rfl
  · intro e
    have h := (atSlot (.inr (.inr (.inl e)))).trans (he (.payload e))
    exact (congrArg Fin.val h).trans (Nat.mod_eq_of_lt (hv e))
  · refine ⟨(atSlot (.inr (.inr (.inr 0)))).trans (he .target), ?_,
      (atSlot (.inr (.inr (.inr 2)))).trans (he .hist), (atSlot (.inr (.inr (.inr 3)))).trans rfl⟩
    apply (atSlot (.inr (.inr (.inr 1)))).trans
    simp [recipe, Expr.add, Expr.eval, BinaryOp.eval, he, values]

/-- Raw caller data for initializing the map, independent of the selector sequence. -/
structure Input (ptr : Fin r) (c : Config w p r) : Prop where
  descriptor : ∀ a, c.privateMem (c.reg ptr + ((args a).val : BurstRAM.Word w)) = values A loc X a
  payloadFit : ∀ e, v e < 2 ^ w
  supplyBase : ∀ t : Port G j,
    X.portBase t = (X.base (MapDirectoryInit.portField t) : BurstRAM.Word w)
  supply : ∀ (t : Port G j) (l : Fin (v (edge t) + u * B.selectorBits)),
    c.privateMem (X.portBase t + (l.val : BurstRAM.Word w)) =
      PrimedInputRAM.encodeBit w (field x t l)
  demandCells : ∀ q : Bool × D, ∀ l : Fin (MapRow.endpoint src dst j demand d q).1,
    c.privateMem ((X.base (.inl q) + l.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w ((MapRow.endpoint src dst j demand d q).2 l)
  supplyApart : ∀ (t : Port G j) (l : Fin (v (edge t) + u * B.selectorBits))
    (a : MapDirectoryInit.Row A),
    X.portBase t + (l.val : BurstRAM.Word w) ≠ X.directory + (a.val : BurstRAM.Word w)
  demandApart : ∀ q : Bool × D, ∀ l : Fin (MapRow.endpoint src dst j demand d q).1,
    ∀ a : MapDirectoryInit.Row A,
    ((X.base (.inl q) + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (a.val : BurstRAM.Word w)

private def segment {w : ℕ} (mem : BurstRAM.Word w → BurstRAM.Word w) (base : ℕ)
    (b : (l : ℕ) × (Fin l → Bool)) : Prop :=
  ∀ i : Fin b.1, mem ((base + i.val : ℕ) : BurstRAM.Word w) = PrimedInputRAM.encodeBit w (b.2 i)

private theorem rowData (mem : BurstRAM.Word w → BurstRAM.Word w)
    (hb : ∀ t : Port G j, X.portBase t = (X.base (MapDirectoryInit.portField t) : BurstRAM.Word w))
    (hs : ∀ (t : Port G j) (l : Fin (v (edge t) + u * B.selectorBits)),
      mem (X.portBase t + (l.val : BurstRAM.Word w)) = PrimedInputRAM.encodeBit w (field x t l))
    (hd : ∀ q : Bool × D, segment mem (X.base (.inl q)) (MapRow.endpoint src dst j demand d q))
    (θ : Fin u → Selector B) (f : LabelField D E) :
    ∀ l : Fin ((MapRowLoop.buffers B z j demand v d x X.base θ 0).len f),
      mem ((X.base f + l.val : ℕ) : BurstRAM.Word w) =
        PrimedInputRAM.encodeBit w
          ((MapRowLoop.buffers B z j demand v d x X.base θ 0).bits f l) := by
  rcases f with q | ⟨b, e⟩
  · exact hd q
  · change segment mem (X.base (.inr (b, e)))
      (MapRow.endpoint G.src G.dst j v (mapHalf G (fun _ ↦ payloadBits) x) (b, e))
    cases b <;> rw [MapRow.endpoint]
    · split
      · rename_i he
        intro i
        let t : Port G j := .inl ⟨e, he⟩
        have cell := hs t (Fin.castLE (Nat.le_add_right ..) i)
        change mem (X.portBase t + (i.val : BurstRAM.Word w)) = _ at cell
        rw [hb] at cell
        rw [Nat.cast_add]
        exact cell
      · exact fun i ↦ i.elim0
    · split
      · rename_i he
        intro i
        let t : Port G j := .inr ⟨e, he⟩
        have cell := hs t (Fin.castLE (Nat.le_add_right ..) i)
        change mem (X.portBase t + (i.val : BurstRAM.Word w)) = _ at cell
        rw [hb] at cell
        rw [Nat.cast_add]
        exact cell
      · exact fun i ↦ i.elim0

/-- The descriptor reader and directory writer leave the actual map program ready at
its first instruction, preserving every private cell outside the fixed port directory. -/
theorem native (slots : Register D E ≃ Fin (Fintype.card (Register D E))) (M : Machine w p r k)
    (ptr : Fin r) (scratch : Fin 2 ↪ Fin r) (apart : ∀ a i, A.reg a ≠ scratch i)
    (dirPC : MapDirectoryInit.Address A → Fin p)
    (dirLink : ∀ a, M.code (dirPC a) =
      (MapDirectoryInit.text A scratch dirPC ((A.selector loc).scan 0) a).resize w) :
    let anchor := MapDirectoryInit.portField (anchorPort G j)
    let f := recipes A args anchor slots
    ∀ (vm : Fin (RegisterSetup.regCount f) ↪ Fin r)
      (_place : ∀ a, vm (RegisterSetup.output f (slots a)) = A.reg a)
      (_safe : ∀ i, vm i ≠ ptr) (pc : ℕ → Fin p)
      (_hl : MapInitCompiler.Linked vm ptr M pc (RegisterSetup.lines f))
      (_endPC : pc (RegisterSetup.lines f).length = dirPC (.inl ()))
      (c : Config w p r), c.pc = pc 0 → Input A args loc X ptr c →
      ∃ out, Prefix M c (List.replicate
          ((RegisterSetup.lines f).length + (1 + 3 * (ports G j A.edgeOrder).length)) .tick) out ∧
        (A.program loc).Ready X out ∧ out.persistent = c.persistent ∧
        ∀ q, (∀ a : MapDirectoryInit.Row A, q ≠ X.directory + (a.val : BurstRAM.Word w)) →
          out.privateMem q = c.privateMem q := by
  intro anchor f vm place safe pc hl endPC c hc input
  obtain ⟨m, pre, hm, vals, mem, per, _⟩ :=
    load A args anchor slots vm place ptr safe M pc hl c hc
  have he := eval_arg args (values A loc X) c ptr input.descriptor
  have dir : m.reg (A.selectors.scanReg 7) = X.directory :=
    (vals (.inl (.inl 7))).trans (he .directory)
  have one : m.reg (A.selectors.scanReg 3) = 1 := (vals (.inl (.inl 3))).trans rfl
  obtain ⟨out, tail, start, hp, keep, pointers, outside⟩ :=
    MapDirectoryInit.native A scratch dirPC ((A.selector loc).scan 0) M dirLink apart m
      (hm.trans endPC) one X.portsFit.le
  rw [dir] at pointers outside
  have frame (q) (hq : ∀ a : MapDirectoryInit.Row A, q ≠ X.directory + (a.val : BurstRAM.Word w)) :
      out.privateMem q = c.privateMem q := (outside q hq).trans (congrFun mem q)
  have supply (t : Port G j) (l : Fin (v (edge t) + u * B.selectorBits)) :
      out.privateMem (X.portBase t + (l.val : BurstRAM.Word w)) =
        PrimedInputRAM.encodeBit w (field x t l) :=
    (frame _ (input.supplyApart t l)).trans (input.supply t l)
  have dem (q : Bool × D) (l : Fin (MapRow.endpoint src dst j demand d q).1) :
      out.privateMem ((X.base (.inl q) + l.val : ℕ) : BurstRAM.Word w) =
        PrimedInputRAM.encodeBit w ((MapRow.endpoint src dst j demand d q).2 l) :=
    (frame _ (input.demandApart q l)).trans (input.demandCells q l)
  refine ⟨out, ?_, ready_of_registers A args anchor loc X out start
    (input.supplyBase _) input.payloadFit _ _ _ he (fun a ↦ (keep _ (apart a 0) (apart a 1)).trans
      (vals a)) ⟨?_, supply⟩ (rowData A loc X _ input.supplyBase supply dem), hp.trans per, frame⟩
  · rw [List.replicate_add]
    exact pre.append tail
  · intro a
    let t := (ports G j A.edgeOrder).get a
    have base : m.reg (A.bank.rowReg (.base (MapDirectoryInit.portField t))) = X.portBase t :=
      ((vals (.inr (.inl (.inr (.base (MapDirectoryInit.portField t)))))).trans
        (he (.base (MapDirectoryInit.portField t)))).trans (input.supplyBase t).symm
    have width : m.reg (A.expected (edge t)) = (v (edge t) : BurstRAM.Word w) :=
      (vals (.inr (.inr (.inl (edge t))))).trans (he (.payload (edge t)))
    exact (pointers a).trans (congrArg₂ (· + ·) base width)

end PairSimulation.MapCallSetup

end VPVNP
end Computability
end OAI
