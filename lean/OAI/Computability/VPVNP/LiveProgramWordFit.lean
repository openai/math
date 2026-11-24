import OAI.Computability.VPVNP.LiveLayoutWordFit
import OAI.Computability.VPVNP.LiveHeaderSitePowers
import OAI.Computability.VPVNP.LiveProgram
import OAI.Computability.VPVNP.RAMTapePublicInputOperands

/-!
# Word fit of the executable live program's public bank

The disjoint operand bank includes all nested header rows and the outer
dispatch tag. The pair's two literal inputs carry the original program
prefix. All remaining slots use length-only expressions whose intermediate
results fit at a common threshold in the input length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram

open Filter
open RAMTape.InputOperandMachine

/-- A literal input bypasses geometry arithmetic in the native bank loader. -/
def InputOperand.SitePowers : InputOperand → Prop
  | .geometry e => e.SitePowers
  | .prefixLength | .prefixWord => True

private theorem vec_all {α : Type*} {P : α → Prop} {n : ℕ} (a : α) (v : Fin n → α) :
    (∀ j, P (Matrix.vecCons a v j)) ↔ P a ∧ ∀ j, P (v j) :=
  ⟨fun h => ⟨h 0, fun j => h j.succ⟩,fun ⟨ha,hv⟩ => Fin.cases ha hv⟩

private theorem add_site (a b : PublicExpr) : (a+b).SitePowers ↔ a.SitePowers ∧ b.SitePowers := Iff.rfl
private theorem mul_site (a b : PublicExpr) : (a*b).SitePowers ↔ a.SitePowers ∧ b.SitePowers := Iff.rfl
private theorem clog_site (a : PublicExpr) : a.clog2.SitePowers ↔ a.SitePowers := Iff.rfl
private theorem lit_site (v : ℕ) : (OfNat.ofNat v : PublicExpr).SitePowers := True.intro

local macro "site_vec" : tactic => `(tactic|
  simp [vec_all,add_site,mul_site,clog_site,lit_site,
    HeaderLayout.capacity,HeaderLayout.exterior,HeaderLayout.exponent,HeaderLayout.config,
    HeaderLayout.advice,HeaderLayout.rightIndex,HeaderLayout.leftIndex,HeaderLayout.population,
    HeaderLayout.high,HeaderLayout.index,HeaderLayout.firstTail,HeaderLayout.mode,HeaderLayout.flag,
    HeaderLayout.width, *] <;> repeat' first | exact True.intro | assumption | constructor)

namespace StageOperands

private theorem router_safe (e : PublicExpr) (he : e.SitePowers) : ∀ j, (router e j).SitePowers := by
  unfold router
  site_vec

private theorem nomination_safe (c : Constants) : ∀ j, (nomination c j).SitePowers := by
  unfold nomination
  site_vec

private theorem auxiliary_safe (c : Constants) : ∀ j, (auxiliary c j).SitePowers := by
  unfold auxiliary
  site_vec

private theorem auxiliaryCopy_safe (c : Constants) : ∀ j, (auxiliaryCopy c j).SitePowers := by
  unfold auxiliaryCopy
  site_vec

private theorem pair_safe (c : Constants) : ∀ j, (pair c j).SitePowers := by
  intro j
  fin_cases j <;> simp [pair,InputOperand.SitePowers,HeaderLayout.index,add_site] <;> exact True.intro

private theorem exponents_safe (c : Constants) : ∀ j, (exponents c j).SitePowers := by
  unfold exponents
  site_vec

private theorem control_safe (c : Constants) (e : PublicExpr) (he : e.SitePowers) :
    ∀ j, (control c e j).SitePowers := by
  unfold control
  site_vec

private theorem lengthPack_safe (c : Constants) : ∀ j, (lengthPack c j).SitePowers := by
  unfold lengthPack
  site_vec

private theorem adviceFrames_safe (c : Constants) : ∀ j, (adviceFrames c j).SitePowers := by
  unfold adviceFrames
  site_vec

private theorem orderPack_safe (c : Constants) : ∀ j, (orderPack c j).SitePowers := by
  unfold orderPack
  site_vec

private theorem gather_safe (c : Constants) (s : LiveHeaderDescriptors.Side) (e : PublicExpr)
    (he : e.SitePowers) : ∀ j, (gather c s e j).SitePowers := by
  cases s <;> unfold gather <;> site_vec

private theorem transition_safe (c : Constants) : ∀ j, (transition c j).SitePowers := by
  unfold transition
  site_vec

end StageOperands

open StageOperands

set_option maxRecDepth 4096 in
private theorem rows_sitePowers (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (header : ∀ j, (HeaderLayout.operands c.lengths Layout.header j).SitePowers)
    (s : Stage) : ∀ j, ((rows c p O s).operands j).SitePowers := by
  fin_cases s
  · exact header
  · exact router_safe _ (by site_vec)
  · exact nomination_safe c
  · exact auxiliary_safe c
  · exact auxiliaryCopy_safe c
  · exact pair_safe c
  · exact exponents_safe c
  · exact router_safe _ (by site_vec)
  · exact control_safe c _ (Layout.oldState_sitePowers c)
  · exact lengthPack_safe c
  · exact adviceFrames_safe c
  · exact fun _ => Layout.adviceFrames_sitePowers c
  · exact orderPack_safe c
  · exact fun _ => ⟨Layout.adviceFrames_sitePowers c,True.intro⟩
  · exact fun _ => ⟨Layout.adviceFrames_sitePowers c,True.intro⟩
  · exact fun _ => ⟨Layout.adviceFrames_sitePowers c,True.intro⟩
  · exact gather_safe c .left _ (Layout.oldState_sitePowers c)
  · exact router_safe _ (by site_vec)
  · exact control_safe c _ (Layout.newState_sitePowers c)
  · exact gather_safe c .right _ (Layout.newState_sitePowers c)
  · exact transition_safe c

attribute [local irreducible] Pieces.count

theorem operand_at_row (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (s : Stage) (j : Fin (rows c p O s).count) :
    operand c p O ((Pieces.operandEmbedding (rows c p O) s j).castSucc) = (rows c p O s).operands j := by
  unfold operand Pieces.operand
  rw [Fin.snoc_castSucc,Pieces.bank_at]

/-- All 21 rows and the outer tag satisfy the required syntax restriction.
The bounded header rows and the outer pair's literal-prefix slots use their
actual positions in the two nested operand banks. -/
theorem operand_sitePowers (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (j : Fin (Pieces.count (rows c p O)+1)) : (operand c p O j).SitePowers := by
  have hh := HeaderLayout.operands_sitePowers c.lengths_h_sitePowers c.lengths_delta_sitePowers
    c.lengths_advice_sitePowers c.lengths_e_sitePowers c.lengths_config_sitePowers Layout.header_sitePowers
  refine Fin.lastCases (n := Pieces.count (rows c p O)) ?_ (fun i => ?_) j
  · simpa only [operand,Pieces.operand,Fin.snoc_last,InputOperand.SitePowers] using Layout.stageTag_sitePowers
  · simp only [operand,Pieces.operand,Fin.snoc_castSucc,Pieces.bank]
    exact rows_sitePowers c p O hh _ _

/-- The two literal words in the compressed-pair row bypass the arithmetic
expression evaluator. Their positions are relocated by the actual linker. -/
theorem operand_pair_literals (c : Constants) (p : UniversalMachine.Program) (O : PairTable) :
    operand c p O ((Pieces.operandEmbedding (rows c p O) Stage.pair (0 : Fin 11)).castSucc) = .prefixWord ∧
    operand c p O ((Pieces.operandEmbedding (rows c p O) Stage.pair (1 : Fin 11)).castSucc) = .prefixLength := by
  exact ⟨(operand_at_row c p O Stage.pair (0 : Fin 11)).trans rfl,
    (operand_at_row c p O Stage.pair (1 : Fin 11)).trans rfl⟩

/-- No other public row positions request a literal prefix value. -/
theorem row_literal_positions (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (s : Stage) (j : Fin (rows c p O s).count) :
    ((rows c p O s).operands j = .prefixWord ↔ s = Stage.pair ∧ j.val = 0) ∧
      ((rows c p O s).operands j = .prefixLength ↔ s = Stage.pair ∧ j.val = 1) := by
  by_cases pair : s = Stage.pair
  · subst s
    change Fin 11 at j
    change (StageOperands.pair c j = .prefixWord ↔ Stage.pair = Stage.pair ∧ j.val = 0) ∧
      (StageOperands.pair c j = .prefixLength ↔ Stage.pair = Stage.pair ∧ j.val = 1)
    fin_cases j <;> simp [StageOperands.pair]
  · have geom : ∃ e, (rows c p O s).operands j = .geometry e := by
      fin_cases s <;> first | exact ⟨_,rfl⟩ | contradiction
    obtain ⟨e,he⟩ := geom
    simp [he,pair]

private theorem geometryOnly_safe {k : ℕ} (args : Fin k → InputOperand) (h : ∀ i, (args i).SitePowers) :
    ∀ i, (geometryOnly args i).SitePowers := by
  intro i
  cases he : args i with
  | geometry e => simpa only [geometryOnly,he] using (show e.SitePowers by simpa only [he,InputOperand.SitePowers] using h i)
  | prefixWord | prefixLength => simp only [geometryOnly,he]; exact True.intro

private theorem geometry_and_literals {k : ℕ} (args : Fin k → InputOperand) (lit : LiteralPrefix)
    (g : Geometry) (modulus : ℕ) (ha : ∀ i, (geometryOnly args i).Fits g modulus)
    (hl : lit.length < modulus) (hv : lit.value < modulus) :
    ∀ j, match args j with
      | .geometry e => e.Fits g modulus
      | a => a.eval g lit < modulus := by
  intro j
  cases he : args j with
  | geometry e => simpa only [geometryOnly,he] using ha j
  | prefixLength => exact hl
  | prefixWord => exact hv

/-- Simultaneous bounds on every intermediate arithmetic word of the
concrete operand-loading routine, including each nested header expression. -/
theorem eventually_operand_geometry_fits (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    {B : ℕ} (hB : 1 ≤ B) {H : ℕ → ℕ} (hH : PolynomiallyBounded H) :
    ∀ᶠ n in atTop, ∀ j, (geometryOnly (operand c p O) j).Fits (paperGeometry B H n) (2^CursorBounds.wordBits B n) := by
  exact PublicExpr.fits_bank hB hH _ (geometryOnly_safe _ (operand_sitePowers c p O))

/-- A fixed literal prefix also fits at a common length threshold, yielding
exact unpacked operand values in addition to every intermediate word bound. -/
theorem eventually_operand_fits (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (lit : LiteralPrefix) {B : ℕ} (hB : 1 ≤ B) {H : ℕ → ℕ} (hH : PolynomiallyBounded H) :
    ∀ᶠ n in atTop, ∀ j,
      match operand c p O j with
      | .geometry e => e.Fits (paperGeometry B H n) (2^CursorBounds.wordBits B n)
      | a => a.eval (paperGeometry B H n) lit < 2^CursorBounds.wordBits B n := by
  have litFits (v : ℕ) : ∀ᶠ n in atTop, v < 2^CursorBounds.wordBits B n :=
    ((PublicExpr.SitePowers.fits hB hH (show (PublicExpr.lit v).SitePowers from True.intro)).2).mono fun _ h => h.1
  filter_upwards [eventually_operand_geometry_fits c p O hB hH,litFits lit.length,litFits lit.value] with n h hl hv
  exact geometry_and_literals (operand c p O) lit _ _ h hl hv

/-- At the same eventual threshold the executable loader fills every
physical slot with the public operand prescribed by the live machine. -/
theorem eventually_load_operands (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    {B : ℕ} (hB : 1 ≤ B) {H : ℕ → ℕ} (hH : PolynomiallyBounded H) :
    ∀ᶠ n in atTop, let g := paperGeometry B H n
      let args := operand c p O
      ∀ (lit : LiteralPrefix) (st : BurstRAM.Word g.w)
        (rs : Fin (registers args) → BurstRAM.Word g.w) (log : BurstRAM.PrivateRAM.WriteLog g.w),
        ∃ t ≤ RAMTape.PublicExprMachine.coefficient (geometryOnly args)*(g.w+1)^2+
          (Pieces.count (rows c p O)+1)*(8*g.w+3)+2,
          ∃ out : Fin (registers args) → BurstRAM.Word g.w,
            (RAMTape.InputOperandMachine.program args).Runs t
              (RAMTape.ISA.bank (input g lit) st rs log) (RAMTape.ISA.bank (input g lit) st out log) ∧
              ∀ j, out (slot args j) = publicData c p O g lit j := by
  filter_upwards [eventually_operand_geometry_fits c p O hB hH] with n hf
  dsimp only
  intro lit st rs log
  exact runs (operand c p O) (paperGeometry B H n) lit hf st rs log

end LiveProgram

end VPVNP
end Computability
end OAI
