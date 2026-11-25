import OAI.Hierarchy.DescentResetSheetsReturnInvoice
import OAI.Hierarchy.DescentResetOperandBookInvoice
import OAI.Hierarchy.DescentPhysicalPublicOperandWork
import OAI.Hierarchy.DescentNamedResetTailSizes

namespace OAI
/-! An invoice for the ranked sheets and successor operands, including the compiled selectors. -/
namespace Hierarchy
open DescentSIMDLookup DescentPackedZip DescentOperandFamilyBook DescentStaticWordColumn
open ProtocolRAM ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
namespace DescentResetOperandSetup.Chart
variable (C : DescentResetOperandSetup.Chart)

def selectorWork := 120+(C.inputs+4+C.fallbackInputs)*(250+11)

theorem selected_work (base : ℕ) (laws : C.Laws) (mode : Option (Fin 7)) (x : Fin C.placement.blocks)
    (arg : Fin C.retained.args) (node : Fin C.retained.nodes)
    (old : Fin C.inputs→Expr) (reg : Fin 4→Expr) (pub : Fin C.fallbackInputs→Expr)
    (low : ∀i,(old i).work≤250) (ports : ∀i,(reg i).work≤250) (surface : ∀i,(pub i).work≤250) :
    (C.selected base laws mode x arg node old reg pub).work≤C.selectorWork:=by
  let j:=finProdFinEquiv (arg,node)
  unfold selectorWork
  rw [Nat.add_mul,Nat.add_mul]
  have arity : C.cable.inputs=C.inputs := rfl
  cases mode with
  | none=>
    have a:=expr_work C.cable.queryLaw C.lanes (C.casts base) 0 old 250 low
    have b:=expr_work laws.rotorQuery C.lanes (C.rotorQuery base) j reg 250 ports
    have c:=expr_work laws.fallbackQuery C.lanes (C.fallbackQuery base) j pub 250 surface
    dsimp only [j] at b c
    simp only [selected,Expr.work]
    omega
  | some f=>
    have a:=expr_work C.cable.prices C.lanes (C.find base) (if f=2 then 0 else 1) old 250 low
    have b:=expr_work laws.rotorFields C.lanes (C.rotorFields base) (finProdFinEquiv (f,j)) reg 250 ports
    have c:=expr_work laws.fallbackFields C.lanes (C.fallbackFields base) (finProdFinEquiv (f,j)) pub 250 surface
    have held : (C.oldValue base x arg node f).work≤25:=of_decide_eq_true rfl
    dsimp only [j] at b c
    by_cases h : f=2 ∨ f=3
    · simp only [selected,ite_eq_left h,Expr.work]
      omega
    · simp only [selected,ite_eq_right h,Expr.work]
      omega

theorem carried_work (base : ℕ) (x : Fin C.placement.blocks) (arg : Fin C.retained.args)
    (node : Fin C.retained.nodes) (hub : Expr) (ticket : Fin C.strip→Expr) (short : hub.work≤250)
    (incoming : ∀i,(ticket i).work≤250) (j : Fin C.inputs) :
    (C.carried base x arg node hub ticket j).work≤250:=by
  unfold carried
  split
  · exact of_decide_eq_true rfl
  · split
    · exact of_decide_eq_true rfl
    · split
      · exact short
      · split
        · exact of_decide_eq_true rfl
        · exact incoming _
end DescentResetOperandSetup.Chart

namespace DescentDatedAddressBook.PhysicalReset
open DescentResetFieldAssembler DescentResetOperandSetup DescentSixParty
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "C" => (v).setup

theorem DateInputs.raw_operands_work :
    (∀i,(u.rawOperands.query i).work≤(C).selectorWork) ∧ (∀i,(u.rawOperands.kept i).work≤(C).selectorWork):=by
  constructor <;> intro i <;> simp only [DateInputs.rawOperands,OperandMenu.renderer] <;>
    apply (C).selected_work
  all_goals first
    | intro j; apply (C).carried_work
      · exact ((v).hub_work _ _).le.trans (by decide)
      · intro d;exact ((v).ticket_work _ _ d).trans (by decide)
    | intro j;fin_cases j <;> exact of_decide_eq_true rfl
    | intro j;exact u.menu.named_public_input_work u.shape floor u.count u.hub u.g u.Y _ _ _ _ _ _ _ j

theorem DateInputs.operand_work :
    (∀i,(u.operand.query i).work≤(C).selectorWork) ∧ (∀i,(u.operand.kept i).work≤(C).selectorWork+12):=by
  refine ⟨u.raw_operands_work.1,fun i=>?_⟩
  rw [show u.operand.kept i=(v).keptValue b (u.rawOperands.kept i) from rfl,(v).keptValue_work]
  exact Nat.add_le_add_right (u.raw_operands_work.2 i) 12

def DateInputs.headerWork (_u : a.DateInputs floor w) : ℕ :=37+28*((v).front.signedQueries/2)

theorem DateInputs.sector_work :
    (∀x j,(u.sectors.header x j).work≤u.headerWork) ∧ (∀x j,(u.sectors.original x j).work≤7):=by
  constructor
  · intro x j
    rcases j with stem | (_ | (contact | private_))
    · change ((v).front.stemOperand _ _ _).work≤_
      rw [CandidateFront.stem_operand_work]
      unfold headerWork
      omega
    · exact (v).front.trunk_operand_work _ _
    · change 7≤37+28*_;omega
    · change 7≤37+28*_;omega
  · intro x j; exact of_decide_eq_true rfl

def DateInputs.sheetBill :=
  (v).rowBill u.sectors ((v).sheetsStart b) b u.headerWork 7 (C).selectorWork ((C).selectorWork+12)+
  (C).setupInvoice ((v).operandFloor b) w

theorem DateInputs.sheets_bill (pitch : (C).SourcePitches) (before : 0<(v).controlRegisters.dims.oldLanes)
    (after_ : 0<(v).controlRegisters.dims.lanes) (blocks : 0<(v).controlRegisters.dims.blocks) :
    instructionWords ((v).sheetsReturn u.sectors ((v).sheetsStart b) u.operand b u.degree u.bank u.laws w)
       ((v).sheetsTime u.sectors ((v).sheetsStart b) u.operand b u.degree u.bank u.laws w)≤u.sheetBill:=by
  have h:=u.sector_work
  have p:=u.operand_work
  have row:=(v).sheets_invoice u.sectors ((v).sheetsStart b) u.operand b u.degree u.bank u.laws w
    u.headerWork 7 (C).selectorWork ((C).selectorWork+12) h.1 h.2 p.1 p.2 before after_ blocks
  have code:=(C).setup_invoice ((v).operandFloor b) w u.bank u.laws pitch (of_decide_eq_true rfl) (fun j=>of_decide_eq_true rfl)
  unfold instructionWords sheetBill
  omega
end DescentDatedAddressBook.PhysicalReset

namespace DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet : ℕ) (old : Prior) (base : ℕ)
local notation "output_" => fromBoard G S board k tail age p f g drift degree payload e previous M nextM C packet old base

theorem sheet_pitches (prior : 0<old.operandLanes) (current : 0<M) :
    (output_).setup.SourcePitches ∧ 0<(output_).controlRegisters.dims.oldLanes ∧
    0<(output_).controlRegisters.dims.lanes ∧ 0<(output_).controlRegisters.dims.blocks:=by
  have matrix : 0<(output_).setup.retained.matrixLanes := by
    let exponent := S.retainedExponent G k tail drift degree p age payload
    let c := S.groupWidth k tail age
    change 0<2^(exponent+k)/2^(c-exponent+(exponent+k)-c)
    exact Nat.div_pos (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.two_pow_pos _)
  refine ⟨?_,?_,?_,?_⟩
  · constructor <;> first | exact current | exact prior | exact matrix | exact Nat.two_pow_pos _
  all_goals first | exact current | exact Nat.two_pow_pos _

end DescentDatedAddressBook.ResetOutput
end
end Hierarchy

end OAI
