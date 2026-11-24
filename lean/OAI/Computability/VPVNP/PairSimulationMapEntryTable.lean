import OAI.Computability.VPVNP.PairSimulationMapEntryProgram
import OAI.Computability.VPVNP.PairSimulationMapSelectorBank

/-!
# Complete private instruction table for a grouped motif entry

The selector scan, row driver, full-width comparison and histogram loop share
one program counter space and one fixed public-word bank. The decoder and the
row dispatcher share selector ordinals. The expected widths and histogram
registers occupy distinct positions throughout both earlier phases.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapEntryTable

open MotifSelector MotifGrid MotifBlocks MotifConversion MapLookup
open BurstRAM.PrivateRAM PrimedInputRAM

variable {J D E : Type} [Fintype J] [Fintype D] [Fintype E]
  {K : Type} [Field K] {src dst : D → J} {G : Supply J E}
  {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H')
  (z : B.grid.demands) (j : J) {r k p w : ℕ}

/-- Logical registers of the grouped map interpreter, comprising selector registers, row-bank
registers, one expected width per supply edge, and six histogram registers. -/
abbrev Register (D E : Type) :=
  MapSelectorBank.Register ⊕ MapBank.Register D E ⊕ E ⊕ Fin 6

/-- Public-word indices for the selector codes and the row bank's selector ordinals, widths,
matrix keys, and parameter ordinals. -/
abbrev PublicPort := Selector B ⊕ MapBank.PublicPort B z j

/-- The allocation can be embedded in a larger vertex program. -/
structure Allocation (r k : ℕ) where
  /-- Inject the grouped interpreter's logical register slots into the machine register file. -/
  reg : Register D E ↪ Fin r
  /-- Inject the selector-code and matrix-table ports into the enclosing machine's public-word
  bank. -/
  pub : PublicPort B z j ↪ Fin k
  /-- Fixed enumeration of the supply edges used for the port directory and the final width
  checks. -/
  edgeOrder : Fin (Fintype.card E) ≃ E

private noncomputable def number (X : Type*) [Finite X] : X ≃ Fin (Nat.card X) := by
  letI := Fintype.ofFinite X
  exact Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm

/-- One concrete finite allocation before the number of copies, word width, or input. -/
noncomputable def allocation :
    Allocation B z j (Nat.card (Register D E)) (Nat.card (PublicPort B z j)) := by
  classical
  let bank := MapBank.allocation B z j
  letI : Finite (MapBank.PublicPort B z j) := Finite.of_injective bank.port bank.port.injective
  exact ⟨(number _).toEmbedding, (number _).toEmbedding, (Fintype.equivFin E).symm⟩

namespace Allocation

variable {B z j} (A : Allocation B z j r k)

/-- Selector scanner and decoder allocation within the entry table. The decoder's output-name
ports are shared with the row bank's dispatch ordinals. -/
def selectors : MapSelectorBank.Allocation (Selector B) r k where
  register := Function.Embedding.inl.trans A.reg
  port := (⟨Sum.elim Sum.inl (Sum.inr ∘ Sum.inl), by
    intro a b h
    cases a <;> cases b <;> simp_all⟩ : _ ↪ PublicPort B z j).trans A.pub

/-- Restrict the entry table's registers and public ports to the selected-row driver and matrix
bank. -/
def bank : MapBank.Allocation B z j r k where
  register := (Function.Embedding.inl.trans Function.Embedding.inr).trans A.reg
  port := Function.Embedding.inr.trans A.pub

/-- Assign one separate physical register per supply edge for its expected total payload width. -/
def expected : E ↪ Fin r :=
  ((Function.Embedding.inl.trans Function.Embedding.inr).trans Function.Embedding.inr).trans A.reg

/-- Place the six private histogram-loop registers in the grouped interpreter's register file. -/
def histReg : Fin 6 ↪ Fin r :=
  ((Function.Embedding.inr.trans Function.Embedding.inr).trans Function.Embedding.inr).trans A.reg

/-- Use the row bank's temporary register as the scratch word for the final width guard. -/
def guardTemp := A.bank.rowReg .tmp

/-- Compiled checks comparing each supply edge's accumulated offset with its expected payload
width, in the allocation's edge order. -/
noncomputable def guard : Flow r k :=
  MapWidths.checkCode (fun e ↦ A.bank.rowReg (.offset (.inr e))) A.expected A.guardTemp
    (List.ofFn A.edgeOrder)

/-- Addresses of the selector scan and decoder instructions installed in the entry table, with
their exits supplied by the enclosing interpreter. -/
abbrev SelectorBody :=
  {a : A.selectors.Address (selectorTable B) // A.selectors.inBody (selectorTable B) a = true}

/-- Addresses of the row driver and matrix lookup bodies installed in the entry table, with the
driver continuations supplied by the enclosing interpreter. -/
noncomputable abbrev BankBody := {a : A.bank.Address // A.bank.inBody a = true}

/-- Addresses of the selector phase, row bank, width checks, seven histogram instructions, and
the success and rejection exits. -/
noncomputable abbrev Address := A.SelectorBody ⊕ A.BankBody ⊕ Fin A.guard.length ⊕ Fin 7 ⊕ Bool

variable (loc : A.Address → Fin p)

/-- Address of the grouped map's normal continuation when `bad` is false or its common
rejecting exit when `bad` is true. -/
def exitPC (bad : Bool) := loc (.inr (.inr (.inr (.inr bad))))

/-- Address in the complete entry table of histogram instruction `i`. -/
def histPC (i : Fin 7) := loc (.inr (.inr (.inr (.inl i))))

/-- Relocate a width-guard label to its numbered instruction in the complete entry table. -/
noncomputable def guardPC (l : A.guard.Label) := loc (.inr (.inr (.inl (A.guard.labels l))))

/-- Redirect the row driver's successful exit into the first guard instruction. -/
noncomputable def bankPlace (a : A.bank.Address) : Fin p :=
  if h : A.bank.inBody a then loc (.inr (.inl ⟨a, h⟩)) else
    match a with
    | .inr (.inr false) => A.guardPC loc A.guard.entry
    | _ => A.exitPC loc true

/-- Redirect a successful selector scan into the driver's first test. -/
noncomputable def selectorPlace (a : A.selectors.Address (selectorTable B)) : Fin p :=
  if h : A.selectors.inBody (selectorTable B) a then loc (.inl ⟨a, h⟩) else
    match a with
    | .exit false => (A.bank.driver (A.bankPlace loc)).pc 0
    | _ => A.exitPC loc true

/-- The relocated selector program whose successful decoder enters row dispatch and whose
failure reaches the entry table's common rejecting exit. -/
noncomputable def selector :=
  A.selectors.program (selectorTable B) (A.selectorPlace loc)

/-- The concrete four phases in the same address space. -/
noncomputable def program : MapEntry.Program B z j p r k where
  selector := A.selector loc
  bank := A.bank
  loc := A.bankPlace loc
  edgeOrder := A.edgeOrder
  expected := A.expected
  guardTemp := A.guardTemp
  guardPC := A.guardPC loc
  histPC := A.histPC loc
  histReg := A.histReg
  done := A.exitPC loc false
  bad := A.exitPC loc true

/-- The complete code, including a common reject instruction and a normal exit. -/
noncomputable def text : A.Address → Instr 2 p r k
  | .inl a => A.selectors.text (selectorTable B) (A.selectorPlace loc) a.val
  | .inr (.inl a) => A.bank.text (A.bankPlace loc) a.val
  | .inr (.inr (.inl a)) =>
    ((A.guard.code (A.guard.labels.symm a)).map
      (fun l ↦ (l.map (A.guardPC loc)).getD (A.histPC loc 0))).emit (A.exitPC loc true)
  | .inr (.inr (.inr (.inl i))) =>
    PrivateLabels.instruction (A.histPC loc) A.histReg (A.exitPC loc false) i
  | .inr (.inr (.inr (.inr false))) => .accept
  | .inr (.inr (.inr (.inr true))) => .reject

/-- Only the successful continuation can be replaced by an enclosing procedure. -/
def installed : A.Address → Bool
  | .inr (.inr (.inr (.inr false))) => false
  | _ => true

/-- The actual instructions discharge the common evaluator's control hypotheses. -/
theorem linked (M : Machine w p r k) (h : ∀ a, A.installed a = true →
    M.code (loc a) = (A.text loc a).resize w) : (A.program loc).Linked M := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · apply A.selectors.linked (selectorTable B) (A.selectorPlace loc)
    intro a ha
    rw [selectorPlace, dite_eq_left ha, h _ rfl]
    rfl
  · change ∀ a : A.bank.Address, A.bank.inBody a = true →
      M.code (A.bankPlace loc a) = (A.bank.text (A.bankPlace loc) a).resize w
    intro a ha
    have he : A.bankPlace loc a = loc (.inr (.inl ⟨a, ha⟩)) := by
      simp only [bankPlace, ha, ↓reduceDIte]
    rw [he]
    exact h _ rfl
  · change Flow.Linked M A.guard (A.guardPC loc) (A.histPC loc 0) (A.exitPC loc true)
    constructor
    intro l
    have hl := h (.inr (.inr (.inl (A.guard.labels l)))) rfl
    change M.code (A.guardPC loc l) = _ at hl
    rw [hl]
    simp [text]
  · intro i
    change M.code (A.histPC loc i) = _
    rw [histPC, h _ rfl]
    fin_cases i <;> rfl

private theorem selectorSaved {q : Fin r} (h : ∀ a, q ≠ A.selectors.register a) :
    (A.program loc).SelectorSaved q :=
  ⟨⟨h (.inl 0), h (.inl 1), h (.inl 2), h (.inl 4), h (.inl 5), h (.inl 6), h (.inl 7)⟩,
    fun i ↦ h (.inr i)⟩

/-- Width targets and histogram registers survive both earlier stages. -/
theorem separate : (A.program loc).Separate :=
  ⟨fun _ ↦ A.selectorSaved loc (fun _ ↦ A.reg.injective.ne Sum.inr_ne_inl),
    fun _ ↦ A.selectorSaved loc (fun _ ↦ A.reg.injective.ne Sum.inr_ne_inl),
    fun _ ↦ A.selectorSaved loc (fun _ ↦ A.reg.injective.ne Sum.inr_ne_inl),
    fun _ _ ↦ A.reg.injective.ne (Sum.inr_injective.ne Sum.inr_ne_inl),
    fun _ _ ↦ A.reg.injective.ne (Sum.inr_injective.ne Sum.inr_ne_inl)⟩

/-- The public selector codes precede the public row bank. Every decoded ordinal
uses exactly the port tested by row dispatch. -/
noncomputable def words (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (selector : Selector B ↪ BurstRAM.Word w)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w) : PublicPort B z j → BurstRAM.Word w :=
  Sum.elim (fun s ↦ MapLookup.widen fb (selectorCode B s))
    (MapBank.Allocation.words fd fs selector ordinal)

theorem public_spec (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (selector : Selector B ↪ BurstRAM.Word w)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w) (M : Machine w p r k)
    (h : ∀ a, M.publicData (A.pub a) = words fb fd fs selector ordinal a) :
    (A.program loc).Public M selector ordinal fb fd fs :=
  ⟨fun s ↦ h (.inl s), fun _ ↦ rfl, fun a ↦ h (.inr a)⟩

/-- Install public values at their fixed addresses inside an enclosing bank. -/
noncomputable def install (values : PublicPort B z j → BurstRAM.Word w)
    (other : Fin k → BurstRAM.Word w) (q : Fin k) : BurstRAM.Word w := by
  classical
  exact if h : ∃ a, A.pub a = q then values h.choose else other q

theorem install_at (values : PublicPort B z j → BurstRAM.Word w) (other : Fin k → BurstRAM.Word w)
    (a : PublicPort B z j) : A.install values other (A.pub a) = values a := by
  classical
  have he : ∃ t, A.pub t = A.pub a := ⟨a, rfl⟩
  rw [install, dite_eq_left he, A.pub.injective he.choose_spec]

/-- Bijection numbering every symbolic instruction address of the complete grouped map entry. -/
noncomputable def locations : A.Address ≃ Fin (Nat.card A.Address) := number _

/-- Numerical fixed finite table; all relative and absolute targets above are its own PCs. -/
noncomputable def template : Template (Nat.card A.Address) r k :=
  let place := A.locations
  ⟨2, (A.selector place).scan 0, fun i ↦ A.text place (place.symm i)⟩

theorem template_linked (pub : Fin k → BurstRAM.Word w) :
    (A.program A.locations).Linked (A.template.instantiate w pub) := by
  apply A.linked
  intro a _
  simp [template, Template.instantiate]


/-- Both final exits are genuine terminal instructions of the standalone template. -/
theorem template_exits (pub : Fin k → BurstRAM.Word w) :
    let P := A.program A.locations
    let M := A.template.instantiate w pub
    M.code P.bad = .reject ∧ M.code P.done = .accept := by
  dsimp only
  simp [template, Template.instantiate, program, exitPC, text, Instr.resize]

/-- The fixed template instantiated with its actual selector, width and matrix words. -/
noncomputable def machine (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (selector : Selector B ↪ BurstRAM.Word w)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w) : Machine w (Nat.card A.Address) r k :=
  A.template.instantiate w (A.install (words fb fd fs selector ordinal) (fun _ ↦ 0))

theorem machine_public (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w)
    (fs : ∀ s e, basePayload B s e ≤ w) (selector : Selector B ↪ BurstRAM.Word w)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w) :
    (A.program A.locations).Public (A.machine fb fd fs selector ordinal)
      selector ordinal fb fd fs :=
  A.public_spec A.locations fb fd fs selector ordinal _ (A.install_at _ (fun _ ↦ 0))

end Allocation

end PairSimulation.MapEntryTable

end VPVNP
end Computability
end OAI
