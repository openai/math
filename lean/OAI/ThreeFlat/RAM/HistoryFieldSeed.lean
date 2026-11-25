import OAI.ThreeFlat.RAM.PhysicalFieldTable
import OAI.ThreeFlat.RAM.ExpressionScan
import OAI.ThreeFlat.BlankNetwork
import OAI.ThreeFlat.RAM.HistoryFactorLibrary

namespace OAI
/-! # Installing the fixed field table after the physical tick inputs -/

namespace ThreeFlat.RAM.HistoryFieldSeed

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM BitLayout DescriptorExpr DescriptorScan
  HistoryFactors Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {p w P R K : ℕ}

noncomputable def fieldExpr (code : FieldCode F w) (base : ℕ) : Term w K 1 :=
  PhysicalFieldTable.atAddress code (.literal (base : Word w)) (.result 0)

theorem fieldExpr_steps (code : FieldCode F w) (base : ℕ) :
    (fieldExpr (K:=K) code base).steps = 6*(Fintype.card F*Fintype.card F)+7 := by
  rw [Term.steps_eq]
  simp [fieldExpr, Term.literal, Term.binds]
  omega

/-- The installed data words in the field segment. Outside this interval all prior
input words, including source pointers, stay at their original addresses. -/
noncomputable def seeded (N : BitNetwork F p) (code : FieldCode F w)
    (pin : Fin p → Bool) (input : Memory w) : Memory w :=
  fillSegment (mulBase p N.internal N.cells) (Fintype.card F * Fintype.card F)
    (memory N code pin (fun _ => false)) input

/-- Concrete field installation using a fixed read-only expression and the three
native scan instructions. The finite field determines its ROM size and runtime. -/
theorem generate_field (N : BitNetwork F p) (code : FieldCode F w) (pin : Fin p → Bool)
    (M : Machine w P R K) (reg : Fin 4 ↪ Fin R) (L : Labels P) (loop : Installed M reg L)
    (loc : Fin (fieldExpr (K:=K) code (mulBase p N.internal N.cells)).labels → Fin P)
    (tmp : Fin (fieldExpr (K:=K) code (mulBase p N.internal N.cells)).binds ↪ Fin R)
    (fresh : ∀ i j, reg i ≠ tmp j)
    (entry : loc (fieldExpr (K:=K) code (mulBase p N.internal N.cells)).first = L.describe)
    (rows : ∀ i, M.code (loc i) = (fieldExpr (K:=K) code (mulBase p N.internal N.cells)).emit
      loc (fun _ => reg 0) tmp (reg 2) L.store i)
    (c : Config w P R) (input : Memory w) (atGuard : c.pc = L.guard)
    (start : (c.reg (reg 0)).val = mulBase p N.internal N.cells)
    (stop : (c.reg (reg 1)).val = footprint N) (unit : c.reg (reg 3) = 1) :
    ∃ steps ≤ 1+(Fintype.card F * Fintype.card F)*(6*(Fintype.card F*Fintype.card F)+10),
      ∃ out : Config w P R, out.pc = L.exit ∧
        advance M.program steps c input = some (out, seeded N code pin input) := by
  let base := mulBase p N.internal N.cells
  let e := fieldExpr (K:=K) code base
  let word := memory N code pin (fun _ => false)
  let valid := scanInvariant (p:=P) reg base (footprint N) input
  have fits : footprint N ≤ 2^w := stop ▸ (c.reg (reg 1)).isLt.le
  have desc : Describes M reg L e.steps word valid := by
    apply describes_expression M reg L e loc tmp fresh entry rows base (footprint N) input word
    intro addr m lo hi _
    apply PhysicalFieldTable.atAddress_memory N code pin (fun _ => false) (fun _ => 0)
      M.publicData m (fun _ => addr) (.literal (base : Word w)) (.result 0) addr.val lo hi fits
    · rfl
    · exact (Fin.cast_val_eq_self addr).symm
  have ok : valid c input := ⟨unit,start.ge,stop,fun _ _ => rfl⟩
  have len : (c.reg (reg 0)).val + Fintype.card F*Fintype.card F = (c.reg (reg 1)).val := by
    rw [start,stop]; rfl
  obtain ⟨steps,hsteps,out,hpc,run⟩ := generate M reg L loop _ word valid desc _ c input atGuard ok len
  refine ⟨steps, ?_, out,hpc, ?_⟩
  · simpa [e,fieldExpr_steps,Nat.add_assoc] using hsteps
  · simpa only [start,seeded,word] using run

omit [Fintype F] [Field F] in
/-- Exact source values may be certified directly on the raw physical tape. -/
theorem source_words {N : BitNetwork F p} {pin : Fin p → Bool} {input : Memory w}
    (zero : input 0 = 0) (one : input 1 = 1)
    (pins : ∀ i : Fin p, input (2+i.val) = bitWord w (pin i))
    (hidden : ∀ i : Fin N.internal, input (hiddenBase p+i.val) = 0) :
    ∀ s : BitSource N.internal p, input (sourceAddress s) =
      bitWord w (s.read (fun _ => false) pin) := by
  intro s
  cases s with
  | constant v => cases v <;> assumption
  | hidden i => exact hidden i
  | pin i => exact pins i

/-- This is the outer-memory premise of the weighted interpreter after the ROM scan. -/
theorem outside_field (N : BitNetwork F p) (code : FieldCode F w) (pin : Fin p → Bool)
    (input : Memory w) (source : ∀ s : BitSource N.internal p, input (sourceAddress s) =
      bitWord w (s.read (fun _ => false) pin)) (a : ℕ) (ha : a < footprint N)
    (away : a < cellsBase p N.internal ∨ mulBase p N.internal N.cells ≤ a) :
    seeded N code pin input a = memory N code pin (fun _ => false) a := by
  rcases away with below | field
  · have lt : a < mulBase p N.internal N.cells := lt_of_lt_of_le below (Nat.le_add_right _ _)
    have no : ¬ (mulBase p N.internal N.cells ≤ a ∧
        a < mulBase p N.internal N.cells+Fintype.card F*Fintype.card F) :=
      fun h => (Nat.not_le.mpr lt) h.1
    rw [seeded,fillSegment,ite_eq_right no]
    obtain ⟨s, rfl⟩ := BitNetwork.source_covers below
    exact (source s).trans (read_source N code pin (fun _ => false) s).symm
  · exact ite_eq_left ⟨field,ha⟩

/-- Source metadata and shared LUTs in the suffix survive installation of the field table. -/
theorem stores_seeded (N : BitNetwork F p) (library : Library N) (code : FieldCode F w)
    (pin : Fin p → Bool) (input : Memory w) {metadata lut : ℕ} (hm : footprint N ≤ metadata)
    (hl : footprint N ≤ lut) (store : Stores N library code metadata lut input) :
    Stores N library code metadata lut (seeded N code pin input) := by
  have frame (a : ℕ) (ha : footprint N ≤ a) : seeded N code pin input a = input a := by
    exact ite_eq_right fun h => (Nat.not_lt.mpr ha) h.2
  constructor
  · intro i j
    exact (frame _ (by omega)).trans (store.source i j)
  · intro i
    exact (frame _ (by omega)).trans (store.tag i)
  · intro t j
    exact (frame _ (by omega)).trans (store.coefficient t j)

end ThreeFlat.RAM.HistoryFieldSeed

end OAI
