import OAI.ThreeFlat.RAM.HistoryPadDriver
import OAI.ThreeFlat.RAM.LiteralTable
import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # Publishing the selected forest's final row and hidden-bit counts -/

noncomputable section
namespace ThreeFlat.RAM.SelectedPadHeader
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan PhysicalProcedure
open scoped Fin.CommRing
variable {w : ℕ}

private def col (ctl «meta» p H tag : ℕ) : ℕ → Term w 0 1
  | 0 => .binary .add (.literal «meta») (.binary .mul (.literal 4) (.load (.literal (ctl+2:ℕ))))
  | 1 => .binary .sub (.literal H) (.load (.literal (ctl+3:ℕ)))
  | 2 => .binary .add (.literal (2+p:ℕ)) (.load (.literal (ctl+3:ℕ)))
  | _ => .literal tag

private def term (ctl pad «meta» p H tag : ℕ) : Term w 0 1 :=
  (LiteralTable.dispatch 0 (col ctl «meta» p H tag) 4).instantiate
    (fun _ => .binary .sub (.result 0) (.literal pad))

private theorem term_budget (ctl pad «meta» p H tag : ℕ) :
    4+4*(2*(term ctl pad «meta» p H tag : Term w 0 1).binds+4) ≤ 400 := by
  have cols (j : ℕ) (hj : j<4) : (col ctl «meta» p H tag j : Term w 0 1).binds ≤ 8 := by
    interval_cases j <;>
      simp [col,Term.binary,Term.literal,Term.load,Term.binds_letThen,Term.binds_rename,Term.binds]
  have price := LiteralTable.dispatch_binds (0 : Fin 1) (col ctl «meta» p H tag : ℕ → Term w 0 1) 4 8 cols
  rw [term,Term.binds_instantiate,Fin.sum_univ_one]
  simp only [Term.binary,Term.literal,Term.binds_letThen,Term.binds_rename,Term.binds]
  omega

def program (w ctl pad «meta» p H tag : ℕ) : Procedure w :=
  PhysicalInputPhases.writing (term ctl pad «meta» p H tag) Fin.elim0 pad 4

/-- Rows and hidden variables come exclusively from the just-completed selected
concatenation cursor. All ordinary external locations outside the four output words survive. -/
theorem run (ctl pad «meta» p H tag cells hidden : ℕ)
    (fit : pad+4<2^w) (ctrl : ctl+3<2^w) (below : hidden≤H)
    (apart : ctl+4≤pad ∨ pad+4≤ctl) :
    (program w ctl pad «meta» p H tag).Spec
      (fun m => m (ctl+2)=(cells:Word w) ∧ m (ctl+3)=(hidden:Word w))
      (fun m out => (∀ j : Fin 4, HistoryPadDriver.header (pad:Word w) out j =
        ![(«meta»+4*cells:ℕ),(H-hidden:ℕ),(2+p+hidden:ℕ),(tag:Word w)] j) ∧
        ∀ x,x<pad ∨ pad+4≤x → out x=m x) 400 := by
  let words : Fin 4 → Word w := ![(«meta»+4*cells:ℕ),(H-hidden:ℕ),(2+p+hidden:ℕ),(tag:Word w)]
  let word := fun x => words ⟨(x-pad)%4,Nat.mod_lt _ (by decide)⟩
  have gen : (program w ctl pad «meta» p H tag).Spec
      (fun m => m (ctl+2)=(cells:Word w) ∧ m (ctl+3)=(hidden:Word w))
      (fun m out => out=fillSegment pad 4 word m)
      (4+4*(2*(term ctl pad «meta» p H tag : Term w 0 1).binds+4)) :=
    PhysicalInputPhases.writing_spec (term ctl pad «meta» p H tag) Fin.elim0 pad 4 fit
    (fun m => m (ctl+2)=(cells:Word w) ∧ m (ctl+3)=(hidden:Word w)) word (by
      rintro m₀ ⟨cn,hn⟩ addr m lo hi same
      let j := addr.val-pad
      have bound : j<4 := by dsimp [j]; omega
      have off : addr-(pad:Word w)=(j:Word w) := by
        change _=((addr.val-pad:ℕ):Word w)
        rw [Nat.cast_sub lo,Fin.cast_val_eq_self]
      have c2 : m ((ctl+2:ℕ):Word w).val=(cells:Word w) := by
        rw [Fin.val_cast_of_lt (show ctl+2<2^w by omega),same _ (by rcases apart with h|h <;> omega),cn]
      have c3 : m ((ctl+3:ℕ):Word w).val=(hidden:Word w) := by
        rw [Fin.val_cast_of_lt ctrl,same _ (by rcases apart with h|h <;> omega),hn]
      have add2 : m ((ctl:Word w)+2).val=(cells:Word w) := by simpa only [Nat.cast_add,Nat.cast_ofNat] using c2
      have add3 : m ((ctl:Word w)+3).val=(hidden:Word w) := by simpa only [Nat.cast_add,Nat.cast_ofNat] using c3
      rw [term,Term.eval_instantiate,LiteralTable.dispatch_eval 0 _ 4 j bound (by omega) _ _ _ (by exact off)]
      change (col ctl «meta» p H tag j).eval _ _ _=words ⟨j%4,_⟩
      have key : (⟨j%4,Nat.mod_lt _ (by decide)⟩ : Fin 4)=⟨j,bound⟩ :=
        Fin.ext (Nat.mod_eq_of_lt bound)
      rw [key]
      interval_cases j <;> simp [col,words,Term.eval,Term.eval_binary,Term.eval_literal,Term.eval_load,BinaryOp.eval,
        add2,add3,Nat.cast_add,Nat.cast_mul,Nat.cast_sub below])
  intro P R K M pc reg pub exit installed rom cfg m entry input
  obtain ⟨t,time,endCfg,out,run,atExit,image⟩ := gen M pc reg pub exit installed rom cfg m entry input
  refine ⟨t,time.trans ?_,endCfg,out,run,atExit,?_⟩
  · exact term_budget ctl pad «meta» p H tag
  subst out
  constructor
  · intro j
    have hj := j.isLt
    have addr : ((pad:Word w)+(j.val:Word w)).val=pad+j.val := by
      rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    unfold HistoryPadDriver.header
    rw [addr]
    have inside : pad≤pad+j.val ∧ pad+j.val<pad+4 := by omega
    simp only [fillSegment,ite_eq_left inside,word,Nat.add_sub_cancel_left,Nat.mod_eq_of_lt hj]
    fin_cases j <;> simp [words]; exact (Fin.cast_val_eq_self (tag : Word w)).symm
  · intro x h
    simp [fillSegment, show ¬(pad≤x ∧ x<pad+4) by omega]

end ThreeFlat.RAM.SelectedPadHeader

end
end OAI
