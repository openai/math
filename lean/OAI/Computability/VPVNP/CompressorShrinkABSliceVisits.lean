import OAI.Computability.VPVNP.CompressorShrinkABSliceRecipe
import OAI.Computability.VPVNP.CompressorShrinkABSliceProgress
import OAI.Computability.VPVNP.CompressorFlatRowScan
import OAI.Computability.VPVNP.LiveHeaderProtectedCore

/-! # Native whole-bundle segments of the AB calendar -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkABSliceRecipe

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM BlockPlanner
open ShrinkABSliceTable IndexedStarts SliceRAM

variable {w m n rows first : ℕ}

/-- The local worker template executed at this AB stage before compilation into a whole-bundle
scan. -/
def Stage.pass : Stage m n → Schedule.Pass
  | .clear _ => ⟨_,_,_,template clearOps 0⟩
  | .pair _ => ⟨_,_,_,IndexedPair.table⟩
  | .refs _ => ⟨_,_,_,adjTemplate⟩

/-- The fixed endpoint or field-pair index that this stage processes at every bundle. -/
def Stage.localIdx : Stage m n → ℕ | .clear i | .pair i | .refs i => i.val
/-- Local call fuel for an AB stage, with 8 steps for clearing, 38 for a field pair and 36 for
references. -/
def Stage.fuel : Stage m n → ℕ | .clear _ => 8 | .pair _ => 38 | .refs _ => 36

/-- Select the clear, intersection or reference operand expressions for the stage's local
worker. -/
def Stage.affineParams (I : Inputs) : (j : Stage m n) → Fin j.pass.params → Affine
  | .clear _ => clearParams I m n
  | .pair _ => pairParams I m n
  | .refs _ => refParams I m n

/-- The local worker's concrete operand words for a single bundle, using its actual input
columns and bank address. -/
def Stage.data (t p : Fin 5 → Word w) (i : Fin rows) (first : ℕ) : (j : Stage m n) → Fin j.pass.params → Word w
  | .clear _ => fun _ => bank first m n i.val
  | .pair _ => IndexedStarts.pair (columns t p i.val) (bank first m n i.val) m n
  | .refs _ => IndexedStarts.adj (bank first m n i.val) m n

private theorem stage_flat (I : Inputs) (j : Stage m n) :
    stage I j = flat j.pass.table I (j.affineParams I) j.localIdx := by cases j <;> rfl

/-- Executing the stage's flat worker from zero with one empty choice stream per bundle
produces the specified source reports. -/
def Source (I : Inputs) (pub : Fin 5 → Word w) (state : Word w) (ref : Memory w) (rows cap : ℕ)
    (j : Stage m n) (mem : Memory w) (rs : List (Report w)) : Prop :=
  let v := stage I j
  let M := v.worker.table.instantiate w (fun a => (v.params a).eval pub state ref)
  runSegment M.program cap (some 0) mem (List.replicate rows []) = some rs

variable (I : Inputs) (pub : Fin 5 → Word w) (state : Word w) (ref : Memory w)
variable {t p : Fin 5 → Word w} (L : Layout t p rows m n first) (D : Describes I pub state ref t p rows first)

open scoped Fin.CommRing

include L D

private theorem local_data (j : Stage m n) (i : Fin rows) (mem : Memory w) :
    (fun x : Fin j.pass.params =>
      FlatRows.value (fun _ => false) (evaluated pub state ref (j.affineParams I) j.localIdx)
        (i.val : Word w) mem x.castSucc) = j.data t p i first := by
  cases j with
  | clear v => exact clear_operands I pub state ref D _ _ _ _ _
  | pair v => exact pair_operands I pub state ref D L _ _ _
  | refs v => exact refs_operands I pub state ref D L _ _ _

open private local_val from OAI.Computability.VPVNP.CompressorShrinkABSliceRecipe

/-- Lifting one local instruction-table execution to the calendar's global
bundle cursor preserves its entire memory effect. -/
theorem one (j : Stage m n) (i : Fin rows) (mem : Memory w) (cap : ℕ) (hcap : 95 ≤ cap) (r : Report w)
    (run : let M := j.pass.table.instantiate w (j.data t p i first)
      execute M.program j.fuel (M.program.start (j.localIdx : Word w)) mem [] = some r)
    (ret : r.result.isSome) :
    let v := stage I j
    let P := (v.worker.table.instantiate w (fun a => (v.params a).eval pub state ref)).program
    ∃ s, execute P cap (P.start (i.val : Word w)) mem [] = some s ∧
      s.result = some (Fin.ofNat _ (i.val+1)) ∧ after mem s.events = after mem r.events := by
  rw [stage_flat]
  let a := evaluated pub state ref (j.affineParams I) j.localIdx
  let row : Word w := i.val
  let t' := FlatRows.events (fun _ => false) a row mem
  let flatProg := ((FlatRows.compile j.pass.table (fun _ => false)).instantiate w a).program
  let s' : Report w := ⟨t'++r.events, some (row+1)⟩
  change ∃ s, execute flatProg cap (flatProg.start row) mem [] = some s ∧ _ ∧ _
  have ld := local_data I pub state ref L D j i mem
  have result := FlatRows.execute_flat j.pass.table (fun _ => false) a row mem [] j.fuel
  dsimp only at result
  rw [ld,local_val pub state ref (j.affineParams I) j.localIdx row mem,run,Option.map_some] at result
  have hs : r.result.map (fun _ => row+1) = some (row+1) := by
    cases hr : r.result <;> simp [hr] at ret ⊢
  rw [hs] at result
  have hlim : j.fuel+(3+7*(j.pass.params+1)) ≤ cap := by
    cases j <;> dsimp [Stage.fuel,Stage.pass] <;> omega
  have hdone := execute_extend result (cap-(j.fuel+(3+7*(j.pass.params+1))))
  rw [Nat.add_sub_of_le hlim] at hdone
  refine ⟨s',hdone,?_,?_⟩
  · apply congrArg some
    change (i.val : Word w)+1 = ((i.val+1 : ℕ) : Word w)
    push_cast; rfl
  · have hm := (FlatRows.events_cost (fun _ => false) a row mem).2.2.1
    change List.foldl update mem (t'++r.events) = _
    rw [List.foldl_append,show List.foldl update mem t' = mem from hm]; rfl

omit D

/-- Distinct bundle ordinals have disjoint output banks, including when the
fixed shape has zero occupied fields. -/
theorem banks_disjoint {i j : Fin rows} (h : i ≠ j) (x : ℕ)
    (hx : BankAt (bank (w := w) first m n i.val) m n x) :
    ¬ BankAt (bank (w := w) first m n j.val) m n x := by
  intro hy
  have hn : i.val ≠ j.val := fun eqn => h (Fin.ext eqn)
  simp only [BankAt,bank_val L i,bank_val L j] at hx hy
  rcases lt_or_gt_of_ne hn with hlt | hlt
  · have h := Nat.mul_le_mul_right (capacity m n) hlt
    rw [Nat.succ_mul] at h; omega
  · have h := Nat.mul_le_mul_right (capacity m n) hlt
    rw [Nat.succ_mul] at h; omega

include D

/-- Every whole-level visit threads actual native reports through the banks
and preserves the shared inputs. -/
theorem phase_run (j : Stage m n) (cap : ℕ) (hcap : 95 ≤ cap)
    (shared : Memory w → Prop) (before done : Fin rows → Memory w → Prop)
    (keepShared : ∀ i : Fin rows, ∀ mem out, shared mem →
      (∀ x, ¬ BankAt (bank (w := w) first m n i.val) m n x → out x = mem x) → shared out)
    (keepB : ∀ i mem out, before i mem →
      (∀ x, BankAt (bank (w := w) first m n i.val) m n x → out x = mem x) → before i out)
    (keepD : ∀ i mem out, done i mem →
      (∀ x, BankAt (bank (w := w) first m n i.val) m n x → out x = mem x) → done i out)
    (localStep : ∀ i : Fin rows, ∀ mem, shared mem → before i mem →
      let M := j.pass.table.instantiate w (j.data t p i first)
      ∃ r, execute M.program j.fuel (M.program.start (j.localIdx : Word w)) mem [] = some r ∧
        r.result.isSome ∧ done i (after mem r.events) ∧
        ∀ x, ¬ BankAt (bank (w := w) first m n i.val) m n x → after mem r.events x = mem x)
    (mem : Memory w) (hs : shared mem) (hb : ∀ i, before i mem) :
    ∃ rs, Source I pub state ref rows cap j mem rs ∧ shared (after mem (eventLog rs)) ∧
      ∀ i, done i (after mem (eventLog rs)) := by
  let v := stage I j
  let P := (v.worker.table.instantiate w (fun a => (v.params a).eval pub state ref)).program
  have worker (i : Fin rows) (st : Memory w) (h₁ : shared st) (h₂ : before i st) :
      ∃ r, execute P cap (P.start (Fin.ofNat _ i.val)) st [] = some r ∧
        r.result = some (Fin.ofNat _ (i.val+1)) ∧ shared (after st r.events) ∧ done i (after st r.events) ∧
        ∀ x, ¬ BankAt (bank (w := w) first m n i.val) m n x → after st r.events x = st x := by
    obtain ⟨r,run,ret,hd,frame⟩ := localStep i st h₁ h₂
    obtain ⟨s,hr,hc,hm⟩ := one I pub state ref L D j i st cap hcap r run ret
    exact ⟨s,hr,hc,hm ▸ keepShared i st _ h₁ frame,hm ▸ hd,hm ▸ frame⟩
  obtain ⟨rs,run,_,_,hs',hd,_⟩ := FlatRows.scan P cap rows shared (fun i => BankAt (bank first m n i.val) m n)
    (banks_disjoint L) before done keepB keepD worker mem hs hb
  exact ⟨rs,run,hs',hd⟩

end CompressorRecords.ShrinkABSliceRecipe

end VPVNP
end Computability
end OAI
