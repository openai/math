import OAI.Computability.NearSquareRoot.InterchangeROMTableCommand
import OAI.Computability.NearSquareRoot.InterchangeSpectralStep

/-! # From three-way comparison marks to the repair ROM mask

A field order can be any permutation of the main comparisons. The committed
bit number for each physical position is an explicit entry in the instruction.
Only a greater-than comparison sets its bit in the little-endian sign mask.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMTable

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open InterchangeROMRepair GeneratorSyntax

def comparisonCode : Ordering → Fin 3
  | .lt => 0
  | .eq => 1
  | .gt => 2

/-- The same three physical marks used by the individual spectral sweep. -/
def comparisonMark (a : Fin 3) : Tree :=
  if a = 0 then .atom false else if a = 1 then .atom true else .fork (.atom false) (.atom false)

private theorem comparisonMark_inj : Function.Injective comparisonMark := by
  intro x y
  fin_cases x <;> fin_cases y <;> decide

def maskValue (positions : List ℕ) (word : List (Fin 3)) : ℕ :=
  ∑ k ∈ Finset.range positions.length,
    (if word.getD k 0 = 2 then 1 else 0) * 2^(positions.getD k 0)

theorem primrec_maskValue : Primrec₂ maskValue := by
  apply KernelComputableAddress.primrec_rangeSum (Primrec.list_length.comp Primrec.fst)
  have hpos : Primrec (fun v : (List ℕ × List (Fin 3)) × ℕ => v.1.1.getD v.2 0) := (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hcode : Primrec (fun v : (List ℕ × List (Fin 3)) × ℕ => v.1.2.getD v.2 0) := (Primrec.list_getD (0 : Fin 3)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact (Primrec.nat_mul.comp (Primrec.ite (Primrec.eq.comp hcode (Primrec.const 2))
    (Primrec.const 1) (Primrec.const 0)) (KernelComputableAddress.primrec_pow (Primrec.const 2) hpos)).to₂

private theorem tab_getD {K A : Type} (s : Series K) (v : K → A) (d : A) (i : Fin s.count) :
    (s.tab v).getD i.val d = v (s.follow i) := by
  have h : i.val < (s.tab v).length := by simp
  rw [List.getD_eq_getElem _ _ h, s.get v i h, Series.index_symm]

theorem maskValue_tab {m : ℕ} (order : Series (Fin m)) (v : Fin m → Ordering) :
    maskValue (order.tab Fin.val) (order.tab (comparisonCode ∘ v)) =
      (Raw.mask (fun j => decide (v j = .gt))).val := by
  change _ = (finFunctionFinEquiv (fun j : Fin m => finTwoEquiv.symm (decide (v j = .gt))) : ℕ)
  rw [finFunctionFinEquiv_apply,maskValue,Series.card,← Fin.sum_univ_eq_sum_range]
  simp_rw [tab_getD]
  calc
    _ = ∑ j : Fin m, (if (comparisonCode ∘ v) j = 2 then 1 else 0) * 2^j.val :=
      order.index.symm.sum_comp (fun j => (if (comparisonCode ∘ v) j = 2 then 1 else 0) * 2^j.val)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      cases h : v j <;> simp [h,comparisonCode,finTwoEquiv]

def comparisonTable (positions : List ℕ) :=
  literal ([0,1,2] : List (Fin 3)) positions.length comparisonMark fun w => numeral (maskValue positions w)

theorem effective_comparisonCommand {X : Type} [Primcodable X] {pos : X → List ℕ} (hp : Computable pos) :
    Effective ltr (fun x => RegisterTable.command (comparisonTable (pos x))) := by
  apply RegisterTable.effective
  apply computable_spelled_literal (letter := fun _ => comparisonMark) (Computable.const _)
    (Computable.list_length.comp hp) ((Primrec.dom_finite (fun v => spelling (comparisonMark v))).to_comp.comp Computable.snd).to₂
  exact (primrec_spelling_numeral.to_comp.comp
    (primrec_maskValue.to_comp.comp (hp.comp Computable.fst) Computable.snd)).to₂

theorem comparisonTable_correct {m : ℕ} (order : Series (Fin m)) (v : Fin m → Ordering) :
    let t := comparisonTable (order.tab Fin.val)
    let u := stripe order (comparisonMark ∘ comparisonCode ∘ v)
    let y := numeral (Raw.mask (fun j => decide (v j = .gt))).val
    RegisterLookup.read t u = y ∧ (u,y) ∈ t := by
  have all (a : Fin 3) : a ∈ ([0,1,2] : List (Fin 3)) := by fin_cases a <;> decide
  have h := literal_correct ([0,1,2] : List (Fin 3)) (order.tab Fin.val).length comparisonMark
    comparisonMark_inj (fun w => numeral (maskValue (order.tab Fin.val) w))
    (order.tab (comparisonCode ∘ v)) (by simp) (fun a _ => all a)
  rw [maskValue_tab] at h
  simpa only [comparisonTable,Series.tab,Task.forest_map,stripe_simple,Function.comp_def] using h

theorem direction_flag {A : Type} [LinearOrder A] (early late : A) :
    decide (InterchangeSpectralStep.direction early late = .gt) = decide (late < early) := by
  rcases lt_trichotomy early late with h | h | h
  · simp [InterchangeSpectralStep.direction,h,ne_of_lt h,not_lt_of_gt h]
  · simp [InterchangeSpectralStep.direction,h]
  · simp [InterchangeSpectralStep.direction,h,ne_of_gt h,not_lt_of_gt h]

theorem comparisonCommand_run {m : ℕ} (order : Series (Fin m)) (v : Fin m → Ordering)
    (env : Env) (r : Deck) :
    let t := comparisonTable (order.tab Fin.val)
    Fits env (RegisterTable.command t)
      (pile 0 (stripe order (comparisonMark ∘ comparisonCode ∘ v)) r)
      (pile 0 (numeral (Raw.mask (fun j => decide (v j = .gt))).val) r) (RegisterTable.cost t) := by
  have h := comparisonTable_correct order v
  exact RegisterTable.run_lookup _ _ _ h.2 h.1 env r

end InterchangeROMTable

end NearSquareRoot
end Computability
end OAI
