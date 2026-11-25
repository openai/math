import OAI.Optimization.LinearProgramming.PriceGame.LearningPathMachine

/-! # Compiling an unbounded list of observed comparisons on the bit machine

Every surviving arc is either an original bound or one of the four integer bounds computed
from a single observation. This gives a polynomial bound on every actual encoded fold
accumulator, including prefixes that are rejected later.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

/-- All possible new integer coefficients for a threshold. -/
def values {n} (o : Observation n) : List ℤ :=
  [⌈o.threshold⌉ - 1, -(⌊o.threshold⌋ + 1), ⌊o.threshold⌋, -⌊o.threshold⌋]

private theorem arc_choice {n} (d : Bounds n) (i j : Fin n) (c : ℤ) (s t : Fin n) :
    tightenArc d i j c s t = d s t ∨ tightenArc d i j c s t = c := by
  simp only [tightenArc,min_def]
  split
  · split <;> simp
  · simp

private theorem add_choice {n} (o : Observation n) {d e : Bounds n}
    (he : addObservation d o = some e) (s t : Fin n) :
    e s t = d s t ∨ e s t ∈ values o := by
  obtain ⟨i,j,θ,side⟩ := o
  cases side with
  | lt =>
    simp only [addObservation,Option.some.injEq] at he; subst e
    rcases arc_choice d j i (⌈θ⌉-1) s t with h|h
    · exact Or.inl h
    · exact Or.inr (by simp [values,h])
  | gt =>
    simp only [addObservation,Option.some.injEq] at he; subst e
    rcases arc_choice d i j (-(⌊θ⌋+1)) s t with h|h
    · exact Or.inl h
    · apply Or.inr
      rw [h]
      exact List.mem_cons_of_mem _ (List.mem_cons_self)
  | eq =>
    simp only [addObservation] at he
    split at he
    next =>
      injection he with heq; subst e
      rcases arc_choice (tightenArc d j i ⌊θ⌋) i j (-⌊θ⌋) s t with h|h
      · rw [h]
        rcases arc_choice d j i ⌊θ⌋ s t with hh|hh
        · exact Or.inl hh
        · exact Or.inr (by simp [values,hh])
      · exact Or.inr (by simp [values,h])
    next => contradiction

private theorem compiled_choice {n} (os : List (Observation n)) {d e : Bounds n}
    (he : addObservations os d = some e) (s t : Fin n) :
    e s t = d s t ∨ ∃ o ∈ os, e s t ∈ values o := by
  induction os generalizing d with
  | nil => simpa [addObservations] using congrArg (fun q => q.map (fun a => a s t)) he.symm
  | cons o os ih =>
    cases h : addObservation d o with
    | none => simp [addObservations,h] at he
    | some b =>
      simp only [addObservations,h,Option.bind_some] at he
      rcases ih he with hk|⟨y,hy,hh⟩
      · rcases add_choice o h s t with hbase|hnew
        · exact Or.inl (hk.trans hbase)
        · exact Or.inr ⟨o,by simp,hk ▸ hnew⟩
      · exact Or.inr ⟨y,by simp [hy],hh⟩

private noncomputable def valueListP {n} (e : Observation n → List Bool)
    (threshold : Procedure e ratCode (fun o => o.threshold)) : Procedure e (listCode intCode) values := by
  let floor := Procedure.ratFloor.comp threshold
  let ceil := OracleSpec.Arithmetic.ratCeil.comp threshold
  let one := Procedure.constant e intCode 1
  let first := Procedure.intSub.comp (ceil.pair one)
  let second := Procedure.intNeg.comp (Procedure.intAdd.comp (floor.pair one))
  let last := Procedure.intNeg.comp floor
  let cons := Procedure.listCons intCode
  let nil := Procedure.constant e (listCode intCode) ([] : List ℤ)
  exact cons.comp (first.pair (cons.comp (second.pair (cons.comp (floor.pair (cons.comp (last.pair nil)))))))

private theorem code_bound {α : Type} (ea : α → List Bool) (xs : List α) (b : ℕ)
    (hb : ∀ x ∈ xs, (ea x).length ≤ b) : (listCode ea xs).length ≤ xs.length*(2*b+2)+1 := by
  induction xs with
  | nil => simp [listCode]
  | cons x xs ih =>
    rw [listCode_length_cons,List.length_cons,Nat.add_mul,one_mul]
    have := hb x (by simp)
    have := ih (fun y hy => hb y (by simp [hy]))
    omega

private theorem mat_bound {n : ℕ} (d : Bounds n) (b : ℕ) (h : ∀ i j, (intCode (d i j)).length ≤ b) :
    (matrixCode intCode n d).length ≤ n*(2*(n*(2*b+2)+1)+2)+1 := by
  unfold matrixCode vecCode
  apply (code_bound _ _ (n*(2*b+2)+1) ?_).trans_eq (by simp)
  intro row hr
  rcases List.mem_ofFn.mp hr with ⟨i,rfl⟩
  apply (code_bound _ _ b ?_).trans_eq (by simp)
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨j,rfl⟩
  exact h i j

private theorem entry_le_code {n : ℕ} (d : Bounds n) (i j : Fin n) :
    (intCode (d i j)).length ≤ (matrixCode intCode n d).length := by
  apply (code_le_of_mem intCode (List.mem_ofFn.mpr ⟨j,rfl⟩ : d i j ∈ List.ofFn (d i))).trans
  exact code_le_of_mem (vecCode intCode n) (List.mem_ofFn.mpr ⟨i,rfl⟩ : d i ∈ List.ofFn d)

/-- Empty optional state propagates a discarded cell. -/
def observationStep {n} (x : Observation n × Option (Bounds n)) : Option (Bounds n) :=
  x.2.bind fun c => addObservation c x.1

private theorem fold_observations {n} (os : List (Observation n)) (b : Option (Bounds n)) :
    os.foldl (fun b o => observationStep (o,b)) b = b.bind (addObservations os) := by
  induction os generalizing b with
  | nil => cases b <;> rfl
  | cons o os ih =>
    rw [List.foldl_cons,ih]
    cases b with
    | none => rfl
    | some d => cases h : addObservation d o <;> simp [observationStep,addObservations,h]

private def asSum {α : Type} : Option α → Unit ⊕ α | none => .inl () | some a => .inr a

noncomputable def optionCasesP {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (b : β) (p : Procedure ea eb f) : Procedure (optionCode ea) eb
    (fun x => x.elim b f) := by
  let q := (Procedure.casesSum (Procedure.constant emptyCode eb b) p).precompose asSum
  exact (q.congrEncoding (fun x => by cases x <;> rfl) (fun _ => rfl)).congrFun (by intro x; cases x <;> rfl)

private noncomputable def stepP {n} (enc : Observation n → List Bool)
    (one : Procedure (prodCode enc (matrixCode intCode n)) (optionCode (matrixCode intCode n))
      (fun a => addObservation a.2 a.1)) :
    Procedure (prodCode enc (optionCode (matrixCode intCode n))) (optionCode (matrixCode intCode n))
      observationStep := by
  let m := matrixCode intCode n
  let em := optionCode m
  let input := prodCode enc em
  let item := Procedure.first enc em
  let acc := Procedure.second enc em
  let ok := (optionCasesP false (Procedure.constant m boolCode true)).comp acc
  let old := (optionCasesP (fun _ _ => (0 : ℤ)) (Procedure.identity m)).comp acc
  apply (Procedure.conditional ok (one.comp (item.pair old)) (Procedure.constant input em none)).congrFun
  rintro ⟨o,b⟩; cases b <;> rfl

/-- This construction consumes each actual historical observation, with a polynomial-clock
certificate that charges the intermediate encodings for *every* input. -/
noncomputable def foldObservationsP {p} (enc : Observation (p+1) → List Bool)
    (threshold : Procedure enc ratCode (fun o => o.threshold))
    (one : Procedure (prodCode enc (matrixCode intCode (p+1))) (optionCode (matrixCode intCode (p+1)))
      (fun a => addObservation a.2 a.1)) :
    Procedure (prodCode (listCode enc) (optionCode (matrixCode intCode (p+1))))
      (optionCode (matrixCode intCode (p+1)))
      (fun x => x.2.bind (addObservations x.1)) := by
  let n := p+1
  let m := matrixCode intCode n
  let em := optionCode m
  let vals := valueListP enc threshold
  let upper : Polynomial ℕ := Polynomial.X + vals.bound
  let clock : Polynomial ℕ := Polynomial.C n * (2 * (Polynomial.C n * (2*upper+2)+1)+2)+2
  let emptyObs : Observation (p+1) := ⟨0,0,0,.eq⟩
  have bounded (xs : List (Observation (p+1))) (b : Option (Bounds n)) (k : ℕ) :
      (em ((xs.take k).foldl (fun b o => observationStep (o,b)) b)).length ≤
        clock.eval ((listCode enc xs).length + (em b).length) := by
    let z := (listCode enc xs).length + (em b).length
    let B := z + vals.bound.eval z
    have evalClock : clock.eval z = n*(2*(n*(2*B+2)+1)+2)+2 := by
      simp [clock,upper,B]
    change _ ≤ clock.eval z
    rw [evalClock,fold_observations]
    cases hb : b with
    | none => simp [em,optionCode]
    | some d =>
      cases h : addObservations (xs.take k) d with
      | none => simp [em,optionCode,h]
      | some e =>
        have bound (i j : Fin n) : (intCode (e i j)).length ≤ B := by
          rcases compiled_choice (xs.take k) h i j with ho|⟨o,ho,hm⟩
          · rw [ho]
            apply (entry_le_code d i j).trans
            have hbnd : (m d).length ≤ (em b).length := by simp [hb,em,optionCode]
            change (matrixCode intCode n d).length ≤ (em b).length at hbnd
            dsimp [B,z]; omega
          · have ho' := List.mem_of_mem_take ho
            have he := code_le_of_mem enc ho'
            have hez : (enc o).length ≤ z := he.trans (Nat.le_add_right _ _)
            have hn := (code_le_of_mem intCode hm).trans (vals.output_length_le o)
            exact hn.trans (Nat.add_le_add hez (Procedure.eval_nat_mono vals.bound hez))
        have hlen := mat_bound e B bound
        simp only [Option.bind_some,h,em,optionCode,List.length_cons]
        change (matrixCode intCode n e).length + 1 ≤ _
        exact Nat.succ_le_succ hlen
  exact (Procedure.foldList emptyObs (stepP enc one) clock bounded).congrFun
    (fun x => fold_observations x.1 x.2)

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
