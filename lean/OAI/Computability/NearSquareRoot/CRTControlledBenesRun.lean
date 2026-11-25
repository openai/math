import OAI.Computability.NearSquareRoot.CRTControlledBenesCompiler
import OAI.Computability.NearSquareRoot.CRTControlledBenesSplit

/-! # Correctness of the switch decisions produced by the charged table compiler

The first column is consumed from the root to the leaves. The second is consumed
in the opposite order. At each layer the row is indexed by the current address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes
open IntegerMultiplication.Code

/-- Both switch bits are indexed by the other bits of the current address. -/
def rawSetting (t : RawTable) (j : ℕ) (x : List Bool) : Bool × Bool :=
  (switchRow ((t,tally j),x)).2

theorem rawSetting_cons_zero (t : RawTable) (b : Bool) (x : List Bool) :
    rawSetting t 0 (b::x) = decisions ((t,[]),x) := by
  simp [rawSetting,switchRow]

theorem rawSetting_cons_succ (t : RawTable) (b : Bool) (x : List Bool) (j : ℕ) :
    rawSetting t (j+1) (b::x) = rawSetting (childTable t b) j x := by
  simp [rawSetting,switchRow,decisions,descend]

/-- Replacing the target bit preserves both columns, for every pair of surrounding
bit strings. This also covers the last (empty-suffix) switch. -/
theorem rawSetting_independent (t : RawTable) (pre suf : List Bool) (b c : Bool) :
    rawSetting t pre.length (pre ++ b :: suf) = rawSetting t pre.length (pre ++ c :: suf) := by
  simp [rawSetting,switchRow]

theorem rawSetting_set (t : RawTable) (x : List Bool) (j : ℕ) (b : Bool) :
    rawSetting t j (x.set j b) = rawSetting t j x := by
  induction x generalizing t j with
  | nil => simp
  | cons a l ih => cases j <;> simp [rawSetting_cons_zero,rawSetting_cons_succ,ih]

def applyRawStage (t : RawTable) (side : Bool) (j : ℕ) (x : List Bool) : List Bool :=
  let c := rawSetting t j x
  x.modify j (· ^^ (if side then c.2 else c.1))

/-- Apply the left stages in ascending depth and the right stages in descending depth. -/
def runDepths (stage : Bool → ℕ → List Bool → List Bool) (d : ℕ) (x : List Bool) : List Bool :=
  let stages := List.range d
  stages.reverse.foldl (fun x j => stage true j x)
    (stages.foldl (fun x j => stage false j x) x)

def rawStages (t : RawTable) := runDepths (applyRawStage t)

private theorem stage_zero (t : RawTable) (side b : Bool) (x : List Bool) :
    applyRawStage t side 0 (b :: x) = (b ^^ (label (rawLabels t) (side,x)).2) :: x := by
  cases side <;> simp [applyRawStage,rawSetting_cons_zero,decisions,descend]

private theorem stage_succ (t : RawTable) (side b : Bool) (x : List Bool) (j : ℕ) :
    applyRawStage t side (j+1) (b::x) = b :: applyRawStage (childTable t b) side j x := by
  simp [applyRawStage,rawSetting_cons_succ]

private theorem fold_succ (t : RawTable) (side b : Bool) (x : List Bool) (js : List ℕ) :
    (js.map Nat.succ).foldl (fun w j => applyRawStage t side j w) (b::x) =
      b :: js.foldl (fun w j => applyRawStage (childTable t b) side j w) x := by
  induction js generalizing x with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons,List.foldl_cons,stage_succ,ih]

/-- Peeling the global ascending/descending schedule makes exactly one recursive
call on the selected lane. -/
theorem rawStages_cons (t : RawTable) (d : ℕ) (b : Bool) (x : List Bool) :
    rawStages t (d+1) (b::x) =
      let lane := b ^^ (label (rawLabels t) (false,x)).2
      let y := rawStages (childTable t lane) d x
      (lane ^^ (label (rawLabels t) (true,y)).2) :: y := by
  simp only [rawStages,runDepths,List.range_succ_eq_map (n:=d),List.reverse_cons,
    ← List.map_reverse,List.foldl_append,List.foldl_cons,List.foldl_nil,stage_zero,fold_succ]

theorem rawStages_run {d : ℕ} (p : Equiv.Perm (Word d)) (t : RawTable)
    (h : RawRepresents p t) (x : Word d) :
    rawStages t d (List.ofFn x) = List.ofFn (p x) := by
  induction d generalizing t with
  | zero => simp [rawStages,runDepths]
  | succ d ih =>
    obtain ⟨q,hq,hp⟩ := raw_split_correct p t h
    let b := x 0
    let z : Word d := Fin.tail x
    let lane := b ^^ rawControl t false z
    have ex : Fin.cons b z = x := Fin.cons_self_tail x
    rw [← ex,List.ofFn_cons,rawStages_cons,hp,List.ofFn_cons]
    change ((_ ^^ (label _ (true,rawStages (childTable t lane) d (List.ofFn z))).2) ::
      rawStages (childTable t lane) d (List.ofFn z)) = _
    rw [ih (q lane) (childTable t lane) (hq lane) z]
    rfl

/-- Evaluate one emitted layer directly, indexing the stored rows by the current word. -/
def readStage (tables : List (List (List Bool × Bool × Bool))) (side : Bool) (j : ℕ)
    (x : List Bool) : List Bool :=
  let c := (tables[j]?.bind (fun rows => rows.lookup x)).getD (false,false)
  x.modify j (· ^^ (if side then c.2 else c.1))

private theorem key_mem {d : ℕ} {p : Equiv.Perm (Word d)} {t : RawTable}
    (h : RawRepresents p t) (x : List Bool) (hx : x.length = d) : x ∈ t.map Prod.fst := by
  subst d
  obtain ⟨ks,_,hall,rfl⟩ := h
  simpa only [List.map_map,Function.comp_def] using
    (List.mem_map.mpr ⟨x.get,hall _,List.ofFn_get x⟩ : x ∈ ks.map List.ofFn)

theorem readStage_generated {d : ℕ} {p : Equiv.Perm (Word d)} {t : RawTable}
    (h : RawRepresents p t) (x : List Bool) (hx : x.length = d) (side : Bool)
    {j : ℕ} (hj : j < d) :
    readStage (generateTables (tally d,t)) side j x = applyRawStage t side j x := by
  simp [readStage,applyRawStage,rawSetting,generated_lookup t hj x (key_mem h x hx)]

private theorem fold_generated {d : ℕ} {p : Equiv.Perm (Word d)} {t : RawTable}
    (h : RawRepresents p t) (x : List Bool) (hx : x.length = d) (side : Bool)
    (js : List ℕ) (hj : ∀ j ∈ js, j < d) :
    js.foldl (fun w j => readStage (generateTables (tally d,t)) side j w) x =
    js.foldl (fun w j => applyRawStage t side j w) x := by
  induction js generalizing x with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [readStage_generated h x hx side (hj _ (by simp))]
    exact ih _ (by simpa [applyRawStage] using hx) fun k hk => hj k (by simp [hk])

private theorem fold_stage_length (t : RawTable) (side : Bool) (js : List ℕ) (x : List Bool) :
    (js.foldl (fun w j => applyRawStage t side j w) x).length = x.length := by
  induction js generalizing x with
  | nil => rfl
  | cons j js ih => rw [List.foldl_cons, ih]; simp [applyRawStage]

/-- Looking up both halves of the emitted tables sends every input address to its
specified output address. The intermediate addresses also index the original tables. -/
theorem generatedStages_run {d : ℕ} (p : Equiv.Perm (Word d)) (t : RawTable)
    (h : RawRepresents p t) (x : Word d) :
    runDepths (readStage (generateTables (tally d,t))) d (List.ofFn x) = List.ofFn (p x) := by
  rw [← rawStages_run p t h x]
  simp only [rawStages,runDepths]
  rw [fold_generated h (List.ofFn x) (by simp) false (List.range d) (by simp)]
  apply fold_generated h
  · simp [fold_stage_length]
  · simp

private def stageWord {d : ℕ} (t : RawTable) (side : Bool) (j : ℕ) (x : Word d) : Word d :=
  fun k => (applyRawStage t side j (List.ofFn x))[k.val]'(by simp [applyRawStage])

private theorem ofFn_stageWord {d : ℕ} (t : RawTable) (side : Bool) (j : ℕ) (x : Word d) :
    List.ofFn (stageWord t side j x) = applyRawStage t side j (List.ofFn x) := by
  apply List.ext_getElem <;> simp [stageWord,applyRawStage]

private theorem rawStage_involutive (t : RawTable) (side : Bool) (j : ℕ) :
    Function.Involutive (applyRawStage t side j) := by
  intro x
  induction x generalizing t j with
  | nil => simp [applyRawStage]
  | cons a x ih =>
    cases j with
    | zero => simp [stage_zero]
    | succ j => simp only [stage_succ,ih]

/-- Every emitted layer gives a self-inverse switch permutation. Axes past the
block's width act as the identity, allowing synchronized layers on different widths. -/
def stagePerm {d : ℕ} (t : RawTable) (side : Bool) (j : ℕ) : Equiv.Perm (Word d) :=
  let hi : Function.Involutive (stageWord (d := d) t side j) := fun x =>
    List.ofFn_injective (by rw [ofFn_stageWord,ofFn_stageWord,rawStage_involutive])
  ⟨stageWord t side j,stageWord t side j,hi,hi⟩

theorem ofFn_stagePerm {d : ℕ} (t : RawTable) (side : Bool) (j : ℕ) (x : Word d) :
    List.ofFn (stagePerm t side j x) = applyRawStage t side j (List.ofFn x) :=
  ofFn_stageWord t side j x

theorem stagePerm_apply {d : ℕ} (t : RawTable) (side : Bool) (j : ℕ) (x : Word d) (k : Fin d) :
    stagePerm t side j x k =
      let c := rawSetting t j (List.ofFn x)
      if j = k.val then x k ^^ (if side then c.2 else c.1) else x k := by
  simp [stagePerm,stageWord,applyRawStage,List.getElem_modify]

theorem rawSetting_update {d : ℕ} (t : RawTable) (j : Fin d) (x : Word d) (b : Bool) :
    rawSetting t j (List.ofFn (Function.update x j b)) = rawSetting t j (List.ofFn x) := by
  rw [← rawSetting_set t (List.ofFn x) j b]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [List.getElem_set,Function.update_apply,Fin.ext_iff,eq_comm]

theorem stagePerm_selfInverse {d : ℕ} (t : RawTable) (side : Bool) (j : ℕ) :
    (stagePerm (d:=d) t side j).symm = stagePerm t side j := rfl

theorem ofFn_readStagePerm {d : ℕ} {p : Equiv.Perm (Word d)} {t : RawTable}
    (h : RawRepresents p t) (side : Bool) {j : ℕ} (hj : j < d) (x : Word d) :
    List.ofFn (stagePerm t side j x) =
      readStage (generateTables (tally d,t)) side j (List.ofFn x) := by
  rw [ofFn_stagePerm,readStage_generated h _ (by simp) side hj]

theorem stagePerm_past_end {d : ℕ} (t : RawTable) (side : Bool) {j : ℕ} (hj : d ≤ j)
    (x : Word d) : stagePerm t side j x = x := by
  apply List.ofFn_injective
  rw [ofFn_stagePerm]
  exact List.modify_eq_self (by simpa using hj)

/-- Width-uniform sequence of input and output switch layers. -/
def executionOrder (d : ℕ) : List (Bool × ℕ) :=
  (List.range d).map (false, ·) ++ (List.range d).reverse.map (true, ·)

@[simp] theorem executionOrder_length (d : ℕ) : (executionOrder d).length = 2*d := by
  simp [executionOrder,two_mul]

private theorem ofFn_foldPerm {d : ℕ} (t : RawTable) (l : List (Bool × ℕ)) (x : Word d) :
    List.ofFn (l.foldl (fun w a => stagePerm t a.1 a.2 w) x) =
      l.foldl (fun w a => applyRawStage t a.1 a.2 w) (List.ofFn x) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons,ih,ofFn_stagePerm]

theorem stagesPerm_run {d : ℕ} (p : Equiv.Perm (Word d)) (t : RawTable)
    (h : RawRepresents p t) (x : Word d) :
    (executionOrder d).foldl (fun w a => stagePerm t a.1 a.2 w) x = p x := by
  apply List.ofFn_injective
  rw [ofFn_foldPerm]
  simpa only [executionOrder,List.foldl_append,List.foldl_map,rawStages,runDepths]
    using rawStages_run p t h x

theorem stagesPerm_padded_run {d : ℕ} (p : Equiv.Perm (Word d)) (t : RawTable)
    (h : RawRepresents p t) (x : Word d) (D : ℕ) (hD : d ≤ D) :
    (executionOrder D).foldl (fun w a => stagePerm t a.1 a.2 w) x = p x := by
  induction D, hD using Nat.le_induction with
  | base => exact stagesPerm_run p t h x
  | succ D hD ih =>
    simpa only [executionOrder,List.range_succ,List.reverse_append,List.reverse_singleton,
      List.map_append,List.map_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil,
      stagePerm_past_end t _ hD] using ih

end Benes

end NearSquareRoot
end Computability
end OAI
