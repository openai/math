import OAI.Computability.MultitapeWeakETH.ShrinkSiteArguments
import OAI.Computability.MultitapeWeakETH.SiteCheck

/-! # Acceptance and labels of the ordered list of resident map results -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication Code VPVNP Compression Compression.ShrinkMotif PairSimulation
open LocalHistory CompressorRecords ShrinkBlockInputs MapResidentRows MotifGrid MotifBlocks MotifConversion
noncomputable section

set_option allowUnsafeReducibility true in
attribute [local reducible] Compression.PackingData.shrinkTermLayout
set_option allowUnsafeReducibility true in
attribute [local irreducible] Compression.ShrinkEnergy.chosenLayout ShrinkRole.MapWitness.names ShrinkRole.MapWitness.input

def checked (rows : List (Option (List Tally))) :=
  bif rows.any Option.isNone then none else some ((rows.map (fun x => x.getD [])).flatten)

theorem checked_poly : Poly checked := by
  let isNone := (NearSquareRoot.PhaseTable.easyOption true (fun _ : List Tally => false) (Easy.const false)).poly
  have bad : Poly (fun xs : List (Option (List Tally)) => xs.any Option.isNone) := by
    apply CNFNetwork.SiteCheck.any_poly
    convert isNone using 1
    funext x
    cases x <;> rfl
  have values : Poly (fun x : Option (List Tally) => x.getD []) := by
    convert (NearSquareRoot.PhaseTable.easyOption ([] : List Tally) id Easy.identity).poly using 1
    funext x
    cases x <;> rfl
  exact Poly.choose bad (Code.Poly.const none) (((Poly.maps _ values).compose Easy.flatten.poly).compose Easy.some.poly)

theorem checked_pass (rows : List (Option (List Tally))) :
    (checked rows).isSome = true ↔ ∀ r ∈ rows, r.isSome = true := by
  cases bad : rows.any Option.isNone
  · simp only [checked,bad,Bool.cond_false,Option.isSome_some,true_iff]
    intro r hr
    have := List.any_eq_false.mp bad r hr
    cases r <;> simp_all
  · simp only [checked,bad,Bool.cond_true,Option.isSome_none,Bool.false_eq_true,false_iff]
    obtain ⟨r,hr,fail⟩ := List.any_eq_true.mp bad
    intro all
    have := all r hr
    cases r <;> contradiction

def rowsAt {A : Type} (n : ℕ) (run : A × Tally → Option (List Tally)) (q : A) :=
  List.ofFn fun i : Fin n => run (q,tally i.val)

theorem rowsAt_poly {A : Type} [Codec A] (n : ℕ) (run : A × Tally → Option (List Tally)) (cost : Poly run) :
    Poly (rowsAt n run) := by
  have build (js : List (Fin n)) : Poly (fun q : A => js.map (fun i => run (q,tally i.val))) := by
    induction js with
    | nil => exact Code.Poly.const []
    | cons j js ih => exact ((((Poly.identity.pair (Code.Poly.const (tally j.val))).compose cost).pair ih).compose Easy.cons.poly)
  unfold rowsAt
  simp only [List.ofFn_eq_map]
  exact build (List.finRange n)

private theorem all_rows {A L : Type} {n : ℕ} (order : Fin n ≃ A)
    (cell : A → Option (List L)) (encode : L → Tally) :
    (checked (List.ofFn fun j => (cell (order j)).map (List.map encode))).isSome = true ↔
      ∀ a, (cell a).isSome = true := by
  rw [checked_pass]
  constructor
  · intro all a
    obtain ⟨j,rfl⟩ := order.surjective a
    have mem : (cell (order j)).map (List.map encode) ∈ List.ofFn (fun i => (cell (order i)).map (List.map encode)) :=
      List.mem_ofFn.mpr ⟨j,rfl⟩
    exact Option.isSome_map.symm.trans (all _ mem)
  · intro all r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact Option.isSome_map.trans (all (order j))

private theorem checked_some (rows : List (Option (List Tally))) (h : (checked rows).isSome = true) :
    checked rows = some ((rows.map (fun x => x.getD [])).flatten) := by
  unfold checked at *
  cases flag : rows.any Option.isNone <;> simp_all

private theorem map_default {L : Type} (f : L → Tally) (x : Option (List L)) :
    (x.map (List.map f)).getD [] = (x.getD []).map f := by cases x <;> rfl

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates} {i : Fin S.steps}
  {g : ℕ} (z : SiteArguments B i g) (number : (parameterData B.shrink).Entry → ℕ)

def SiteArguments.results :=
  List.ofFn fun j : z.Row => (ShrinkRole.MapWitness.names B (z.input j)).map (List.map (tally ∘ number))

variable (f : B.Entry → R) (hf : B.IsSolution f)
local notation "W" => B.shrinkPassWitnesses f hf i rfl z.state z.choice z.owner z.old z.parent

set_option maxHeartbeats 900000 in
/-- With fixed child and hidden assignments, success of the full resident row
is equivalent to a unique extension to the scheduled kernel witness. -/
theorem SiteArguments.accepts_iff :
    (checked (z.results number)).isSome = true ↔ ∃! x : (W).Choice, x.1 = z.hidden := by
  rw [ShrinkRole.MapWitness.unique_iff B f hf i z.state z.choice z.owner z.old z.parent z.hidden]
  unfold SiteArguments.results SiteArguments.input
  exact all_rows (ShrinkRole.MapWitness.rowEquiv z.state (SelectedFinish.chosen B z.state z.choice) z.owner)
    (fun q => ShrinkRole.MapWitness.names B (ShrinkRole.MapWitness.input B i z.state z.choice z.owner z.old z.parent z.hidden q))
    (tally ∘ number)

set_option maxHeartbeats 1000000 in
/-- An accepted row emits precisely the scheduled label list, with all multiplicities. -/
theorem SiteArguments.labels (x : (W).Choice) (hx : x.1 = z.hidden) :
    checked (z.results number) = some ((ShrinkRole.MapWitness.emitted B f hf i z.state z.choice z.owner z.old z.parent x).map
      (tally ∘ number)) := by
  have present := (ShrinkRole.MapWitness.exists_iff B f hf i z.state z.choice z.owner z.old z.parent z.hidden).mp ⟨x,hx⟩
  have unique := (ShrinkRole.MapWitness.unique_iff B f hf i z.state z.choice z.owner z.old z.parent z.hidden).mpr present
  have pass := (z.accepts_iff number f hf).mpr unique
  rw [checked_some _ pass,Option.some.injEq]
  simp only [SiteArguments.results,List.map_ofFn,Function.comp_def,ShrinkRole.MapWitness.emitted,List.map_flatten]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  erw [hx]
  exact map_default _ _

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
