import OAI.Computability.NearSquareRoot.InterchangeROMColors

/-! # A fixed physical command for all finite color partitions

The routing input consists of Boolean source/destination mask pairs followed by
one copy of the source payload stream. The natural class numbers and the
expected destination occur only in the specification.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMColors

open IntegerMultiplication.Code Space

abbrev Tagged := List (ℕ × Tree)

structure Rows where
  source : Tagged
  target : Tagged
  lengths : source.length = target.length
  lanes : ∀ k : ℕ, Ribbon.read k source = Ribbon.read k target

def taggedMask (k : ℕ) (s : Tagged) := s.map fun z => decide (z.1 = k)

def Rows.masks (r : Rows) (k : ℕ) := (taggedMask k r.source, taggedMask k r.target)
def Rows.values (r : Rows) := r.source.map Prod.snd
def Rows.answer (r : Rows) := r.target.map Prod.snd

private def maskTags (k : ℕ) (s : Tagged) :=
  s.map fun z => (decide (z.1 = k), z.2)

private theorem read_mask (k : ℕ) (s : Tagged) :
    Ribbon.read true (maskTags k s) = Ribbon.read k s := by
  unfold Ribbon.read maskTags
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro z _
  by_cases h : z.1 = k <;> simp [Ribbon.keep, h]

theorem Rows.class_eq (r : Rows) (k : ℕ) :
    pass (r.values, r.masks k) = r.target.map (Ribbon.keep k) := by
  have agree := (read_mask k r.source).trans ((r.lanes k).trans (read_mask k r.target).symm)
  have e := pass_eq agree
  simp only [maskTags, List.map_map, Function.comp_def] at e
  rw [show r.values = r.source.map (fun z => z.2) from rfl, Rows.masks, taggedMask, taggedMask, e]
  apply List.map_congr_left
  intro z _
  by_cases h : z.1 = k <;> simp [Ribbon.keep, h]

private def partialRows (r : Rows) (ks : List ℕ) := r.target.map (Ribbon.collect ks)
private def carry (r : Rows) (ks : List ℕ) := (r.values, partialRows r ks)

private abbrev StepInput := (List Bool × List Bool) × (List Tree × List (List Tree))
private def step (i : StepInput) :=
  (i.2.1, Ribbon.unite (pass (i.2.1, i.1), i.2.2))

private theorem easy_step : Easy step := by
  have payload : Easy (fun i : StepInput => i.2.1) := by fun_prop
  exact payload.pair (Ribbon.easyUnite ((((payload.pair Easy.fst).compose pass_easy).pair
    (by fun_prop : Easy (fun i : StepInput => i.2.2)))))

private theorem step_correct (r : Rows) (k : ℕ) (ks : List ℕ) (hk : k ∉ ks) :
    step (r.masks k, carry r ks) = carry r (k :: ks) := by
  simp only [step, carry, partialRows, r.class_eq, Ribbon.collecting _ _ _ hk]

private def seed (v : List Tree) := (v, v.map fun _ => ([] : List Tree))

private theorem seed_correct (r : Rows) : seed r.values = carry r [] := by
  unfold seed carry
  apply congrArg (Prod.mk r.values)
  change (r.source.map Prod.snd).map (fun _ => ([] : List Tree)) = r.target.map (Ribbon.collect [])
  have e : Ribbon.collect (B := Tree) ([] : List ℕ) = fun _ => [] := by funext z; simp [Ribbon.collect]
  rw [e, List.map_const', List.map_const', List.length_map, r.lengths]

private theorem mask_size (s : Tagged) (k : ℕ) : size (taggedMask k s) = 2 * s.length + 1 := by
  induction s with
  | nil => rfl
  | cons z s ih => simp [taggedMask] at ih ⊢; omega

private theorem len_values (s : Tagged) : s.length ≤ size (s.map Prod.snd) := by
  induction s with
  | nil => simp
  | cons z s ih => simp; omega

private theorem partial_size (ks : List ℕ) (s : Tagged) :
    size (s.map (Ribbon.collect ks)) ≤ 3 * size (s.map Prod.snd) := by
  induction s with
  | nil => simp
  | cons z s ih =>
    by_cases h : z.1 ∈ ks <;> simp [Ribbon.collect, h] at ih ⊢ <;> omega

/-- The encoded source and destination sizes bound the work of one scan. -/
def Rows.volume (r : Rows) := size r.values + size r.answer + 1

private theorem step_size (r : Rows) (k : ℕ) (ks : List ℕ) :
    size (r.masks k, carry r ks) ≤ 10 * r.volume := by
  simp only [Rows.masks, carry, partialRows, size_prod, mask_size, Rows.volume, Rows.values, Rows.answer]
  have hs := len_values r.source
  have hd := len_values r.target
  have hp := partial_size ks r.target
  omega

private abbrev StepCase := {v : ℕ × List ℕ × Rows // (v.1 :: v.2.1).Nodup}

private theorem fold_program :
    Task (fun j : {v : List ℕ × Rows // v.1.Nodup} =>
      j.val.2.volume + Task.foldCost (fun k _ => 10*j.val.2.volume + (send (j.val.2.masks k)).count) j.val.1)
      (fun j => .fork (Task.forest (send ∘ j.val.2.masks) j.val.1) (send j.val.2.values))
      (fun j => send (carry j.val.2 j.val.1)) := by
  apply Task.foldRight (b := Rows.volume) (f := fun ks r => send (carry r ks))
    (seed := fun r => send r.values) (D := fun ks (_ : Rows) => ks.Nodup)
    (p := fun r k => send (r.masks k)) (a := fun _ _ r => 10 * r.volume)
    (fun _ _ _ h => h.of_cons)
  · have z : Easy seed := by unfold seed; fun_prop
    have e := z.on (fun j : {r : Rows // ([] : List ℕ).Nodup} => j.val.values)
    apply ((e.conform (fun _ => rfl) (fun _ => rfl) (fun j => congrArg send (seed_correct j.val)))).mono
    intro j
    unfold Rows.volume
    omega
  · have e := easy_step.on (fun j : StepCase => (j.val.2.2.masks j.val.1, carry j.val.2.2 j.val.2.1))
    apply ((e.conform (fun _ => rfl) (fun _ => rfl) (fun j =>
      congrArg send (step_correct _ _ _ (List.nodup_cons.mp j.property).1)))).mono
    intro j
    exact step_size ..

structure Batch extends Rows where
  colors : List ℕ
  distinct : colors.Nodup
  covers : ∀ z ∈ target, z.1 ∈ colors

def Batch.query (x : Batch) :=
  Tree.fork (send (x.colors.map x.masks)) (send x.values)

def Batch.work (x : Batch) := (x.colors.length + 1) * x.volume

private theorem mask_count (r : Rows) (k : ℕ) : (send (r.masks k)).count + 1 ≤ 10 * r.volume := by
  have hs := len_values r.source
  have hd := len_values r.target
  change size (r.masks k) + 1 ≤ _
  simp only [Rows.masks, size_prod, mask_size, Rows.volume, Rows.values, Rows.answer]
  omega

private theorem fold_work (r : Rows) (ks : List ℕ) :
    Task.foldCost (fun k _ => 10 * r.volume + (send (r.masks k)).count) ks ≤
      20 * (ks.length * r.volume) + 1 := by
  induction ks with
  | nil => simp [Task.foldCost]
  | cons k ks ih =>
    have h := mask_count r k
    simp only [Task.foldCost, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.mul_add]
    omega

private theorem flat_result (x : Batch) : (partialRows x.toRows x.colors).flatten = x.answer := by
  have eq : partialRows x.toRows x.colors = x.target.map (fun z => [z.2]) := by
    apply List.map_congr_left
    exact fun z hz => by simp [Ribbon.collect, x.covers z hz]
  rw [eq]
  change _ = x.target.map Prod.snd
  generalize x.target = l
  induction l with
  | nil => rfl
  | cons z l ih => simp [ih]

/-- A single machine reads the runtime mask bank, matches each class in order,
and flattens the completed destination. Its constant is independent of the
class catalog, radix, input length, address functions, and record contents. -/
theorem batch_task : Task Batch.work Batch.query (fun x => send x.answer) := by
  have fold := fold_program.on (fun x : Batch => ⟨(x.colors,x.toRows),x.distinct⟩)
  have finish : Easy (fun i : List Tree × List (List Tree) => i.2.flatten) := by fun_prop
  have done := finish.on (fun x : Batch => carry x.toRows x.colors)
  have run := fold.compose done
  refine (run.conform (fun _ => rfl) (fun x => ?_) (fun x => congrArg send (flat_result x))).bound 30 ?_
  · change Tree.fork _ (send x.values) = Tree.fork _ (send x.values)
    congr 1
    exact (Task.forest_map send x.masks x.colors).symm.trans (Task.forest_send _)
  · intro x
    have hw := fold_work x.toRows x.colors
    have hp := partial_size x.colors x.target
    dsimp only [carry, partialRows, size_prod, Batch.work]
    rw [Nat.add_mul, Nat.one_mul]
    dsimp only [Rows.volume, Rows.values, Rows.answer] at *
    omega

private theorem masks_count (r : Rows) (ks : List ℕ) :
    (Task.forest (send ∘ r.masks) ks).count ≤ 10 * (ks.length * r.volume) + 1 := by
  induction ks with
  | nil => simp [Task.forest, Tree.count]
  | cons k ks ih =>
    have h := mask_count r k
    simp only [Task.forest_cons, Function.comp_apply, Tree.count, List.length_cons,
      Nat.add_mul, Nat.one_mul, Nat.mul_add]
    omega

/-- The mask bank and the live data/return stacks fit the same uniform bound
as the total scan time. -/
theorem batch_program : BoundedTask Batch.work Batch.work Batch.query (fun x => send x.answer) := by
  apply (BoundedTask.of_time batch_task).bound 1 15
  · simp
  · intro x
    have eq := (Task.forest_map send x.masks x.colors).symm.trans (Task.forest_send _)
    have bank := masks_count x.toRows x.colors
    change Task.forest (send ∘ x.masks) x.colors = _ at eq
    rw [eq] at bank
    simp only [Batch.query, Tree.count, Batch.work, Nat.add_mul, Nat.one_mul]
    have h : (send x.values).count ≤ x.volume := by change size x.values ≤ size x.values + size x.answer + 1; omega
    omega

/-- A fixed command for every coefficient and every number of classes. -/
noncomputable def command : Cmd := batch_program.choose

theorem command_fits : ∃ C : ℕ, ∀ (x : Batch) env d base, (∀ j, (letters d j).length ≤ base) →
    BoundedFits env command (pile 0 x.query d) (pile 0 (send x.answer) d)
      (C * (x.work + 1)) (base + C * (x.work + 1)) (C * (x.work + 1)) :=
  batch_program.choose_spec

end InterchangeROMColors

end NearSquareRoot
end Computability
end OAI
