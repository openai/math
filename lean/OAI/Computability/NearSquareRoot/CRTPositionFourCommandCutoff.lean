import OAI.Computability.NearSquareRoot.CRTControlledReserveCutoff
import OAI.Computability.NearSquareRoot.PhysicalWalshParamLiterals

/-! # A named width guard for the position commands

The cutoff is emitted as a unary literal. The fixed comparison command reads
the actual table length and retains the original table and data for the
selected branch.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd

open IntegerMultiplication IntegerMultiplication.Code NearSquareRoot.Space
open CommonRegisters GeneratorSyntax EffectiveBoundedTask Filter
open Reflections (Table table)

noncomputable section

private abbrev GuardInput := (Tally × Tally) × (Table × Tree)

private def tag (z : GuardInput) : Bool × Table × Tree :=
  (Iter.small (z.1.1,z.2.1),z.2)

private theorem tag_easy : Easy tag :=
  (((Easy.fst.compose Easy.fst).pair (Easy.snd.compose Easy.fst)).compose Iter.small_easy).pair Easy.snd

private def tagCmd : Cmd := tag_easy.choose

private theorem tag_runs : EffectiveBoundedTask.Runs tagCmd (size (X := GuardInput))
    (fun z => size z + size z) send (fun z => send (tag z)) :=
  EffectiveBoundedTask.Runs.of_time tag_easy.choose_spec

/-- Test whether the table has more than `K` entries and retain the input as
the payload of the resulting tagged tree. -/
def cutoffCmd (K : ℕ) (big small : Cmd) : Cmd :=
  (PhysicalWalsh.ParamLiterals.command K 0 tagCmd).join (decodeBit small big)

private theorem reindex {P Q : Type} [Primcodable P] [Primcodable Q]
    (emit : Q → Cmd) (param : P → Q) (hc : Effective ltr emit) (hp : Computable param) :
    Effective ltr (fun p => emit (param p)) :=
  hc.comp hp

private theorem effective_test {P : Type} [Primcodable P] {K : P → ℕ}
    (core : Cmd) (hk : Computable K) :
    Effective ltr (fun p => PhysicalWalsh.ParamLiterals.command (K p) 0 core) :=
  reindex (fun v : ℕ × ℕ => PhysicalWalsh.ParamLiterals.command v.1 v.2 core)
    (fun p => (K p,0)) (PhysicalWalsh.ParamLiterals.effective core) (hk.pair (Computable.const 0))

theorem cutoff_effective {P : Type} [Primcodable P] {K : P → ℕ} {big small : P → Cmd}
    (hk : Computable K) (hb : Effective ltr big) (hs : Effective ltr small) :
    Effective ltr (fun p => cutoffCmd (K p) (big p) (small p)) := by
  apply (effective_test tagCmd hk).join
  apply KernelEffectiveFamily.effective_splitRoot _ (fun _ => effective_const _ _)
  apply KernelEffectiveFamily.effective_splitRoot _ _ (effective_const _ _)
  intro b
  cases b
  · exact hs
  · exact hb

theorem cutoff_within : ∀ᶠ R : ℕ in atTop, ∀ K big small, Within R big → Within R small →
    Within R (cutoffCmd K big small) := by
  filter_upwards [RegisterSelect.within_eventually tagCmd, eventually_gt_atTop (0 : ℕ)] with R cmd pos
  intro K big small hb hs
  refine ⟨PhysicalWalsh.ParamLiterals.within pos cmd _ _,RegisterWitness.splitRoot_within.mpr ?_⟩
  exact ⟨pos,trivial,trivial,RegisterWitness.splitRoot_within.mpr ⟨pos,hs,hb,trivial⟩⟩

/-- The physical input contains the actual permutation table next to its data. -/
def cutoffInput {I : Type} {k : I → ℕ} (p : ∀ i, Equiv.Perm (Fin (k i))) (data : I → Tree)
    (i : I) := Tree.fork (send (table (p i))) (data i)

private theorem cutoff_test {I : Type} (K : ℕ) (k T V : I → ℕ)
    (p : ∀ i, Equiv.Perm (Fin (k i))) (data : I → Tree) (room : ∀ i, V i ≤ T i)
    (C : ℕ) (count : ∀ i, (cutoffInput p data i).count ≤ C*(V i+1)) :
    EffectiveBoundedTask.Runs (PhysicalWalsh.ParamLiterals.command K 0 tagCmd) T V (cutoffInput p data)
      (fun i => .fork (.atom (decide (K < k i))) (cutoffInput p data i)) := by
  let raw (i : I) : GuardInput := ((tally K,tally 0),table (p i),data i)
  let overhead := (PhysicalWalsh.ParamLiterals.literal K 0).count
  let n i := overhead + (cutoffInput p data i).count + 1
  have run : EffectiveBoundedTask.Runs tagCmd n (fun i => n i+n i)
      (fun i => .fork (PhysicalWalsh.ParamLiterals.literal K 0) (cutoffInput p data i))
      (fun i => .fork (.atom (decide (K < k i))) (cutoffInput p data i)) := by
    have h := tag_runs.on raw
    have eq i : tag (raw i) = (decide (K < k i),table (p i),data i) := by
      simp only [tag, raw, Iter.small, tally_length, Reflections.table, List.length_ofFn]
    change EffectiveBoundedTask.Runs tagCmd n (fun i => n i+n i) _ (fun i => send (tag (raw i))) at h
    change EffectiveBoundedTask.Runs tagCmd n (fun i => n i+n i) (send ∘ raw)
      (fun i => send (decide (K < k i),table (p i),data i))
    simpa only [eq] using h
  have all := PhysicalWalsh.ParamLiterals.runs K 0 run (input := fun i => by dsimp [n]; omega)
  let D := overhead+C+2
  have sizeBound i : n i + 1 ≤ D*(V i+1) := by
    have := count i
    dsimp [n,D]
    have h := Nat.mul_le_mul_left overhead (Nat.succ_le_succ (Nat.zero_le (V i)))
    rw [Nat.mul_one] at h
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
    omega
  apply all.bound D (2*D)
  · exact fun i => (sizeBound i).trans (Nat.mul_le_mul_left D (Nat.succ_le_succ (room i)))
  · intro i
    have h := Nat.mul_le_mul_left 2 (sizeBound i)
    rw [Nat.mul_assoc]
    omega

/-- Both branches are the specified commands and are required only on their
own ranges. The comparison and decoding fit in the same time and space. -/
theorem cutoff_runs {I : Type} (K : ℕ) (k T V : I → ℕ) (p : ∀ i, Equiv.Perm (Fin (k i)))
    (data output : I → Tree) (room : ∀ i, V i ≤ T i) (area : ∀ i, 2^(k i) ≤ V i)
    (C : ℕ) (volume : ∀ i, (data i).count ≤ C*(V i+1)) {big small : Cmd}
    (large : EffectiveBoundedTask.Runs big (fun i : {i // K < k i} => T i.val) (fun i => V i.val)
      (fun i => cutoffInput p data i.val) (fun i => output i.val))
    (short : EffectiveBoundedTask.Runs small (fun i : {i // k i ≤ K} => T i.val) (fun i => V i.val)
      (fun i => cutoffInput p data i.val) (fun i => output i.val)) :
    EffectiveBoundedTask.Runs (cutoffCmd K big small) T V (cutoffInput p data) output := by
  obtain ⟨M,hM⟩ := polynomial_le_multiple_array_length 2
  let D := 2*M+C+1
  have inputSize i : (cutoffInput p data i).count ≤ D*(V i+1) := by
    change size (table (p i)) + (data i).count + 1 ≤ _
    have h := (Reflections.table_size (p i)).trans (Nat.mul_le_mul_left 2
      ((hM (k i)).trans (Nat.mul_le_mul_left M (area i))))
    have v := volume i
    dsimp [D]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at *
    omega
  have yes (i : {i // decide (K < k i) = true}) : K < k i.val := of_decide_eq_true i.property
  have no (i : {i // decide (K < k i) = false}) : k i.val ≤ K :=
    Nat.le_of_not_gt (of_decide_eq_false i.property)
  have body := EffectiveBoundedTask.Runs.control (t := T) (s := V) (u := cutoffInput p data) (v := output)
    (fun i => decide (K < k i)) (short.on fun i => ⟨i.val,no i⟩) (large.on fun i => ⟨i.val,yes i⟩)
  exact (cutoff_test K k T V p data room D inputSize).sequence (body.bound 1 (D+1)
    (fun i => by simp) (fun i => by have h := inputSize i; rw [Nat.add_mul, Nat.one_mul]; omega))

end
end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
