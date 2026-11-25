import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveContext
import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveTask
import OAI.Computability.NearSquareRoot.ScheduleRegisterAlign
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyIterate
import Batteries.Tactic.OpenPrivate

/-! # Effective arity-dependent scans on the address streams -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterAlign
open IntegerMultiplication Code CommonRegisters GeneratorSyntax KernelSelectorAlign Filter
open EffectiveTask (Runs)
open KernelEffectiveFamily (leftCmd rightCmd)

theorem runLeft {X : Type*} {c : Cmd} {a : X → ℕ} {p q : X → Tree}
    (h : Runs c a p q) (z : X → Tree) :
    Runs (leftCmd c) a (fun x => .fork (p x) (z x)) (fun x => .fork (q x) (z x)) := by
  obtain ⟨C,hc⟩ := h
  refine ⟨C+7,fun x env r => ?_⟩
  apply (fits_pair ((hc x env (pile 0 (z x) r)).join (fits_pack _ _ _ _ _))).mono
  rw [Nat.add_mul]
  omega

private theorem runRight {X : Type*} {c : Cmd} {a : X → ℕ} {p q : X → Tree}
    (h : Runs c a p q) (z : X → Tree) :
    Runs (rightCmd c) (fun x => (z x).count+a x)
      (fun x => .fork (z x) (p x)) (fun x => .fork (z x) (q x)) := by
  obtain ⟨C,hc⟩ := h
  refine ⟨91+C,fun x env r => ?_⟩
  have h₁ := fits_move (i := 0) (u := 2) (j := 1) (by decide) (by decide) (z x) env (pile 0 (p x) r)
  have h₂ := hc x env (pile 1 (z x) r)
  rw [pile_comm 1 _ r 0 _ (by decide)] at h₁
  have h₃ := fits_move (i := 1) (u := 2) (j := 0) (by decide) (by decide) (z x) env (pile 0 (q x) r)
  rw [pile_comm 1 _ r 0 _ (by decide)] at h₃
  refine (fits_pair (h₁.join (h₂.join (h₃.join (fits_pack _ _ _ _ _))))).mono ?_
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]
  omega

open private complete from OAI.Computability.NearSquareRoot.ScheduleRegisterDivide
open RegisterDivide in
theorem run_divide (d : ℕ) :
    Runs (command d) id (fun n => send (tally ((d+1)*n))) (fun n => send (tally n)) := by
  refine ⟨8*(d+1)+16,fun n env r => ?_⟩
  let b := block (d+1) emit
  have run (n : ℕ) : Fits (b::env) b (pile 0 (send (tally ((d+1)*n))) r)
      (pile 0 (send (tally n)) r) ((8*(d+1)+15)*n+5) := by
    induction n with
    | zero =>
      change Fits (b::env) (splitRoot 0 (fun _ => give 0 false) _)
        (pile 0 (.atom false) r) (pile 0 (.atom false) r) _
      exact fits_bit (c := fun _ => give 0 false) (fits_give false r 0 _)
    | succ n ih =>
      have step := ih.again0.join ((fits_give false (pile 0 (send (tally n)) r) 0 (b::env)).join
        (fits_pack (.atom false) (send (tally n)) r 0 (b::env)))
      have h := complete (d+1) ((d+1)*n) (k := emit) step
      rw [Nat.mul_succ,Nat.add_comm ((d+1)*n) (d+1),tally_succ,send_cons]
      exact h.mono (by simp only [Nat.mul_succ]; omega)
  exact (run n).tie.mono (by change _ ≤ (8*(d+1)+16)*(n+1); rw [Nat.mul_add,Nat.mul_one]; nlinarith)

/-- Growing a constant-length list of copies does not increase the register
bank. Each pass appends a copy of the original ruler. -/
theorem generate_repeat {R : ℕ} (hR : 4 ≤ R) :
    KernelEffectiveFamily.Family R (fun n : ℕ => fun t : Tally => List.replicate n t) := by
  let seed := fun t : Tally => (t,([] : List Tally))
  let step := fun t : Tally × List Tally => (t.1,t.1 :: t.2)
  have hseed : RegisterWitness.Easy R seed := RegisterWitness.Easy.identity.pair (by omega)
    (RegisterWitness.Easy.const (by omega) [])
  have hstep : RegisterWitness.Easy R step :=
    (RegisterWitness.Easy.fst hR).pair (by omega) RegisterWitness.Easy.cons
  have base := KernelEffectiveFamily.Family.fixed (P := ℕ) hseed
  have bulk := base.comp (KernelEffectiveFamily.Family.iterate_fixed hstep)
  apply (bulk.comp (KernelEffectiveFamily.Family.fixed (RegisterWitness.Easy.snd (by omega)))).congr
  intro n t
  have h : step^[n] (seed t) = (t,List.replicate n t) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih]; rfl
  exact congrArg Prod.snd h

private theorem bit_cost (xs : List Bool) : size xs=2*xs.length+1 :=
  columns_size 0 xs

/-- Compile the zipper from streams already separated at their slot boundaries.
The arity controls the number of nested right-component calls. -/
theorem generate_streams : ∀ᶠ R in atTop, EffectiveTask.Family R
    (fun n (xs : List (Column n)) => xs.length)
    (fun n xs => send (bitStreams n xs)) (fun _ xs => send xs) := by
  let drop := Task.dropRight (fun xs : List (Column 0) => send xs)
    (fun _ => send ([] : List (List Bool)))
  let zip := Task.zipTrees (Prod.fst : Tree × Tree → Tree) Prod.snd
  filter_upwards [eventually_ge_atTop 3,RegisterSelect.checked_eventually drop,RegisterSelect.checked_eventually zip]
    with R hR hd hz
  obtain ⟨d,wd,rd⟩ := hd
  obtain ⟨z,wz,rz⟩ := hz
  let t : Template := .join Template.right (.fixed z)
  refine ⟨t.iterate d,t.effective_iterate d,?_⟩
  intro n
  induction n with
  | zero =>
    refine ⟨wd,?_⟩
    apply (show Runs d _ _ _ from rd).bound 4
    intro xs
    change size xs+1+1 ≤ 4*(xs.length+1)
    rw [columns_size]
    omega
  | succ n ih =>
    change Within R ((Template.subst (t.iterate d n) Template.right).join z) ∧ _
    rw [Template.subst_right]
    refine ⟨⟨KernelEffectiveFamily.within_right hR ih.1,wz⟩,?_⟩
    let tail (xs : List (Column (n+1))) := xs.map Prod.snd
    let hd' (xs : List (Column (n+1))) := send (xs.map Prod.fst)
    let pair (v : Column (n+1)) : Tree × Tree := (send v.1,send v.2)
    have input (xs : List (Column (n+1))) :
        Tree.fork (Task.forest Prod.fst (xs.map pair)) (Task.forest Prod.snd (xs.map pair)) =
          Tree.fork (hd' xs) (send (tail xs)) := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons,Task.forest_cons,Tree.fork.injEq] at ih ⊢
        exact ⟨congrArg (Tree.fork (send x.1)) ih.1,congrArg (Tree.fork (send x.2)) ih.2⟩
    have output (xs : List (Column (n+1))) :
        Task.forest (fun w => Tree.fork w.1 w.2) (xs.map pair) = send xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => exact congrArg (Tree.fork (send x)) ih
    have merge := ((show Runs z _ _ _ from rz).on (List.map pair)).conform (fun _ => rfl) input output
    have full := (runRight (ih.2.on tail) hd').comp merge
    change Runs ((Template.subst (t.iterate d n) Template.right).join z) _ _ _
    rw [Template.subst_right]
    apply full.bound (2*n+10)
    intro xs
    have c := (Tree.fork.inj (input xs))
    change size (xs.map Prod.fst)+(tail xs).length+
      ((Task.forest Prod.fst (xs.map pair)).count+(Task.forest Prod.snd (xs.map pair)).count)+1 ≤ _
    rw [c.1,c.2]
    change size (xs.map Prod.fst)+(tail xs).length+
      (size (xs.map Prod.fst)+size (tail xs))+1 ≤ _
    rw [bit_cost,columns_size n]
    simp only [tail,List.length_map]
    ring_nf
    omega

end RegisterAlign

end NearSquareRoot
end Computability
end OAI
