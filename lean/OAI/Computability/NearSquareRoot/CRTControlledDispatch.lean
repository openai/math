import OAI.Computability.NearSquareRoot.CRTControlledBatches
import OAI.Computability.IntegerMultiplication.Code.FoldLeft

/-! # Executing a variable list of physical passes

Stage descriptors live on the data tape. One P192 command consumes the list in order and
charges both the stage's physical run and the transport of its encoded descriptor.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Code

private def passProduct {A D : Type*} (run : A → Equiv.Perm D) : List A → Equiv.Perm D
  | [] => Equiv.refl _
  | a::l => (run a).trans (passProduct run l)

private theorem passProduct_apply {A D : Type*} (run : A → Equiv.Perm D) (stages : List A) (d : D) :
    passProduct run stages d = stages.foldl (fun q a => run a q) d := by
  induction stages generalizing d with
  | nil => rfl
  | cons a l ih => exact ih (run a d)

/-- The checked loop uses the same command on all inputs and for all schedule lengths.
Its input consists of the encoded program followed by an arbitrary encoded array. -/
theorem physicalSchedule {X A : Type*} {D : X → Type*}
    (stages : X → List A) (key : X → A → Tree) (box : (x : X) → D x → Tree)
    (run : (x : X) → A → Equiv.Perm (D x)) (charge : X → A → ℕ) (allowance : X → ℕ)
    (step : Task (fun i : (x : X) × {a // a ∈ stages x} × D x => charge i.1 i.2.1)
      (fun i => .fork (key i.1 i.2.1) (box i.1 i.2.2))
      (fun i => box i.1 (run i.1 i.2.1 i.2.2)))
    (bound : ∀ x, ∀ a ∈ stages x, charge x a + (key x a).count + 1 ≤ allowance x) :
    Task (fun i : (x : X) × D x => (stages i.1).length * allowance i.1 + 1)
      (fun i => .fork (Task.forest (key i.1) (stages i.1)) (box i.1 i.2))
      (fun i => box i.1 ((stages i.1).foldl (fun q a => run i.1 a q) i.2)) := by
  let Y := (x : X) × D x
  let w := fun (l : List A) (y : Y) => box y.1 ((passProduct (run y.1) l).symm y.2)
  let V := fun (l : List A) (y : Y) => ∀ a ∈ l, a ∈ stages y.1
  have loop := @Task.sweep A Y (fun y => key y.1) w (fun a _ y => charge y.1 a) V
    (fun a l y h v hv => h v (List.mem_cons_of_mem a hv))
    (show Task _ _ _ from ?_)
  · let terminal (i : (x : X) × D x) : Y := ⟨i.1,passProduct (run i.1) (stages i.1) i.2⟩
    let initial (i : (x : X) × D x) : {s : List A × Y // V s.1 s.2} :=
      ⟨(stages i.1, terminal i),fun _ ha => ha⟩
    have hs := loop.on initial
    have hc (x : X) (l : List A) (hl : ∀ a ∈ l, a ∈ stages x) :
        Task.foldCost (fun a _ => charge x a + (key x a).count) l ≤ l.length * allowance x + 1 := by
      induction l with
      | nil => simp [Task.foldCost]
      | cons a l ih =>
        have h₁ := bound x a (hl a List.mem_cons_self)
        have h₂ := ih (fun v hv => hl v (List.mem_cons_of_mem _ hv))
        simp only [Task.foldCost, List.length_cons, Nat.succ_mul]
        omega
    refine (hs.mono (fun i => hc i.1 (stages i.1) (fun _ hv => hv))).conform (fun _ => rfl) ?_ ?_
    · intro i
      simp [initial, terminal, w]
    · intro i
      simp [initial, terminal, w, passProduct, passProduct_apply]
  · let source (i : {s : A × List A × Y // V (s.1::s.2.1) s.2.2}) :
        (x : X) × {a // a ∈ stages x} × D x :=
      ⟨i.val.2.2.1, ⟨i.val.1, i.property _ List.mem_cons_self⟩,
        (passProduct (run i.val.2.2.1) (i.val.1::i.val.2.1)).symm i.val.2.2.2⟩
    refine (step.on source).conform (fun _ => rfl) (fun _ => rfl) ?_
    intro i
    simp [source, w, passProduct]

end Controlled

end NearSquareRoot
end Computability
end OAI
