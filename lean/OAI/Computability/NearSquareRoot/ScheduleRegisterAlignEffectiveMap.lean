import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveTask
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct
import OAI.Computability.IntegerMultiplication.Code.Fold

/-! # Effective map on a forest with an elementwise promise

The command parks the unprocessed head in register one and maps the tail.
It then restores the head and calls the callback with the completed tail
still parked beneath it. Both transports therefore cost time proportional
to the input head.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveMap
open IntegerMultiplication Code GeneratorSyntax CommonRegisters

private def body (c : Cmd) : Cmd :=
  splitRoot 0 (fun _ => give 0 false)
    ((move 0 1 2).join ((Prog.again 0).join ((move 1 0 2).join (c.join (pack 0)))))

def program (c : Cmd) : Cmd := .tie (body c)

theorem effective {P : Type} [Primcodable P] {c : P → Cmd} (h : Effective ltr c) :
    Effective ltr (fun p => program (c p)) := by
  unfold program
  apply Effective.tie
  unfold body
  apply KernelEffectiveFamily.effective_splitRoot
  · intro; exact effective_const _ _
  · exact (effective_const _ (move 0 1 2)).join ((effective_const _ (Prog.again 0)).join
      ((effective_const _ (move 1 0 2)).join (h.join (effective_const _ (pack 0)))))

theorem within {R : ℕ} (hR : 3 ≤ R) {c : Cmd} (h : Within R c) : Within R (program c) := by
  simp [program,body,RegisterWitness.splitRoot_within,Within,move,forward,forwardBody,flood,give,pack,h]
  omega

theorem run (c : Cmd) {F X : Type*} (p q : F → X → Tree) (cost : F → X → ℕ)
    (B : F → X → Prop)
    (h : EffectiveTask.Runs c (fun x : {x : F × X // B x.1 x.2} => cost x.val.1 x.val.2)
      (fun x => p x.val.1 x.val.2) (fun x => q x.val.1 x.val.2)) :
    EffectiveTask.Runs (program c) (fun x : {x : F × List X // ∀ i ∈ x.2, B x.1 i} =>
      costSum (cost x.val.1) x.val.2 + (Task.forest (p x.val.1) x.val.2).count)
      (fun x => Task.forest (p x.val.1) x.val.2) (fun x => Task.forest (q x.val.1) x.val.2) := by
  obtain ⟨C,hc⟩ := h
  let D := C+100
  refine ⟨D,fun ⟨⟨f,xs⟩,valid⟩ env r => ?_⟩
  let G := body c::env
  have fits (ys : List X) (ok : ∀ x∈ys, B f x) (deck : Deck) :
      Fits G (body c) (pile 0 (Task.forest (p f) ys) deck) (pile 0 (Task.forest (q f) ys) deck)
        (D*(costSum (cost f) ys + (Task.forest (p f) ys).count)) := by
    induction ys generalizing deck with
    | nil =>
      apply (fits_bit (b:=false) (c:=fun _ => give 0 false) (fits_give false deck 0 G)).mono
      simp [D,Tree.count]
    | cons y ys ih =>
      have park := fits_move (i:=0) (j:=1) (u:=2) (by decide) (by decide) (p f y) G
        (pile 0 (Task.forest (p f) ys) deck)
      rw [pile_comm 1 _ _ 0 _ (by decide)] at park
      have tail := Fits.again0 (ih (fun x hx => ok x (List.mem_cons_of_mem _ hx)) (pile 1 (p f y) deck))
      have restore := fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide) (p f y) G
        (pile 0 (Task.forest (q f) ys) deck)
      rw [pile_comm 1 _ _ 0 _ (by decide)] at restore
      have call := hc ⟨(f,y),ok y List.mem_cons_self⟩ G (pile 0 (Task.forest (q f) ys) deck)
      apply (fits_pair (park.join (tail.join (restore.join (call.join (fits_pack _ _ deck 0 G)))))).mono
      simp only [costSum_cons,Task.forest_cons,Tree.count,D,Nat.add_mul,Nat.mul_add,Nat.mul_one]
      omega
  apply (Fits.tie (fits xs valid r)).mono
  simp only [Nat.mul_add,Nat.mul_one]
  omega

/-- A callback without a promise maps a plain list with the same input traversal cost. -/
theorem unrestricted (c : Cmd) {X : Type*} (p q : X → Tree) (cost : X → ℕ)
    (h : EffectiveTask.Runs c cost p q) :
    EffectiveTask.Runs (program c) (fun xs => costSum cost xs + (Task.forest p xs).count)
      (Task.forest p) (Task.forest q) := by
  let point : {x : Unit × X // True} → X := fun x => x.val.2
  let row : List X → {x : Unit × List X // ∀ i∈x.2, True} := fun xs => ⟨((),xs),by simp⟩
  exact (run c (fun _ : Unit => p) (fun _ => q) (fun _ => cost) (fun _ _ => True)
    (h.on point)).on row

end EffectiveMap

end NearSquareRoot
end Computability
end OAI
