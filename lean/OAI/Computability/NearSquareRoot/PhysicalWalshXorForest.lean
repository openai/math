import OAI.Computability.IntegerMultiplication.Strip.Header
import OAI.Computability.IntegerMultiplication.Code.Pace
import OAI.Computability.NearSquareRoot.BoundedProduct
import OAI.Computability.NearSquareRoot.PhysicalWalshXorSweep

/-! # Preparing the annotated opcode forest from a single header -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorForest

open IntegerMultiplication Code Strip Space

variable {X Q : Type} [Codec Q] {r : Regime X} {ops : X → List Q}

/-- Serializing the chronological opcode list after attaching its common header
produces precisely the descriptor forest read by the bounded schedule. -/
private theorem encode (header : Tree) (qs : List Q) :
    send (polyPush id (header,qs)) = Task.forest (fun q => .fork header (send q)) qs := by
  rw [← Task.forest_send, polyPush, Task.forest_map]
  rfl

/-- Make one copy of the original physical header on each emitted opcode. -/
theorem small (z : Q) (h : r.Has ops) :
    r.Small (fun x => Task.forest (fun q => .fork (r.header x) (send q)) (ops x)) := by
  have header : r.Has r.header := r.self
  have paired := (header.pair h).thenDo (Poly.push (.atom false : Tree) z Poly.identity)
  change r.Small (fun x => send (polyPush id (r.header x,ops x))) at paired
  simpa only [encode] using paired

/-- One polynomial bounds the actual preparation time, workspace, whole
descriptor forest, and each individual descriptor in the schedule. -/
theorem bounded (z : Q) (h : r.Has ops) : ∃ D H : ℕ,
    let b x := H*(r.scale x+1)^D
    let key x (q : Q) := Tree.fork (r.header x) (send q)
    let forest x := Task.forest (key x) (ops x)
    BoundedTask b b r.header forest ∧ (∀ x, (forest x).count ≤ b x) ∧
      ∀ x q, q ∈ ops x → (key x q).count ≤ b x := by
  have prep := small z h
  have extent := prep.extent
  obtain ⟨time,dt,cmd⟩ := prep
  obtain ⟨D,H,bound⟩ := (r.gauge.add dt).add extent
  refine ⟨D,H,?_,?_,?_⟩
  · apply (BoundedTask.of_time cmd).mono <;> intro x <;> have := bound x <;> dsimp only at * <;> omega
  · intro x
    have := bound x
    dsimp only at *
    omega
  · intro x q hq
    have mem : (r.header x,q) ∈ polyPush id (r.header x, ops x) :=
      List.mem_map_of_mem (f := fun op => (r.header x,op)) hq
    have less := (size_bel mem).le
    rw [size, size, encode] at less
    exact less.trans (by have := bound x; dsimp only at *; omega)

open Controlled Controlled.PositionProgram Controlled.PositionPreparation

/-- Run the aligned XOR from the original header and the complete spectator
array. A polynomial reserve in the volume pays for preparing the forest and
reading its entries, uniformly under later restrictions of the input family. -/
theorem boundedProgramWithSetup (k G : X → ℕ)
    (D H : ℕ)
    (prep : BoundedTask (fun x => H*(r.scale x+1)^D) (fun x => H*(r.scale x+1)^D) r.header
      (fun x => Task.forest (fun q : Op => .fork (r.header x) (send q)) (XorSweep.program (k x/3) (G x))))
    (forestCap : ∀ x, (Task.forest (fun q : Op => .fork (r.header x) (send q))
      (XorSweep.program (k x/3) (G x))).count ≤ H*(r.scale x+1)^D)
    (keyCap : ∀ x q, q ∈ XorSweep.program (k x/3) (G x) →
      (Tree.fork (r.header x) (send q)).count ≤ H*(r.scale x+1)^D) :
    ∀ {J : Type} (select : J → X) {Y : J → Type}
      (box : (j : J) → ((Fin (k (select j)) → Bool) → Y j) → Tree)
      (V factor : J → ℕ) (C : ℕ),
      (∀ j, 0 < G (select j)) → (∀ j, (r.scale (select j)+1)^D ≤ V j) →
      (∀ j f, (box j f).count ≤ C*V j) →
      let key j (q : Op) := Tree.fork (r.header (select j)) (send q)
      let stages j := XorSweep.program (k (select j)/3) (G (select j))
      let cost j := V j*(factor j+1)
      BoundedTask (fun i : (j : J) × {q // q ∈ stages j} × ((Fin (k (select j)) → Bool) → Y j) => cost i.1)
        (fun i => V i.1) (fun i => .fork (key i.1 i.2.1) (box i.1 i.2.2))
        (fun i => box i.1 (i.2.2 ∘ fun w => act (G (select i.1)) w i.2.1)) →
      BoundedTask (fun i : (j : J) × ((Fin (k (select j)) → Bool) → Y j) =>
        (4+3*G (select i.1))*cost i.1+1) (fun i => V i.1)
        (fun i => .fork (r.header (select i.1)) (box i.1 i.2))
        (fun i => box i.1 (i.2 ∘ directed (XorSweep.gate (k (select i.1)/3)))) := by
  intro J select Y box V factor C pos reserve cell key stages cost stage
  let I := (j : J) × ((Fin (k (select j)) → Bool) → Y j)
  let room j := (H+C+1)*V j
  have space (j) : V j ≤ room j := Nat.le_mul_of_pos_left _ (by omega)
  have setup (j) := Nat.mul_le_mul_left H (reserve j)
  have tables (j) : (Task.forest (key j) (stages j)).count ≤ room j :=
    ((forestCap (select j)).trans (setup j)).trans (Nat.mul_le_mul_right _ (by omega))
  have live (j f) : (box j f).count ≤ room j :=
    (cell j f).trans (Nat.mul_le_mul_right _ (by omega))
  have enough (j) : V j ≤ cost j := Nat.le_mul_of_pos_right _ (by omega)
  have keys (j q) (hq : q ∈ stages j) : cost j + (key j q).count + 1 ≤ (H+2)*cost j := by
    have keySize := ((keyCap (select j) q hq).trans (setup j)).trans (Nat.mul_le_mul_left H (enough j))
    change (key j q).count ≤ H*cost j at keySize
    have positive : 0 < cost j := ((pow_pos (Nat.succ_pos _) D).trans_le (reserve j)).trans_le (enough j)
    rw [Nat.add_mul]
    omega
  have sweep := XorSweep.boundedProgram (k ∘ select) (G ∘ select) pos key box
    (fun j => (H+2)*cost j) room (fun j _ => cost j)
    (stage.mono (fun _ => le_rfl) (fun i => space i.1)) tables live keys
  let calls j := 4+3*G (select j)
  let total j := calls j*cost j+1
  have batch := sweep.bound (time' := fun i => total i.1) (space' := fun i => V i.1) (H+2) (H+C+1)
    (by
      intro i
      change calls i.1*((H+2)*cost i.1)+1+1 ≤ (H+2)*(calls i.1*cost i.1+1+1)
      rw [Nat.mul_left_comm]
      simp only [Nat.mul_succ]
      omega)
    (by
      intro i
      change (H+C+1)*V i.1+1 ≤ (H+C+1)*(V i.1+1)
      rw [Nat.mul_succ]; omega)
  have boot := (prep.on (fun i : I => select i.1)).left (fun i => box i.1 i.2)
  have start := boot.bound (time' := fun i => total i.1) (space' := fun i => V i.1) (H+1) (H+C+1)
    (by
      intro i
      have v := (enough i.1).trans (Nat.le_mul_of_pos_left (cost i.1) (by dsimp [calls]; omega : 0 < calls i.1))
      have cap := (setup i.1).trans (Nat.mul_le_mul_left H (Nat.le_succ_of_le v))
      change _ ≤ H*total i.1 at cap
      simp only [Nat.succ_mul, Nat.mul_succ]; omega)
    (by
      intro i
      have head := setup i.1
      have data := cell i.1 i.2
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_succ]
      omega)
  exact (start.compose batch).bound 2 1 (fun _ => by dsimp only [total, calls]; omega) (fun _ => by simp)

/-- Prepare the native schedule once for the original family and reuse it
on every subsequent array and every selected subfamily. -/
theorem boundedProgramOn (k G : X → ℕ)
    (h : r.Has (fun x => XorSweep.program (k x/3) (G x))) :
    ∃ D : ℕ, ∀ {J : Type} (select : J → X) {Y : J → Type}
      (box : (j : J) → ((Fin (k (select j)) → Bool) → Y j) → Tree)
      (V factor : J → ℕ) (C : ℕ),
      (∀ j, 0 < G (select j)) → (∀ j, (r.scale (select j)+1)^D ≤ V j) →
      (∀ j f, (box j f).count ≤ C*V j) →
      let key j (q : Op) := Tree.fork (r.header (select j)) (send q)
      let stages j := XorSweep.program (k (select j)/3) (G (select j))
      let cost j := V j*(factor j+1)
      BoundedTask (fun i : (j : J) × {q // q ∈ stages j} × ((Fin (k (select j)) → Bool) → Y j) => cost i.1)
        (fun i => V i.1) (fun i => .fork (key i.1 i.2.1) (box i.1 i.2.2))
        (fun i => box i.1 (i.2.2 ∘ fun w => act (G (select i.1)) w i.2.1)) →
      BoundedTask (fun i : (j : J) × ((Fin (k (select j)) → Bool) → Y j) =>
        (4+3*G (select i.1))*cost i.1+1) (fun i => V i.1)
        (fun i => .fork (r.header (select i.1)) (box i.1 i.2))
        (fun i => box i.1 (i.2 ∘ directed (XorSweep.gate (k (select i.1)/3)))) := by
  obtain ⟨D,H,prep,forestCap,keyCap⟩ := bounded (default : Op) h
  exact ⟨D,boundedProgramWithSetup k G D H prep forestCap keyCap⟩

end PhysicalWalsh.XorForest

end NearSquareRoot
end Computability
end OAI
