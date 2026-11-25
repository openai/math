import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomColumn
import OAI.Computability.NearSquareRoot.ScheduleRegisterWitness

/-!
# Register-preserving traversal of a P192 forest

Each application of the row command runs above the unconsumed input. The
traversal parks the resulting row on register one and restores it in order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code
open CommonRegisters Space

open private rowBody from OAI.Computability.NearSquareRoot.ScheduleRegisterLoomColumn

/-- Apply the compiled command to each row of a forest. -/
def mapCommand (op : Cmd) : Cmd := .tie (rowBody op)

theorem map_within {R : ℕ} (hR : 3 ≤ R) {op : Cmd} (hop : Within R op) :
    Within R (mapCommand op) :=
  split_within (by omega) (fun _ => (by omega : 0 < R))
    ⟨hop, move_within (by omega) (by omega) (by omega), trivial,
      move_within (by omega) (by omega) (by omega), (by omega : 0 < R)⟩

private theorem row_fits {K : Type*} (rows : List K) (p q : K → Tree) (op : Cmd) (t : K → ℕ)
    (hc : ∀ k env r, Fits env op (pile 0 (p k) r) (pile 0 (q k) r) (t k))
    (env : Env) (r : Deck) :
    Fits (rowBody op :: env) (rowBody op) (pile 0 (Task.forest p rows) r)
      (pile 0 (Task.forest q rows) r) (costSum t rows + 100 * (Task.forest q rows).count) := by
  let G := rowBody op :: env
  induction rows generalizing r with
  | nil =>
    exact (fits_bit (b := false) (c := give 0) (fits_give false ..)).mono (by simp [Tree.count])
  | cons x xs ih =>
    have head := hc x G (pile 0 (Task.forest p xs) r)
    have park := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide)
      (q x) G (pile 0 (Task.forest p xs) r)
    rw [pile_comm 1 _ _ 0 _ (by decide)] at park
    have tail := (ih (pile 1 (q x) r)).again0
    rw [pile_comm 0 (Task.forest q xs) r 1 (q x) (by decide)] at tail
    have restore := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide)
      (q x) G (pile 0 (Task.forest q xs) r)
    apply (fits_pair (head.join (park.join (tail.join (restore.join (fits_pack _ _ r 0 G)))))).mono
    simp only [costSum_cons, Task.forest_cons, Tree.count, Nat.mul_add, Nat.mul_one]
    omega

/-- The calls add their own clocks. Parking and rebuilding the forest costs
a linear function of the output volume. -/
theorem map_fits {K : Type*} (rows : List K) (p q : K → Tree) (op : Cmd) (t : K → ℕ)
    (hc : ∀ k env r, Fits env op (pile 0 (p k) r) (pile 0 (q k) r) (t k))
    (env : Env) (r : Deck) :
    Fits env (mapCommand op) (pile 0 (Task.forest p rows) r) (pile 0 (Task.forest q rows) r)
      (costSum t rows + 100 * (Task.forest q rows).count + 10) :=
  (row_fits rows p q op t hc env r).tie.mono (by omega)


/-- A uniform linear clock for every child gives a linear clock in the combined
input and output forest volume. -/
theorem map_fits_linear {K : Type*} (rows : List K) (p q : K → Tree) (op : Cmd) (D : ℕ)
    (hc : ∀ k env r, Fits env op (pile 0 (p k) r) (pile 0 (q k) r) (D * ((p k).count + 1)))
    (env : Env) (r : Deck) :
    Fits env (mapCommand op) (pile 0 (Task.forest p rows) r) (pile 0 (Task.forest q rows) r)
      ((D + 100) * ((Task.forest p rows).count + (Task.forest q rows).count + 1)) := by
  apply (map_fits rows p q op _ hc env r).mono
  rw [costSum_mul]
  have size : costSum (fun a => (p a).count + 1) rows ≤ (Task.forest p rows).count := by
    induction rows with
    | nil => exact Nat.zero_le _
    | cons x xs ih => simp only [costSum_cons, Task.forest_cons, Tree.count]; omega
  have budget := Nat.mul_le_mul_left D size
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- The row command's working space plus the volume of the two forests
bounds all live registers and the return stack throughout the map. -/
def mapSpace (S : ℕ) (input output : Tree) : ℕ := S + 50 * (input.count + output.count)

private theorem row_bounded {K : Type*} (rows : List K) (p q : K → Tree) (op : Cmd) (t : K → ℕ)
    (S : ℕ) (hc : ∀ k env r base, DeckCap base r →
      BoundedFits env op (pile 0 (p k) r) (pile 0 (q k) r) (t k) (base + S) S)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let depth := mapSpace S (Task.forest p rows) (Task.forest q rows)
    BoundedFits (rowBody op :: env) (rowBody op) (pile 0 (Task.forest p rows) r)
      (pile 0 (Task.forest q rows) r) (costSum t rows + 100 * (Task.forest q rows).count)
      (base + depth) depth := by
  let G := rowBody op :: env
  induction rows generalizing r base with
  | nil =>
    let depth := mapSpace S (.atom false) (.atom false)
    have cap : DeckCap (base + depth) (pile 0 (.atom false) r) :=
      (hr.pile 0 _).mono (by simp [depth, mapSpace, Tree.count])
    have write := BoundedFits.give false r 0 G (depth := depth) cap
    exact (BoundedFits.bit (b := false) (c := give 0) write cap
      (by simp [depth, mapSpace, Tree.count])).mono (by simp [Tree.count]) le_rfl le_rfl
  | cons x xs ih =>
    let tailIn := Task.forest p xs
    let tailOut := Task.forest q xs
    let parentIn := Tree.fork (p x) tailIn
    let parentOut := Tree.fork (q x) tailOut
    let depth := mapSpace S parentIn parentOut
    let cap := base + depth
    have amount : depth = S + 50 * ((p x).count + tailIn.count + 1 +
        ((q x).count + tailOut.count + 1)) := rfl
    have one : 1 ≤ depth := by omega
    have room : depth - 1 + 1 ≤ depth := by omega
    have hi : DeckCap cap (pile 0 parentIn r) := (hr.pile 0 _).mono (by
      dsimp only [cap, parentIn, Tree.count]
      omega)
    have ho : DeckCap cap (pile 0 parentOut r) := (hr.pile 0 _).mono (by
      dsimp only [cap, parentOut, Tree.count]
      omega)
    have head := (hc x G (pile 0 tailIn r) _ (hr.pile 0 _)).mono le_rfl
      (show base + tailIn.count + S ≤ cap by dsimp only [cap]; omega)
      (show S ≤ depth - 1 by omega)
    have park := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide)
      (q x) G (pile 0 tailIn r)
    have store := BoundedFits.of_fits park (cap := cap) (depth := depth - 1)
      (fun i => by have := ((hr.pile 0 tailIn).pile 0 (q x)) i; dsimp only [cap]; omega)
      (by omega)
    rw [pile_comm 1 _ _ 0 _ (by decide)] at store
    have tail := (ih (pile 1 (q x) r) _ (hr.pile 1 _)).again0
    have tailCap : base + (q x).count + mapSpace S tailIn tailOut ≤ cap := by
      dsimp only [cap, mapSpace]; omega
    have tailDepth : mapSpace S tailIn tailOut ≤ depth - 1 := by
      dsimp only [mapSpace]; omega
    have remaining := tail.mono le_rfl tailCap tailDepth
    rw [pile_comm 0 (Task.forest q xs) r 1 (q x) (by decide)] at remaining
    have restore := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide)
      (q x) G (pile 0 tailOut r)
    have back := BoundedFits.of_fits restore (cap := cap) (depth := depth - 1)
      (fun i => by have := ((hr.pile 0 tailOut).pile 1 (q x)) i; dsimp only [cap]; omega)
      (by omega)
    have pack := BoundedFits.pack (q x) tailOut r 0 G (depth := depth) ho
    have whole := head.join (store.join (remaining.join (back.join pack room) room) room) room
    apply (BoundedFits.pair whole hi one).mono _ le_rfl le_rfl
    simp only [costSum_cons, Task.forest_cons, Tree.count, Nat.mul_add, Nat.mul_one]
    omega

/-- Space for the forest and the largest row call suffices, even for a leaf
whose clock exceeds its space bound. -/
theorem map_bounded {K : Type*} (rows : List K) (p q : K → Tree) (op : Cmd) (t : K → ℕ)
    (S : ℕ) (hc : ∀ k env r base, DeckCap base r →
      BoundedFits env op (pile 0 (p k) r) (pile 0 (q k) r) (t k) (base + S) S)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let depth := mapSpace S (Task.forest p rows) (Task.forest q rows)
    BoundedFits env (mapCommand op) (pile 0 (Task.forest p rows) r) (pile 0 (Task.forest q rows) r)
      (costSum t rows + 100 * (Task.forest q rows).count + 10) (base + depth) depth :=
  (row_bounded rows p q op t S hc env r base hr).tie.mono (by omega) le_rfl le_rfl


/-- Lift one register-bounded command over variable-length input forests.
The time budget adds the row times and output volume; the space budget
depends on the maximum row allowance and the two resident forest volumes. -/
theorem map_checked {I : Type} {K : I → Type} {R : ℕ} (hR : 3 ≤ R)
    (rows : (i : I) → List (K i)) (p q : (i : I) → K i → Tree)
    (t : (i : I) → K i → ℕ) (S : I → ℕ)
    (h : RegisterWitness.Bounded R (fun z : Sigma K => t z.1 z.2)
      (fun z => S z.1) (fun z => p z.1 z.2) (fun z => q z.1 z.2)) :
    let src := fun i => Task.forest (p i) (rows i)
    let dst := fun i => Task.forest (q i) (rows i)
    RegisterWitness.Bounded R (fun i => costSum (fun k => t i k + 1) (rows i) + (dst i).count)
      (fun i => S i + (src i).count + (dst i).count) src dst := by
  obtain ⟨op, hop, C, hc⟩ := h
  refine ⟨mapCommand op, map_within hR hop, C + 100, fun i env r base hr => ?_⟩
  have run := map_bounded (rows i) (p i) (q i) op (fun k => C * (t i k + 1))
    (C * (S i + 1)) (fun k env r base hr => hc ⟨i, k⟩ env r base hr) env r base hr
  apply run.mono
  · rw [costSum_mul]
    dsimp only
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  · dsimp only [mapSpace]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  · dsimp only [mapSpace]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
