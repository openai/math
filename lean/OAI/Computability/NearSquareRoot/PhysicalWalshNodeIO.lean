import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSpec
import OAI.Computability.NearSquareRoot.PhysicalWalshLaneIndex

/-! # Address-ordered tape input and output of a recursive Walsh template

A nonterminal has complete batches of `W` spectator blocks. The split and
merge tape programs preserve the two layout rulers. Their returned records
are those at the parent ordinals given by `lane` and `unlane`.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication Code PhysicalWalsh PhysicalWalsh.ChildLanes Space

/-- Return a result written by any child lane to the same lane, including
its local group order. -/
theorem lane_unlane {A W : ℕ} (hW : 0 < W) (s : Shape) (x : Fin W → Data s) :
    lane A W s (unlane A hW s x) = x := by
  funext j n
  let R := inner A s
  have hr : 0 < R := Nat.mul_pos (by positivity : 0 < 2^(grow A s.level)) s.suff_pos
  let p := n/R*W+j.val
  have div : (p*R+n%R)/R = p := by
    rw [Nat.mul_comm p, Nat.mul_add_div hr, Nat.div_eq_of_lt (Nat.mod_lt _ hr), Nat.add_zero]
  have rem : (p*R+n%R)%R = n%R := by
    rw [Nat.mul_comm p, Nat.mul_add_mod, Nat.mod_mod]
  have divW : p / W = n/R := by
    rw [show p = W*(n/R)+j.val by dsimp [p]; ac_rfl, Nat.mul_add_div hW, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have remW : p % W = j.val := by
    rw [show p = W*(n/R)+j.val by dsimp [p]; ac_rfl, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
  change x ⟨(p*R+n%R)/R%W,_⟩ ((p*R+n%R)/R/W*R+(p*R+n%R)%R) = x j n
  simp only [div,rem,remW,divW,Fin.eta,Nat.div_add_mod']

private def cell (A W : ℕ) (s : Shape) (x : Data s)
    (g : Fin (groups W s)) (j : Fin W) (b : Fin (inner A s)) : Dusk.Pair :=
  Dusk.mark (x ((g.val*W+j.val)*inner A s+b.val))

private theorem flat_cells {A W : ℕ} (s : Shape) (hs : 0 < s.level) (hd : W^s.level ∣ s.pref) (x : Data s) :
    stream (List.finRange (groups W s)) (fun g j => List.ofFn (cell A W s x g j)) = flat A s x := by
  rw [stream_rect]
  apply List.ext_getElem
  · simp [flat,count,groups_mul hs hd]
  · intro t ht hidx
    simp only [flat,List.getElem_ofFn,List.getElem_map,List.getElem_range,Function.comp_apply,cell]
    change Dusk.mark (x (((t/inner A s/W)*W+(t/inner A s)%W)*inner A s+t%inner A s)) = _
    rw [Nat.div_add_mod', Nat.div_add_mod']

/-- The grid-template header enumerates exactly `groups * inner` scalar
addresses on each lane of a nonterminal node. -/
theorem coords_range (a W : ℕ) (s : Shape) (hs : 0 < s.level) :
    (coords a W).rows s = List.range (groups W s * inner (a+1) s) := by
  have w := Header.grid_width W a s hs
  change (a+1)*(2*(a+1)^(s.level-1)) = grow (a+1) s.level at w
  change List.range (groups W s * (2^((a+1)*(2*(a+1)^(s.level-1)))*s.suff)) = _
  rw [w]
  rfl

private theorem bank_cells {a W : ℕ} (s : Shape) (hs : 0 < s.level) (x : Data s) :
    rows (List.finRange (groups W s)) (fun g j => List.ofFn (cell (a+1) W s x g j)) =
      (packet (PhysicalWalshGrid.layout (coords a W) Shape.w) s (lane (a+1) W s x)).2 := by
  rw [rows_rect]
  apply congrArg List.ofFn
  funext j
  change _ = ((coords a W).rows s).map _
  rw [coords_range _ _ s hs]
  apply List.ext_getElem
  · simp
  · intro t ht hidx
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
    rfl

/-- The resident parent bank volume, used by both full-stream permutations. -/
def nodeVolume (A : ℕ) (s : Shape) := (count A s+1)*(s.w+1)

private theorem rectangular_volume (A W : ℕ) (s : Shape) :
    (groups W s+1)*(inner A s+1)*(4*(s.w+1)+3+1) ≤ 32 * nodeVolume A s := by
  have hg : 1 ≤ groups W s := Nat.le_max_left ..
  have hi : 1 ≤ inner A s := Nat.mul_pos (pow_pos (by decide) _) s.suff_pos
  have hp : groups W s ≤ s.pref := max_le s.pref_pos (Nat.div_le_self ..)
  calc
    _ ≤ (2*(groups W s))*(2*(inner A s))*(8*(s.w+1)) := by gcongr <;> omega
    _ = 32*(groups W s * inner A s)*(s.w+1) := by ring
    _ ≤ 32*(s.pref * inner A s + 1)*(s.w+1) := by gcongr; exact (Nat.mul_le_mul_right _ hp).trans (Nat.le_succ _)
    _ = _ := by unfold nodeVolume count; ring

variable {I : Type} {a W : ℕ} (s : I → Shape)
  (level : ∀ i, 0 < (s i).level) (divisible : ∀ i, W^(s i).level ∣ (s i).pref)

include level divisible

private theorem nodePaths (x : ∀ i, Data (s i)) :
    let V := nodeVolume (a+1) ∘ s
    let flat i := send (Header.cuts (a+1) W (s i),flat (a+1) (s i) (x i))
    let bank i := send (Header.cuts (a+1) W (s i),
      (packet (PhysicalWalshGrid.layout (coords a W) Shape.w) (s i) (lane (a+1) W (s i) (x i))).2)
    BoundedTask V V flat bank ∧ BoundedTask V V bank flat := by
  intro V flat bank
  have z := rectangularTasks (fun i => groups W (s i)) (fun i => inner (a+1) (s i))
    (fun i => 4*((s i).w+1)+3) (fun i => cell (a+1) W (s i) (x i)) (fun _ _ _ _ => (Dusk.volume _).le)
  have h (i : I) : (groups W (s i)+1)*(inner (a+1) (s i)+1)*(4*((s i).w+1)+3+1)+1 ≤ 32*(V i+1) := by
    have hi := rectangular_volume (a+1) W (s i)
    change _ ≤ 32*(V i) at hi
    omega
  simp only [flat_cells _ (level _) (divisible _), bank_cells _ (level _)] at z
  exact ⟨z.1.bound 32 32 h h,z.2.bound 32 32 h h⟩

/-- Split the address-ordered parent into the template's serialized argument bank. -/
theorem nodeSplit (x : ∀ i, Data (s i)) :
    BoundedTask (nodeVolume (a+1) ∘ s) (nodeVolume (a+1) ∘ s)
      (fun i => send (Header.cuts (a+1) W (s i),flat (a+1) (s i) (x i)))
      (fun i => send (Header.cuts (a+1) W (s i),
        (packet (PhysicalWalshGrid.layout (coords a W) Shape.w) (s i) (lane (a+1) W (s i) (x i))).2)) :=
  (nodePaths s level divisible x).1

/-- Reassemble an arbitrary template result bank in parent address order. -/
theorem nodeMerge (hW : 0 < W) (y : (i : I) → Fin W → Data (s i)) :
    BoundedTask (nodeVolume (a+1) ∘ s) (nodeVolume (a+1) ∘ s)
      (fun i => send (Header.cuts (a+1) W (s i),
        (packet (PhysicalWalshGrid.layout (coords a W) Shape.w) (s i) (y i)).2))
      (fun i => send (Header.cuts (a+1) W (s i),flat (a+1) (s i) (unlane (a+1) hW (s i) (y i)))) := by
  simpa only [lane_unlane] using
    (nodePaths (a := a) s level divisible (fun i => unlane (a+1) hW (s i) (y i))).2

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
