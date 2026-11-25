import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSpec
import OAI.Computability.NearSquareRoot.PhysicalWalshChildAdapter
import OAI.Computability.NearSquareRoot.PhysicalWalshContext

/-! # Calling the normalized recursive command on a physical work lane

At each child entry the parent layout enumerates precisely the child's flat
record interval. The parent header is reconstructed on return. The polynomial
degree and the code handling the finite set of slots are fixed independently
of the input width and the contents of the stream.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication Code KernelPass Space PhysicalWalsh

/-- Enriched row-bank layout with the compact descriptor beside the five
physical grid rulers. -/
abbrev work (a W : ℕ) := PhysicalWalshContext.routeLayout (coords a W) Shape.w (Header.wire (a+1))

private theorem flat_child {a W : ℕ} (axis : Fin (a+1)) (s : Shape) (pos : 0<s.level) (x : Data s) :
    (work a W).store s x = flat (a+1) (descend (a+1) W axis s) x := by
  have size := Header.grid_width W a s pos
  change (a+1)*(2*(a+1)^(s.level-1)) = grow (a+1) s.level at size
  change (List.range (groups W s*(2^((a+1)*(2*(a+1)^(s.level-1)))*s.suff))).map (Dusk.mark ∘ x) =
    (List.range (count (a+1) (descend (a+1) W axis s))).map (Dusk.mark ∘ x)
  rw [size, child_count s axis pos]
  rfl

private theorem row_budget {a W : ℕ} (axis : Fin (a+1)) (s : Shape) (pos : 0<s.level) (x : Data s) :
    size ((work a W).store s x) ≤ 8*(ChildAdapter.volume (a+1) s+1) := by
  rw [flat_child axis s pos x]
  let L := List.range (count (a+1) (descend (a+1) W axis s))
  have h (l : List ℕ) : size (l.map (Dusk.mark ∘ x)) = l.length*(4*(s.w+1)+4)+1 := by
    induction l with
    | nil => simp
    | cons z l ih => simp only [List.map_cons, List.length_cons, size_cons, Function.comp_apply, Dusk.volume, ih]; ring
  have cg : count (a+1) (descend (a+1) W axis s) ≤ count (a+1) s := by
    rw [child_count s axis pos]; exact Nat.mul_le_mul_right _ (max_le s.pref_pos (Nat.div_le_self ..))
  change size (L.map (Dusk.mark ∘ x)) ≤ _
  rw [h, List.length_range]
  apply le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ cg) 1)
  unfold ChildAdapter.volume
  ring_nf; omega

variable {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)

private theorem oneChild (axis : Fin (a+1)) : ∃ d : ℕ, ∀ scan arena : Shape → ℕ,
    ∀ cost : ∀ s, arena s ≤ scan s, (∀ s, allowance (a+1) d s ≤ arena s) →
    let vm :=  spec hw p scan arena cost
    let u := fun t : vm.Step => t.val.shape
    ∀ x : ∀ t, Rows (work a W) (u t) 1, (∀ t, Good hw p (descend (a+1) W axis (u t)) (x t 0)) →
    OpenRun vm.meter 1 u (fun t => send (packet (work a W) (u t) (x t)))
      (fun t => send (packet (work a W) (u t) (fun _ : Fin 1 => run hw p (descend (a+1) W axis (u t)) (x t 0)))) := by
  obtain ⟨d,C,h⟩ := ChildAdapter.boundedRows ([] : List Dusk.Pair) a W axis
  refine ⟨d,fun scan arena cost cap => ?_⟩
  intro vm u x ready
  let shape t := descend (a+1) W axis (u t)
  let y (t : vm.Step) := childInvocation hw p t.val t.property axis (x t 0) (ready t)
  let r (t : vm.Step) := (work a W).store (u t) (x t 0)
  let z (t : vm.Step) := (work a W).store (u t) (run hw p (shape t) (x t 0))
  have pos (t : vm.Step) : 0<(u t).level := t.property
  have fit := h u r z 8 pos (fun t => row_budget axis (u t) (pos t) _) (fun t => row_budget axis (u t) (pos t) _)
  obtain ⟨down,up,frame⟩ := fit
  let prec t := C*(Header.scale (a+1) (u t)+1)^d + ChildAdapter.volume (a+1) (u t)
  have fits (t) : prec t + 1 ≤ (C+1)*(arena (u t)+1) := by
    have bound := cap (u t)
    change (count (a+1) (u t)+1)*(grow (a+1) (u t).level+(u t).w+1)+(Header.scale (a+1) (u t)+1)^d ≤ arena (u t) at bound
    have vol : ChildAdapter.volume (a+1) (u t) ≤ arena (u t) := by
      unfold ChildAdapter.volume; rw [Nat.add_comm (u t).w]; omega
    have pow : (Header.scale (a+1) (u t)+1)^d ≤ arena (u t)+1 := by omega
    dsimp only [prec]; rw [Nat.succ_mul]; have := Nat.mul_le_mul_left C pow; omega
  have inc := down.bound (C+1) (C+1) fits fits
  have ret := up.bound (C+1) (C+1) fits fits
  have fw (t) : size (ChildAdapter.saved a W (u t)) ≤ (40*(8+1)*(C+1))*(arena (u t)+1) := by
    rw [Nat.mul_assoc, Nat.mul_assoc]
    exact (frame t).trans (Nat.mul_le_mul_left 40 (Nat.mul_le_mul_left (8+1) (fits t)))
  have hrec := childWithFrame vm u y (fun t => send (ChildAdapter.saved a W (u t)))
    (fun t => send (ChildAdapter.saved a W (u t), [r t])) (fun t => send (ChildAdapter.saved a W (u t), [z t]))
    (fun t => ⟨pos t,t.val.batches,axis,rfl⟩) _ fw
  have aeq (t) : r t = flat (a+1) (shape t) (x t 0) := flat_child axis _ (pos t) _
  have beq (t) : z t = flat (a+1) (shape t) (run hw p (shape t) (x t 0)) := flat_child axis _ (pos t) _
  have I := inc.mono (fun t => cost (u t)) (fun _ => le_rfl)
  have O := ret.mono (fun t => cost (u t)) (fun _ => le_rfl)
  have prog := hrec (I.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun t => by
    change (Tree.fork (Tree.fork _ (send (_, r t))) _) = Tree.fork (Tree.fork _ (send (_, flat (a+1) (shape t) (x t 0)))) _
    rw [aeq]; rfl)) (O.conform (fun _ => rfl) (fun _ => rfl) (fun t => by
      change (Tree.fork (send (_, z t)) _) = Tree.fork (send (_, flat (a+1) (shape t) (run hw p (shape t) (x t 0)))) _
      rw [beq]; rfl) (fun _ => rfl))
  exact prog

/-- One polynomial degree works for every slot of this fixed template. The
frame and output occupy the exact shape-local arena independently of clock. -/
theorem childCalls : ∃ d : ℕ, ∀ scan arena : Shape → ℕ, ∀ cost : ∀ s, arena s ≤ scan s,
    (∀ s, allowance (a+1) d s ≤ arena s) → let vm :=  spec hw p scan arena cost
    let u := fun t : vm.Step => t.val.shape
    ∀ axis (x : ∀ t, Rows (work a W) (u t) 1), (∀ t, Good hw p (descend (a+1) W axis (u t)) (x t 0)) →
    OpenRun vm.meter 1 u (fun t => send (packet (work a W) (u t) (x t)))
      (fun t => send (packet (work a W) (u t) (fun _ : Fin 1 => run hw p (descend (a+1) W axis (u t)) (x t 0)))) := by
  choose deg h using oneChild hw p
  refine ⟨Finset.univ.sup deg,fun scan arena cost room axis => h axis scan arena cost ?_⟩
  intro s
  exact (allowance_mono (Finset.le_sup (f := deg) (Finset.mem_univ axis)) s).trans (room s)

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
