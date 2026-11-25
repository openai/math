import OAI.Computability.NearSquareRoot.PhysicalWalshNodeMachine

/-! # A packed column gate on a compact descriptor and one flat array

The permutation sees a single ordered list of complete records. The Walsh
caller retains its own header and restores the singleton bank on return.
When both column indices coincide the caller simply returns its input.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode
open IntegerMultiplication Code Space PhysicalWalsh

/-- One bank lane in increasing physical order. Its leading and trailing
spectator ranges may have any positive size. -/
def laneFlat (A W : ℕ) (s : Shape) (x : Data s) :=
  (List.range (groups W s * inner A s)).map (Dusk.mark ∘ x)

/-- Contract of the standalone permutation. Input is exactly the compact
descriptor followed by the record list, output is the record list alone. -/
def FlatXorRuns (a W : ℕ) (scan arena : Shape → ℕ) :=
  ∀ g : Fin (a+1) × Fin (a+1), g.1 ≠ g.2 →
    BoundedTask (fun t : XorInput W => scan t.shape) (fun t => arena t.shape)
      (fun t => .fork (send (Header.wire (a+1) t.shape)) (send (laneFlat (a+1) W t.shape t.row)))
      (fun t => send (laneFlat (a+1) W t.shape (xor a g t.shape t.row)))

@[simp] theorem xorIndex_diag (a : ℕ) (i : Fin (a+1)) (s : Shape) (n : ℕ) :
    xorIndex a (i,i) s n = n := by
  let h := (a+1)^(s.level-1)
  let D := 2^((a+1)*(2*h))
  have Dpos : 0 < D := pow_pos (by decide) _
  have e : KernelPass.xorColumn (i,i) ∘ KernelScaleLayout.coord a h s.suff n =
      KernelScaleLayout.coord a h s.suff n := by funext j k b; simp [KernelPass.xorColumn]
  have r := KernelScaleLayout.rank_address (a:=a) (h:=h) (⟨(n/s.suff)%D,Nat.mod_lt _ Dpos⟩ : Fin D)
  change (n/s.suff/D*D+(KernelScaleLayout.rank (KernelPass.xorColumn _ ∘ KernelScaleLayout.coord a h s.suff n)).val)*s.suff+n%s.suff = n
  rw [e]
  change (n/s.suff/D*D+(KernelScaleLayout.rank (KernelScaleLayout.address a h ((n/s.suff)%D))).val)*s.suff+n%s.suff = n
  rw [congrArg Fin.val r]
  rw [Nat.div_add_mod', Nat.div_add_mod']

private abbrev Saved := PhysicalWalshGrid.Header × Header.Wire
private abbrev Stream := List Dusk.Pair

private def prep (z : Saved × List Stream) := ((z.1.2,z.2.headD []),z.1)
private def done_ (z : Stream × Saved) := (z.2,[z.1])

private theorem prep_easy : Easy prep :=
  ((Easy.fst.compose Easy.snd).pair (Easy.snd.compose (Iter.leader []))).pair Easy.fst
private theorem done_easy : Easy done_ := by unfold done_; fun_prop

/-- In this wrapper, a superlinear routing clock does not inflate the workspace
used to save the caller's header. -/
theorem xorRuns_of_flat {a W : ℕ} {scan arena : Shape → ℕ} (cost : ∀ s, arena s ≤ scan s)
    (fit : ∀ s, PhysicalWalshContext.routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ arena s)
    (routes : FlatXorRuns a W scan arena) : XorRuns a W scan arena := by
  let m : Meter Shape := ⟨scan,arena,cost,fun _ _ _ _ => True⟩
  let L := work a W
  have room : FitsLayout m L := PhysicalWalshContext.fitsLayout _ _ _ fit
  let s : XorInput W → Shape := XorInput.shape
  let pkt (x : (t : XorInput W) → Data (s t)) t := packet L (s t) (fun _ : Fin 1 => x t)
  have store (t : XorInput W) (x : Data t.shape) : L.store t.shape x = laneFlat (a+1) W t.shape x := by
    change ((coords a W).rows t.shape).map _ = _
    rw [coords_range a W t.shape t.positive]; rfl
  have singleton (t : XorInput W) (x : Data (s t)) :
      packet L (s t) (fun _ : Fin 1 => x) = (L.header (s t), [laneFlat (a+1) W (s t) x]) := by
    rw [← store t x]; rfl
  intro g
  by_cases equal : g.1 = g.2
  · obtain ⟨i,j⟩ := g
    dsimp only at equal; subst j
    have idgate (t : XorInput W) : xor a (i,i) t.shape t.row = t.row := by funext n; simp [xor]
    simp only [idgate]
    exact (PhysicalWalshGrid.easyWithin (arena ∘ s) Easy.identity (pkt XorInput.row) 4
      (fun t => room.packet _ _)).mono (fun t => cost (s t)) (fun _ => le_rfl)
  let y := fun t : XorInput W => xor a g (s t) t.row
  let x := fun t : XorInput W => laneFlat (a+1) W (s t) t.row
  let out := fun t : XorInput W => laneFlat (a+1) W (s t) (y t)
  let head := fun t : XorInput W => L.header (s t)
  have sh (t : XorInput W) : size (head t) ≤ arena (s t) := room.header _
  have sz (t : XorInput W) : size (out t) ≤ arena (s t) := by
    change size (laneFlat (a+1) W t.shape (y t)) ≤ arena (s t)
    rw [← store t (y t)]; exact room.row _ _
  have start := PhysicalWalshGrid.easyWithin (arena ∘ s) prep_easy (pkt XorInput.row) 4 (fun t => room.packet _ _)
  have finish := PhysicalWalshGrid.easyWithin (arena ∘ s) done_easy (fun t => (out t,head t)) 3 (fun t => by
    have hh := sh t; have h := sz t; change size (out t)+size (head t)+1 ≤ 3*(arena (s t)+1); omega)
  have body := (routes g equal).left (fun t => send (head t))
  have middle : BoundedTask (scan ∘ s) (arena ∘ s)
      (fun t => send (prep (pkt XorInput.row t))) (fun t => send (out t,head t)) := by
    have real := body.bound (time' := scan ∘ s) (space' := arena ∘ s) 1 2 (fun _ => by simp [s]) (fun t => by
      have e := sh t
      change arena (s t) + size (head t)+1 ≤ 2*(arena (s t)+1); omega)
    apply real.conform (fun _ => rfl) (fun _ => rfl) (fun t => ?_) (fun _ => rfl)
    simp only [pkt,singleton,prep,List.headD_cons]; rfl
  have h := (start.compose middle).compose finish
  have bound := h.bound (time' := scan ∘ s) (space' := arena ∘ s) 3 1 (fun t => by
    change arena (s t)+scan (s t)+arena (s t)+1 ≤ 3*(scan (s t)+1)
    have := cost (s t); omega) (fun _ => by simp)
  apply bound.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun t => ?_)
  rw [singleton]; rfl

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
