import OAI.Computability.NearSquareRoot.PhysicalWalshNodeXorBits

/-! # Routing an arbitrary axis XOR through a fixed three-slot gate

Two whole-slot interchanges place the source and target at the prescribed
positions. Reversing the pair after the gate restores all spectator slots.
Each interchange acts on an entire equal-width window at once.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.Route
open IntegerMultiplication Code Space PhysicalWalsh KernelPass KernelScaleLayout

abbrev Active (a : ℕ) (s : Shape) := Addr (a+1) ((a+1)^(s.level-1))

def key {a : ℕ} (s : Shape) (f : Active a s → Active a s) (n : ℕ) : ℕ :=
  let M := 2^((a+1)*(2*((a+1)^(s.level-1))))
  (n/s.suff/M*M+(rank (f (coord a _ s.suff n))).val)*s.suff+n%s.suff

/-- Split off the exact leading row and the suffix on both sides of a stage. -/
theorem key_comp {a : ℕ} (s : Shape) (f g : Active a s → Active a s) (n : ℕ) :
    key s f (key s g n) = key s (f ∘ g) n := by
  let h := (a+1)^(s.level-1)
  let M := 2^((a+1)*(2*h))
  let row := n/s.suff/M
  let u := g (coord a h s.suff n)
  have mn : 0<M := Nat.two_pow_pos _
  have low : (rank u).val<M := (rank u).isLt
  let p := (row*M+(rank u).val)*s.suff+n%s.suff
  have pv : p/s.suff = row*M+(rank u).val := by
    rw [show p=s.suff*(row*M+(rank u).val)+n%s.suff from by dsimp [p];ring, Nat.mul_add_div s.suff_pos,
      Nat.div_eq_of_lt (Nat.mod_lt n s.suff_pos),Nat.add_zero]
  have ps : p%s.suff = n%s.suff := by
    rw [show p=s.suff*(row*M+(rank u).val)+n%s.suff from by dsimp [p];ring,Nat.mul_add_mod,Nat.mod_mod]
  have hp : p/s.suff/M = row := by rw [pv,Nat.mul_comm row M,Nat.mul_add_div mn,Nat.div_eq_of_lt low,Nat.add_zero]
  have slot : coord a h s.suff p = u := by
    unfold coord
    change address a h (p/s.suff%M) = u
    rw [pv,Nat.mul_comm row M,Nat.mul_add_mod,Nat.mod_eq_of_lt low,address_rank]
  change (p/s.suff/M*M+(rank (f (coord a h s.suff p))).val)*s.suff+p%s.suff = (row*M+(rank (f u)).val)*s.suff+n%s.suff
  rw [hp,slot,ps]

/-- Reorder the equal-width windows within the complete active part. -/
def axes {a h : ℕ} (π : Equiv.Perm (Fin (a+1))) (x : Addr (a+1) h) : Addr (a+1) h :=
  fun j k => x j (π k)

def axisSwap {a : ℕ} (i j : Fin (a+1)) (s : Shape) (x : Data s) : Data s := x ∘ key s (axes (Equiv.swap i j))

private theorem conjugate {A h : ℕ} (π : Equiv.Perm (Fin (A+1))) (dst src : Fin (A+1))
    (u : Addr (A+1) h) :
    axes π (xorColumn (π dst,π src) ∘ axes π.symm u) = xorColumn (dst,src) ∘ u := by
  funext j k b
  simp only [axes,Function.comp_apply,xorColumn,π.injective.ne_iff,π.injective.eq_iff,
    Equiv.symm_apply_apply]

/-- Apply source swap, target swap, the fixed-position XOR, and the same
swaps in reverse order. This equality holds at every physical ordinal. -/
theorem swap_route {a : ℕ} (dst src target source : Fin (a+1)) (hds : dst ≠ src) (hts : target ≠ source)
    (s : Shape) (x : Data s) :
    let first := Equiv.swap src source
    let j := first dst
    axisSwap src source s (axisSwap j target s
      (xor a (target,source) s (axisSwap j target s (axisSwap src source s x)))) = xor a (dst,src) s x := by
  intro first j
  let second := Equiv.swap j target
  let π := first.trans second
  have hf : first src = source := Equiv.swap_apply_left ..
  have hn : j ≠ source := fun h => hds (first.injective (h.trans hf.symm))
  have hs : π src = source := by
    change second (first src) = source; rw [hf,Equiv.swap_apply_of_ne_of_ne hn.symm hts.symm]
  have hd : π dst = target := Equiv.swap_apply_left ..
  funext n
  change x (key s (axes first) (key s (axes second) (key s (fun z => xorColumn (target,source) ∘ z)
    (key s (axes second) (key s (axes first) n))))) = x (key s (fun z => xorColumn (dst,src) ∘ z) n)
  simp only [key_comp]
  apply congrArg x
  apply congrArg (fun f => key s f n)
  funext z
  change axes π (xorColumn (target,source) ∘ axes π.symm z) = _
  rw [← hd,← hs,conjugate π dst src]

/-- A standalone gate consumes the descriptor and returns just the ordered
record stream. Its semantic input is a single complete lane. -/
def FlatRun {W : ℕ} (a : ℕ) (scan arena : Shape → ℕ) (F : (s : Shape) → Data s → Data s) :=
  BoundedTask (fun t : XorInput W => scan t.shape) (fun t => arena t.shape)
    (fun t => send (Header.wire (a+1) t.shape, laneFlat (a+1) W t.shape t.row))
    (fun t => send (laneFlat (a+1) W t.shape (F t.shape t.row)))

/-- Forward convention for the shared wrapper giving a complete input
packet to the second physical pass and reusing the side storage. -/
theorem FlatRun.chain {a W : ℕ} {scan arena : Shape → ℕ} (cost : ∀ s, arena s ≤ scan s)
    (fit : ∀ s, PhysicalWalshContext.routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ arena s)
    {F G : (s : Shape) → Data s → Data s} (first : FlatRun (W:=W) a scan arena F)
    (second : FlatRun (W:=W) a scan arena G) : FlatRun (W:=W) a scan arena (fun s x => G s (F s x)) := by
  let m : Meter Shape := ⟨scan,arena,cost,fun _ _ _ _ => True⟩
  have size := PhysicalWalshContext.fitsLayout (m:=m) (coords a W) Shape.w (Header.wire (a+1)) fit
  let u := fun t : XorInput W => t.shape
  let head := fun t : XorInput W => Header.wire (a+1) (u t)
  let x := fun t : XorInput W => laneFlat (a+1) W (u t) t.row
  let next := fun t : XorInput W => {t with row := F (u t) t.row}
  have hH (t : XorInput W) : Code.size (head t) ≤ arena (u t) := by
    have h := size.header (u t)
    change Code.size (PhysicalWalshGrid.header (coords a W) Shape.w (u t)) + Code.size (head t)+1 ≤ arena (u t) at h
    omega
  have hR (t : XorInput W) (v : Data (u t)) : Code.size (laneFlat (a+1) W (u t) v) ≤ arena (u t) := by
    have r := size.row (u t) v
    change Code.size (((coords a W).rows (u t)).map (Dusk.mark ∘ v)) ≤ _ at r
    rw [coords_range _ _ _ t.positive] at r; exact r
  let dup := fun z : Header.Wire × List Dusk.Pair => (z,z.1)
  have pre := PhysicalWalshGrid.easyWithin (arena ∘ u) (show Easy dup from Easy.identity.pair Easy.fst)
    (fun t => (head t,x t)) 3 (fun t => by
      change Code.size (head t)+Code.size (x t)+1 ≤ 3*(arena (u t)+1)
      have h := hH t; have h' := hR t t.row; change Code.size (x t) ≤ _ at h';omega)
  have body := first.left (send ∘ head)
  have short := body.bound (time' := scan ∘ u) (space' := arena ∘ u) 1 2
    (fun _ => by simp [u]) (fun t => by have := hH t; change arena (u t)+Code.size (head t)+1 ≤ 2*(arena (u t)+1);omega)
  have rearrange := PhysicalWalshGrid.easyWithin (arena ∘ u) (Easy.exchange (X:=List Dusk.Pair) (Y:=Header.Wire))
    (fun t => (laneFlat (a+1) W (u t) (F (u t) t.row),head t)) 3 (fun t => by
      change Code.size (laneFlat (a+1) W (u t) (F (u t) t.row))+Code.size (head t)+1 ≤ 3*(arena (u t)+1);have := hH t;have := hR t (F (u t) t.row);omega)
  have out := ((pre.compose short).compose rearrange).compose (second.on next)
  apply out.bound 4 1
  · intro t;change arena (u t)+scan (u t)+arena (u t)+scan (u t)+1 ≤ 4*(scan (u t)+1);have := cost (u t);omega
  · intro t;change max (max (max (arena (u t)) (arena (u t))) (arena (u t))) (arena (u t))+1 ≤ 1*(arena (u t)+1); simp

/-- Every arbitrary-axis gate reduces to the two fixed-position primitives,
with no change to the scale-dependent time or space factors. -/
theorem flatXorRuns {a W : ℕ} {scan arena : Shape → ℕ} (cost : ∀ s, arena s ≤ scan s)
    (fit : ∀ s, PhysicalWalshContext.routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ arena s)
    (target source : Fin (a+1)) (apart : target ≠ source)
    (swap : ∀ i j : Fin (a+1), FlatRun (W:=W) a scan arena (axisSwap i j))
    (front : FlatRun (W:=W) a scan arena (xor a (target,source))) : FlatXorRuns a W scan arena := by
  rintro ⟨dst,src⟩ hds
  let j := Equiv.swap src source dst
  have run := ((((swap src source).chain cost fit (swap j target)).chain cost fit front).chain cost fit (swap j target)).chain cost fit (swap src source)
  refine run.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun t => ?_)
  exact congrArg (fun y => send (laneFlat (a+1) W t.shape y)) (swap_route dst src target source hds apart t.shape t.row)

end PhysicalWalshNode.Route

end NearSquareRoot
end Computability
end OAI
