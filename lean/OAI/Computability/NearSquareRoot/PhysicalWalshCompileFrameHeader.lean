import OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildLiteral
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeFrames

/-! # Specializing the physical frame descriptor for all template arities

The generated key contains a cut ruler per group, the grid header, and the
wire to be returned when the work bank has finished. A single descriptor
program reads the arity and the batch width as literals.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.FrameHeader

open IntegerMultiplication Code Space Staff Carry Strip PhysicalWalsh PhysicalWalshNode
open PhysicalWalshCompileChild CommonRegisters GeneratorSyntax Filter
open private arity batch wire active width prefFigure suffix childBits from OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildHeader
open private supply from OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildLiteral
open private size_copies from OAI.Computability.NearSquareRoot.PhysicalWalshChildLanes

abbrev Fields := List Tally × PhysicalWalshGrid.Header × Header.Wire

def rulers (a W : ℕ) (s : Shape) := List.replicate (groups W s) (tally (inner (a+1) s))

def fields (a W : ℕ) (s : Shape) : Fields :=
  (rulers a W s,PhysicalWalshGrid.header (coords a W) Shape.w s,Header.wire (a+1) s)

private theorem groupFig : Figure regime (fun t : World => groups t.W t.shape) :=
  (Figure.natural 1).maximum (prefFigure.quotients (Figure.of_spoken batch))

private theorem gridMint : Mint regime (fun t : World => PhysicalWalshGrid.header (coords t.a t.W) Shape.w t.shape) := by
  have span := arity.times childBits
  have power := (Figure.natural 2).repeated span
  have n := groupFig.multiplied (power.multiplied suffix)
  have mk := ((Mint.tally n).pair (Mint.of_has width)).pair
    (((Mint.tally groupFig).pair (Mint.tally suffix)).pair (Mint.of_has span))
  convert mk using 1
  funext t
  simp only [PhysicalWalshGrid.header,KernelScaleBank.count_eq,Function.comp_apply]
  rfl

private theorem rulerMint : Mint regime (fun t : World => rulers t.a t.W t.shape) := by
  let cuts (t : World) := Header.cuts (t.a+1) t.W t.shape
  have innerF : Figure regime (fun t : World => inner (t.a+1) t.shape) :=
    ((Figure.natural 2).repeated active).multiplied suffix
  obtain ⟨clock,dc,calcCuts⟩ := (show Mint regime cuts from (Mint.tally groupFig).pair (Mint.tally innerF))
  refine ⟨clock,dc,?_⟩
  have copied := (generate (X := Tally)).on cuts
  simp only [cuts,Header.cuts,tally_length] at copied
  apply (calcCuts.compose copied).bound 9
  intro t
  let g := groups t.W t.shape
  let x := tally (inner (t.a+1) t.shape)
  have hg : 1 ≤ g := Nat.le_max_left ..
  have hx := Nat.le_mul_of_pos_left (size x) hg
  have hG := Nat.le_mul_of_pos_right g (Nat.succ_pos (size x))
  change clock t + size (tally g,x) + (g+1)*size x + 1 ≤ 9*(clock t + size (List.replicate g x)+1)
  simp only [size_prod,size_copies,size_tally (tally g),tally_length]
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_add,Nat.mul_one] at *
  omega

/-- The cost includes every emitted ruler cell; the compact computation has a
single polynomial degree for all template arities and batch widths. -/
theorem minted : Mint regime (fun t : World => fields t.a t.W t.shape) :=
  rulerMint.pair (gridMint.pair (Mint.of_has wire))

private theorem fields_size (a W : ℕ) (s : Shape) (hs : 0 < s.level) {d : ℕ} (hd : 1 ≤ d) :
    size (fields a W s) ≤ 70*(allowance (a+1) d s+1) := by
  let A := a+1
  let v := allowance A d s
  have grid := Header.grid_size W a s hs
  have wit : Header.scale A s ≤ v := by
    have p := Nat.pow_le_pow_right (Nat.succ_pos (Header.scale A s)) hd
    rw [pow_one] at p
    exact (Nat.le_succ _).trans (p.trans (Nat.le_add_left ..))
  have vol := nodeVolume_le A d s
  have gross : count A s+s.w+1 ≤ v := by
    apply le_trans _ vol
    dsimp [nodeVolume]; nlinarith
  have g : groups W s ≤ s.pref := max_le s.pref_pos (Nat.div_le_self ..)
  have innerP : 1 ≤ inner A s := Nat.mul_pos (pow_pos (by decide) _) s.suff_pos
  have small : groups W s*(2*inner A s+2) ≤ 4*count A s := by
    calc
      _ ≤ s.pref*(4*inner A s) := Nat.mul_le_mul g (by omega)
      _ = _ := by dsimp [PhysicalWalshNode.count]; ring
  change size (List.replicate (groups W s) (tally (inner A s))) +
    (size (PhysicalWalshGrid.header (coords a W) Shape.w s) + Header.scale A s + 1) + 1 ≤ 70*(v+1)
  rw [size_copies,size_tally,tally_length]
  change _ ≤ 10*(count A s+s.w+1)+8 at grid
  change groups W s*(2*inner A s+2)+1 + (_ + Header.scale A s +1)+1 ≤ 70*(v+1)
  omega

/-- One effective command per `(a,W)` generates the frame key and uses a
uniform register bound. Per-command constants may depend on the template. -/
theorem compiled : ∃ (emit : ℕ × ℕ → Cmd) (N d : ℕ), Effective ltr emit ∧ 1 ≤ d ∧
    (∀ k, Within N (emit k)) ∧ ∀ a W, ∃ C : ℕ, ∀ s : Shape, 0 < s.level →
    (∀ env park, Fits env (emit (a,W)) (pile 0 (send (Header.wire (a+1) s)) park)
      (pile 0 (send (fields a W s)) park) (C*(allowance (a+1) d s+1))) ∧
      size (fields a W s) ≤ C*(allowance (a+1) d s+1) := by
  obtain ⟨clock,dom,body,K,r⟩ := minted
  obtain ⟨d,D,dc⟩ := dom
  obtain ⟨N,hr,rb⟩ := ((eventually_ge_atTop 3).and (RegisterSelect.within_eventually body)).exists
  obtain ⟨pre,ep,hpre⟩ := supply hr
  let key (k : ℕ × ℕ) : Control := (k.1+1,k.2,0)
  have hk : Computable key := (Computable.succ.comp Computable.fst).pair (Computable.snd.pair (Computable.const 0))
  refine ⟨fun k => (pre (key k)).join body,N,d+1,(show Effective ltr (pre ∘ key) from ep.comp hk).join
    (effective_const ltr body),by omega,fun k => ⟨(hpre _).1,rb⟩,?_⟩
  intro a W
  let k := key (a,W)
  obtain ⟨B,hB⟩ := (hpre k).2
  let P := size (params k.1 k.2.1 k.2.2)+2
  let C := D*P^d
  refine ⟨B+K*(C+71)+72,fun s hs => ?_⟩
  let t : World := ⟨a,W,0,s⟩
  let v := allowance (a+1) (d+1) s
  let n := Header.scale (a+1) s+1
  have en : 0 < n := Nat.succ_pos _
  have nd : n^d ≤ v := (Nat.pow_le_pow_right en (Nat.le_succ _)).trans (Nat.le_add_left ..)
  have nv : n ≤ v := by
    have := Nat.pow_le_pow_right en (show 1 ≤ d+1 by omega)
    rw [pow_one] at this
    exact this.trans (Nat.le_add_left ..)
  have inp : regime.scale t+1 ≤ P*n := by
    change size (params (a+1) W 0)+Header.scale (a+1) s+1+1 ≤ (size (params (a+1) W 0)+2)*(Header.scale (a+1) s+1)
    rw [Nat.mul_succ,Nat.add_mul]; omega
  have cost := (dc t).trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left inp d))
  rw [mul_pow,← Nat.mul_assoc] at cost
  have cv : clock t ≤ C*(v+1) := cost.trans (Nat.mul_le_mul_left _ (nd.trans (Nat.le_succ _)))
  have vol := fields_size a W s hs (d := d+1) (by omega)
  change size (fields a W s) ≤ 70*(v+1) at vol
  have localCost : clock t+size (fields a W s)+1 ≤ (C+71)*(v+1) := by rw [Nat.add_mul]; omega
  constructor
  · intro env park
    have first := hB (Header.wire (a+1) s) env park
    have second := r t env park
    apply (first.join second).mono
    have hp := Nat.mul_le_mul_left B (nv.trans (Nat.le_succ _))
    change B*n ≤ B*(v+1) at hp
    have hb := Nat.mul_le_mul_left K localCost
    rw [← Nat.mul_assoc] at hb
    change B*n + K*(clock t+size (fields a W s)+1)+2 ≤ (B+K*(C+71)+72)*(v+1)
    simp only [Nat.add_mul]; omega
  · change _ ≤ (B+K*(C+71)+72)*(v+1)
    simp only [Nat.add_mul]; omega

end PhysicalWalshCompile.FrameHeader

end NearSquareRoot
end Computability
end OAI
