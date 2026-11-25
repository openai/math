import OAI.Computability.NearSquareRoot.PhysicalWalshXorInteriorHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshXorThreshold

/-! # Computing the interior XOR branch from the compact descriptor -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code Staff Strip Carry Space PhysicalWalsh
open private level active recordWidth pref from OAI.Computability.NearSquareRoot.PhysicalWalshNodeHeader

/-- Recover the serialized descriptor size from its five fields. -/
theorem scaleFigureOf {I : Type} {r : Regime I} (A : I → ℕ) (s : I → Shape)
    (level : Realizes r (fun t => (s t).level)) (active : Realizes r (fun t => grow (A t) (s t).level))
    (width : Realizes r (fun t => (s t).w+1)) (pref : Figure r (fun t => (s t).pref))
    (suff : Figure r (fun t => (s t).suff)) : Figure r (fun t => Header.scale (A t) (s t)) := by
  have counts := (((level.plus active).plus width).plus ((pref.added (Figure.natural 1)).short_log)).plus
    ((suff.added (Figure.natural 1)).short_log)
  have out := ((Realizes.fix 2).times counts).plus (Realizes.fix 9)
  exact (funext (fun t => Header.scale_exact (A t) (s t))) ▸ Figure.of_spoken out

/-- Classify the large-window case from the available descriptor fields. -/
theorem hasComparison {I : Type} {r : Regime I} {D Q L : I → ℕ}
    (degree : Realizes r D) (scale : Figure r Q) (width : Realizes r L) :
    r.Has (fun t => decide (XorThreshold.cutoff (D t) (Q t) ≤ L t)) := by
  have bits := (scale.added (Figure.natural 1)).short_log
  have cut : Figure r (fun t => XorThreshold.cutoff (D t) (Q t)) :=
    (Figure.natural 6).maximum (Figure.of_spoken (degree.times bits))
  have end_ := (Figure.of_spoken width).added (Figure.natural 1)
  obtain ⟨f,hf,iff⟩ := cut.compare_ end_
  have eq : f = fun t => decide (XorThreshold.cutoff (D t) (Q t) ≤ L t) := by
    funext s
    have h := iff s
    cases flag : f s <;> simp [flag] at h <;> simp <;> omega
  exact eq ▸ hf

private def tag (a D : ℕ) (s : Shape) : Bool :=
  decide (XorThreshold.cutoff D (Header.scale (a+1) s) ≤ Interior.L (a+1) s)

private theorem hasTag (a D : ℕ) : (Header.regime (a+1)).Has (tag a D) := by
  let A := a+1
  have scale := scaleFigureOf (fun _ => A) id (level A) (active A) (recordWidth A) (pref A) (Header.suff A)
  exact hasComparison (Realizes.fix D) scale (Interior.realizes_L A (by dsimp [A]; omega))

private def unpack (x : (Bool × Header.Wire) × List Dusk.Pair) := (x.1.1,x.1.2,x.2)

private theorem easy_unpack : Easy unpack := by unfold unpack; fun_prop

/-- Tag a flat packet with the exact threshold used by the native gate. The
polynomial setup reads the compact descriptor while its record row is parked. -/
theorem selector (a W D : ℕ) : ∃ e : ℕ, ∀ d, e ≤ d →
    let v := fun t : XorInput W => allowance (a+1) d t.shape
    let packet := fun t : XorInput W =>
      Tree.fork (send (Header.wire (a+1) t.shape)) (send (laneFlat (a+1) W t.shape t.row))
    BoundedTask v v packet (fun t => .fork (.atom (decide
      (XorThreshold.cutoff D (Header.scale (a+1) t.shape) ≤ Interior.L (a+1) t.shape))) (packet t)) := by
  let A := a+1
  let s := fun t : XorInput W => t.shape
  let hd := fun t : XorInput W => Header.wire A t.shape
  let row := fun t : XorInput W => laneFlat A W t.shape t.row
  have keep := (hasTag a D).pair (show (Header.regime A).Has (Header.wire A) from (Header.regime A).self)
  obtain ⟨clock,dom,computation⟩ := keep
  obtain ⟨e,C,hclock⟩ := dom
  refine ⟨max 1 e,?_⟩
  intro d ed
  let v := fun t : XorInput W => allowance A d (s t)
  have powle (j : ℕ) (hj : j ≤ d) (t : XorInput W) :
      (Header.scale A (s t)+1)^j ≤ v t :=
    (Nat.pow_le_pow_right (by omega) hj).trans (Nat.le_add_left ..)
  have sc (t : XorInput W) : size (hd t) ≤ v t := by
    have h := powle 1 ((le_max_left ..).trans ed) t
    change Header.scale A (s t) ≤ v t
    rw [pow_one] at h
    omega
  have cr (t : XorInput W) : clock (s t) ≤ C*v t :=
    (hclock (s t)).trans (Nat.mul_le_mul_left C (powle e ((le_max_right ..).trans ed) t))
  have sr (t : XorInput W) : size (row t) ≤ 16*v t+1 :=
    SwapPrefix.stream_cost A W d (s t) _ t.row (SwapPrefix.length_le A W (s t))
  let word := fun t : XorInput W => tag a D (s t)
  have data := ((computation.on s).left (send ∘ row)).compose
    (easy_unpack.on (fun t => ((word t,hd t),row t)))
  apply (BoundedTask.of_time data).bound (C+22) (C+40) <;> intro t
  · have := cr t; have := sc t; have := sr t
    change clock (s t)+size ((word t,hd t),row t)+1 ≤ (C+22)*(v t+1)
    simp only [size_prod]
    change clock (s t) + (1+size (hd t)+1+size (row t)+1) +1 ≤ _
    rw [Nat.add_mul,Nat.mul_add,Nat.mul_one]; omega
  · have := cr t; have := sc t; have := sr t
    change size (hd t,row t)+(clock (s t)+size ((word t,hd t),row t))+1 ≤ (C+40)*(v t+1)
    simp only [size_prod]
    change size (hd t)+size (row t)+1+(clock (s t)+(1+size (hd t)+1+size (row t)+1))+1 ≤ _
    rw [Nat.add_mul,Nat.mul_add,Nat.mul_one]; omega

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
