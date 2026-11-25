import OAI.Computability.NearSquareRoot.PhysicalWalshNodeHeader

/-! # Computing a child descriptor with literal arity, batch and axis inputs

One polynomial descriptor command reads its three parameters from the tape.
The input carries the active bit count in unary, bounding the smaller child
bit count that will be used as the exponent in the spectator lengths.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileChild

open IntegerMultiplication Code Staff Strip Carry PhysicalWalsh PhysicalWalshNode

abbrev Params := Tally × Tally × Tally

def params (A W j : ℕ) : Params := (tally A,tally W,tally j)

structure World where
  a : ℕ
  W : ℕ
  axis : Fin (a+1)
  shape : Shape

def descriptor (t : World) := Header.wire (t.a+1) t.shape

def input (t : World) := (params (t.a+1) t.W t.axis.val, descriptor t)

def child (t : World) := descend (t.a+1) t.W t.axis t.shape

def tag (t : World) := (decide (0 < (child t).level), Header.wire (t.a+1) (child t))

def regime : Regime World := ⟨size ∘ input,send ∘ input, Dom.base _⟩

private theorem key : regime.Has input := regime.self

private theorem arity : Realizes regime fun t => t.a+1 := key.ez (Easy.fst.compose Easy.fst)
private theorem batch : Realizes regime World.W := key.ez (Easy.fst.compose (Easy.snd.compose Easy.fst))
private theorem axis : Realizes regime fun t => t.axis.val := key.ez (Easy.fst.compose (Easy.snd.compose Easy.snd))
private theorem wire : regime.Has descriptor := key.ez Easy.snd

private theorem level : Realizes regime fun t => t.shape.level := wire.ez (Easy.fst.compose Easy.fst)
private theorem active : Realizes regime fun t => grow (t.a+1) t.shape.level :=
  wire.ez (Easy.fst.compose (Easy.snd.compose Easy.fst))
private theorem width : Realizes regime fun t => t.shape.w+1 :=
  wire.ez (Easy.fst.compose (Easy.snd.compose Easy.snd))
private theorem prefFigure : Figure regime fun t => t.shape.pref :=
  ⟨_,wire.ez (Easy.snd.compose Easy.fst),fun t => Header.binary_value t.shape.pref⟩
private theorem suffix : Figure regime fun t => t.shape.suff :=
  ⟨_,wire.ez (Easy.snd.compose Easy.snd),fun t => Header.binary_value t.shape.suff⟩

private theorem predLevel : Realizes regime (fun t => t.shape.level-1) := level.minused (Realizes.fix 1)

private theorem childBits : Realizes regime fun t => grow (t.a+1) (t.shape.level-1) := by
  have formula : Figure regime (fun t => grow (t.a+1) (t.shape.level-1)) :=
    (Figure.natural 2).multiplied ((Figure.of_spoken arity).repeated predLevel)
  have d : Dom regime.scale (fun t => size (tally (grow (t.a+1) t.shape.level))) := Regime.Small.extent active
  apply formula.pay (d.mono ?_)
  intro t
  have hA : 1 ≤ t.a+1 := by omega
  have hle := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hA (Nat.sub_le t.shape.level 1))
  simp only [size_tally,tally_length]; unfold grow; omega

theorem childWire : regime.Has (fun t => Header.wire (t.a+1) (child t)) := by
  have group : Figure regime (fun t => groups t.W t.shape) :=
    (Figure.natural 1).maximum (prefFigure.quotients (Figure.of_spoken batch))
  have leftWidth := axis.times childBits
  have rightWidth := ((arity.minused (Realizes.fix 1)).minused axis).times childBits
  have pref := group.multiplied ((Figure.natural 2).repeated leftWidth)
  have suff := ((Figure.natural 2).repeated rightWidth).multiplied suffix
  exact ((Regime.Has.pair predLevel (Regime.Has.pair childBits width))).pair
    ((Header.toBinary pref).pair (Header.toBinary suff))

/-- A single descriptor command works for every template, slot and level. -/
theorem generated : regime.Has tag := by
  have pol : Poly (fun w : Header.Wire => ((!w.1.1.isEmpty),w)) := by
    exact ((Easy.fst.compose Easy.fst).compose (Carry.vacant Unit) |>.compose
      (show Easy (! · : Bool → Bool) from Easy.finite _)).pair Easy.identity |>.poly
  have h := childWire.thenDo pol
  convert h using 1
  funext t

  cases e : (child t).level with
  | zero => simp [tag,Header.wire,e,tally]
  | succ n => simp [tag,Header.wire,e,tally_succ]

end PhysicalWalshCompileChild

end NearSquareRoot
end Computability
end OAI
