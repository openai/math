import OAI.Computability.NearSquareRoot.PhysicalWalshSwapRulers

/-! # One Walsh ruler generator over explicit routing parameters

Arity, batch width, both slot ordinals and reserve degree arrive on the tape
beside the node descriptor. Binary magnitudes use short words. Tally expansion
is charged separately at the size of its output.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileSwapRulers

open IntegerMultiplication Code Strip Staff Carry PhysicalWalsh PhysicalWalshNode Space

abbrev Control := ℕ × ℕ × ℕ × ℕ × ℕ
abbrev Params := Tally × Tally × Tally × Tally × Tally

def params (A W i j D : ℕ) : Params := (tally A,tally W,tally i,tally j,tally D)

structure World where
  a : ℕ
  W : ℕ
  src : Fin (a+1)
  dst : Fin (a+1)
  depth : ℕ
  shape : Shape

def control (t : World) : Control := (t.a+1,t.W,t.src.val,t.dst.val,t.depth)
def descriptor (t : World) := Header.wire (t.a+1) t.shape
def input (t : World) := (params (t.a+1) t.W t.src.val t.dst.val t.depth,descriptor t)
def regime : Regime World := ⟨size ∘ input,send ∘ input, Dom.base _⟩

private theorem key : regime.Has input := regime.self
private theorem literals : regime.Has (fun t => (input t).1) := key.ez Easy.fst

theorem wire : regime.Has descriptor := key.ez Easy.snd
theorem arity : Realizes regime (fun t => t.a+1) := literals.ez Easy.fst
theorem batch : Realizes regime World.W := literals.ez (Easy.snd.compose Easy.fst)
theorem src : Realizes regime (fun t => t.src.val) := literals.ez ((Easy.snd.compose Easy.snd).compose Easy.fst)
theorem dst : Realizes regime (fun t => t.dst.val) :=
  literals.ez (((Easy.snd.compose Easy.snd).compose Easy.snd).compose Easy.fst)
theorem depth : Realizes regime World.depth :=
  literals.ez (((Easy.snd.compose Easy.snd).compose Easy.snd).compose Easy.snd)
theorem level : Realizes regime (fun t => t.shape.level) := wire.ez (Easy.fst.compose Easy.fst)
theorem active : Realizes regime (fun t => grow (t.a+1) t.shape.level) :=
  wire.ez (Easy.fst.compose (Easy.snd.compose Easy.fst))
theorem width : Realizes regime (fun t => t.shape.w+1) :=
  wire.ez (Easy.fst.compose (Easy.snd.compose Easy.snd))
theorem pref : Figure regime (fun t => t.shape.pref) :=
  ⟨_,wire.ez (Easy.snd.compose Easy.fst),fun t => Header.binary_value t.shape.pref⟩
theorem suff : Figure regime (fun t => t.shape.suff) :=
  ⟨_,wire.ez (Easy.snd.compose Easy.snd),fun t => Header.binary_value t.shape.suff⟩
theorem group : Figure regime (fun t => groups t.W t.shape) :=
  (Figure.natural 1).maximum (pref.quotients (Figure.of_spoken batch))

theorem slot : Realizes regime (fun t => ElementarySchedule.slotWidth (t.a+1) t.shape) := by
  have formula := (Figure.natural 2).multiplied ((Figure.of_spoken arity).repeated (level.minused (Realizes.fix 1)))
  have d : Dom regime.scale (fun t => size (tally (grow (t.a+1) t.shape.level))) := Regime.Small.extent active
  apply formula.pay (d.mono ?_)
  intro t
  have hb := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (n := t.a+1) (by omega) (Nat.sub_le t.shape.level 1))
  simp only [size_tally,tally_length, grow]; omega

theorem scale : Realizes regime (fun t => Header.scale (t.a+1) t.shape) := by
  have p := (pref.added (Figure.natural 1)).short_log
  have b := (suff.added (Figure.natural 1)).short_log
  convert ((Realizes.fix 2).times ((((level.plus active).plus width).plus p).plus b)).plus (.fix 9) using 1
  funext t; exact Header.scale_exact _ _

theorem reserve : Realizes regime (fun t => SlotSwap.reserve t.depth (t.a+1) t.shape) := by
  have wanted := depth.times (Figure.of_spoken (scale.plus (Realizes.fix 1))).short_log
  convert slot.minused (slot.minused wanted) using 1
  funext t; dsimp only [SlotSwap.reserve,Controlled.payloadBits]; omega

theorem minRealizes {u v : World → ℕ} (hu : Realizes regime u) (hv : Realizes regime v) :
    Realizes regime (fun t => min (u t) (v t)) := by
  convert hu.minused (hu.minused hv) using 1
  funext t; omega

theorem maxRealizes {u v : World → ℕ} (hu : Realizes regime u) (hv : Realizes regime v) :
    Realizes regime (fun t => max (u t) (v t)) := by
  convert (hu.minused hv).plus hv using 1
  funext t; omega

def geometry (t : World) := SlotSwap.geometry t.W t.src t.dst t.shape (SlotSwap.reserve t.depth (t.a+1) t.shape)

theorem geometry_has : regime.Has (fun t => (geometry t).header) := by
  have lo := minRealizes src dst
  have hi := maxRealizes src dst
  have p := group.short_log.plus (lo.times slot)
  have g := (((hi.minused lo).minused (Realizes.fix 1)).times slot).plus reserve
  exact p.pair (g.pair (slot.minused reserve))

theorem countFigure : Figure regime (fun t => (geometry t).grid.count) := by
  have p : Realizes regime (fun t => (geometry t).pre) := geometry_has.ez Easy.fst
  have g : Realizes regime (fun t => (geometry t).gap) := geometry_has.ez (Easy.snd.compose Easy.fst)
  have w : Realizes regime (fun t => (geometry t).wing) := geometry_has.ez (Easy.snd.compose Easy.snd)
  simp_rw [SlotSwap.geometry_count]
  exact (Figure.natural 2).repeated (((p.plus w).plus g).plus w)

theorem strideFigure : Figure regime (fun t =>
    SlotSwap.stride t.src t.dst t.shape (SlotSwap.reserve t.depth (t.a+1) t.shape)) := by
  have n := (((arity.minused (Realizes.fix 1)).minused (maxRealizes src dst)).times slot).plus reserve
  exact ((Figure.natural 2).repeated n).multiplied suff

theorem recordFigure : Figure regime (fun t => 2*(t.shape.w+1)) :=
  (Figure.natural 2).multiplied (Figure.of_spoken width)

def packHeader (t : World) := SlotSwap.Rulers.packHeader t.depth t.W t.src t.dst t.shape
def rectHeader (t : World) := (geometry t).header
def unpackHeader (t : World) := SlotSwap.Rulers.unpackHeader t.depth t.W t.src t.dst t.shape

theorem packMint : Mint regime packHeader :=
  (Mint.tally countFigure).pair (Mint.tally (strideFigure.multiplied recordFigure))
theorem rectMint : Mint regime rectHeader := Mint.of_has geometry_has
theorem unpackMint : Mint regime unpackHeader :=
  (Mint.tally (countFigure.multiplied strideFigure)).pair (Mint.tally recordFigure)

end PhysicalWalshCompileSwapRulers

end NearSquareRoot
end Computability
end OAI
