import OAI.Computability.VPVNP.LiveHeaderComplete
import OAI.Computability.VPVNP.LiveGroupModeInput
import OAI.Computability.VPVNP.LiveConfigGatherImage

/-!
# The two ordinary incident cuts of an evaluator tail group

The physical header contains the configuration bits in its left or right
bank. The mode guard and padding guard check the other two fields of exactly
the cut used by the chain contraction. Hence gathering this bank feeds the
same configuration decoder as the semantic boundary, including malformed
word encodings.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.Output

open BurstRAM CutSchedule ChainAssignments LiveEvaluatorEncoding
open LiveHeader LiveHeaderSchedule LiveHeaderDescriptors LiveConfigGather
open scoped Fin.CommRing

variable {w d base M : ℕ} {s : Sizes} {hw : 4 ≤ w} {advice : Bits s.advice}
variable {cuts : AllCuts s.h s.delta} {m : Memory w} {p : UniversalMachine.Program}

private theorem typed_payload {h Δ i c : ℕ} (half : 2^h ≤ i) (hend : i < 2^(h+1))
    (hc : 1+c ≤ Δ) (config : c = fieldWords M*w)
    (layout : LiveEvaluatorTail.Layout p.extra M w Δ) (b : Bits (width (h+1) Δ i))
    (source : Word w) (m : Memory w)
    (image : ∀ j : Fin c, m (source.val+j.val) = PrimedInputRAM.encodeBit w
      ((tailLayout h Δ i c half hend hc b).2.1 j))
    (pad : (tailLayout h Δ i c half hend hc b).2.2 = fun _ => false) :
    let f := tailLayout h Δ i (fieldWords M*w) half hend layout.cutWidth b
    ArrayBitImage m source f.2.1 ∧ f.2.2 = fun _ => false := by
  subst c
  refine ⟨?_, pad⟩
  intro j
  rw [image j]
  cases (tailLayout h Δ i (fieldWords M*w) half hend hc b).2.1 j <;> rfl

private theorem fields_congr {h Δ c : ℕ} (cuts : AllCuts h Δ) {a b : Fin (2^(h+1)+1)}
    (hab : a = b) (ha₁ : 2^h ≤ a.val) (ha₂ : a.val < 2^(h+1))
    (hb₁ : 2^h ≤ b.val) (hb₂ : b.val < 2^(h+1)) (fit : 1+c ≤ Δ) :
    tailLayout h Δ a.val c ha₁ ha₂ fit (cuts a) = tailLayout h Δ b.val c hb₁ hb₂ fit (cuts b) := by
  subst b
  rfl

private theorem interiorCut {g : Fin (2^(s.h+1))}
    (output : Output s base d hw advice cuts g .tail m)
    (layout : LiveEvaluatorTail.Layout p.extra M w s.delta) (init : Code p.extra M)
    (config : s.config = fieldWords M*w) (tag : physicalTag cuts g = some .tail)
    (side : Side) (pad : Fields.ValidPadding s cuts g .tail side)
    (source : Word w) (addr : source.val = configBase s base side)
    (j : Fin (2^s.h-1)) (cut : incidentCut side g = laterCut j)
    (x : Fin (2^s.h+1)) (time : x.val = j.val+1) :
    ∃ b : Fin (fieldWords M*w) → Bool, ArrayBitImage m source b ∧
      LiveEvaluatorTail.boundary layout init (liveCutEquiv s.h s.delta cuts).2 x =
        (format layout.symbolWidth layout.stateWidth).decode b := by
  have hj := j.isLt
  have half : 2^s.h < (incidentCut side g).val := by rw [cut]; change 2^s.h < 2^s.h+(j.val+1); omega
  have hend : (incidentCut side g).val < 2^(s.h+1) := by rw [cut]; change 2^s.h+(j.val+1) < _; rw [pow_succ]; omega
  have fit : 1+s.config ≤ s.delta := config ▸ layout.cutWidth
  have hΔ : 0 < s.delta := by omega
  let k := incidentCut side g
  have hmode : evalCutMode cuts k := by
    obtain ⟨hm, _⟩ := (physicalTag_tail hΔ cuts g).mp tag
    cases side <;> first | exact hm.1 | exact hm.2
  have hsite : 0 < width (s.h+1) s.delta k.val := by
    rw [width_tail s.h s.delta k.val half.le hend]
    exact hΔ
  let zero : Fin (width (s.h+1) s.delta k.val) := ⟨0,hsite⟩
  have hbit : cuts k zero = true := by
    have h := hmode (by have := Nat.two_pow_pos s.h; omega) hend
    simpa only [distributedBit, dite_eq_left hsite] using h
  have hfieldmode := (Physical.tail_mode half.le hend layout.cutWidth (cuts k) zero rfl).trans hbit
  obtain ⟨before, _, img⟩ := output.fieldImage
  have image (i : Fin s.config) : m (source.val+i.val) = PrimedInputRAM.encodeBit w
      ((tailLayout s.h s.delta k.val s.config half.le hend fit (cuts k)).2.1 i) := by
    rw [addr]
    exact img.tail_config (by decide) side fit half hend i
  have hpad := (Fields.validPadding_tail_iff (tag := .tail) (by decide) side fit half hend).mp pad
  obtain ⟨him, hp⟩ := typed_payload half.le hend fit config layout (cuts k) source m image hpad
  change k = laterCut j at cut
  let f := tailLayout s.h s.delta (laterCut j).val (fieldWords M*w) (by change _ ≤ 2^s.h+(j.val+1); omega)
    (by change 2^s.h+(j.val+1) < _; rw [pow_succ]; omega) layout.cutWidth (cuts (laterCut j))
  have he : tailLayout s.h s.delta k.val (fieldWords M*w) half.le hend layout.cutWidth (cuts k) = f :=
    fields_congr cuts cut half.le hend _ _ layout.cutWidth
  have hp' : f.2.2 = fun _ => false := he ▸ hp
  have hm' : f.1 = true := he ▸ hfieldmode
  refine ⟨f.2.1, he ▸ him, ?_⟩
  have hx : x.val ≠ 0 := by omega
  have hT : x.val ≠ 2^s.h := by omega
  rw [LiveEvaluatorTail.boundary, dite_eq_right hx, dite_eq_right hT]
  have hidx : (⟨x.val-1, by omega⟩ : Fin (2^s.h-1)) = j := Fin.ext (by change x.val-1 = j.val; omega)
  rw [hidx]
  change (if f.1 = true ∧ f.2.2 = fun _ => false then _ else _) = _
  rw [ite_eq_left ⟨hm', hp'⟩]
  rfl

variable {i : Fin (2^s.h)}

/-- Incoming configuration after the first evaluator group. The midpoint
itself supplies the explicitly initialized input. -/
theorem tail_incoming {src : Word w}
    (output : Output s base d hw advice cuts (halves s.h (.inr i)) .tail m)
    (layout : LiveEvaluatorTail.Layout p.extra M w s.delta) (init : Code p.extra M)
    (config : s.config = fieldWords M*w)
    (tag : physicalTag cuts (halves s.h (.inr i)) = some .tail)
    (pad : Fields.ValidPadding s cuts (halves s.h (.inr i)) .tail .left)
    (addr : src.val = configBase s base .left) (nonfirst : 0 < i.val) :
    ∃ b : Fin (fieldWords M*w) → Bool, ArrayBitImage m src b ∧
      LiveEvaluatorTail.boundary layout init (liveCutEquiv s.h s.delta cuts).2 i.castSucc =
        (format layout.symbolWidth layout.stateWidth).decode b := by
  let j : Fin (2^s.h-1) := ⟨i.val-1, by have := i.isLt; omega⟩
  apply interiorCut output layout init config tag .left pad src addr j
  · apply Fin.ext
    change 2^s.h+i.val = 2^s.h+(j.val+1)
    dsimp only [j]
    omega
  · change i.val = (i.val-1)+1
    omega

/-- Outgoing configuration before the last evaluator group. The terminal
endpoint uses the explicitly prepared accepting sentinel. -/
theorem tail_outgoing {src : Word w}
    (output : Output s base d hw advice cuts (halves s.h (.inr i)) .tail m)
    (layout : LiveEvaluatorTail.Layout p.extra M w s.delta) (init : Code p.extra M)
    (config : s.config = fieldWords M*w)
    (tag : physicalTag cuts (halves s.h (.inr i)) = some .tail)
    (pad : Fields.ValidPadding s cuts (halves s.h (.inr i)) .tail .right)
    (addr : src.val = configBase s base .right) (nonlast : i.val+1 < 2^s.h) :
    ∃ b : Fin (fieldWords M*w) → Bool, ArrayBitImage m src b ∧
      LiveEvaluatorTail.boundary layout init (liveCutEquiv s.h s.delta cuts).2 i.succ =
        (format layout.symbolWidth layout.stateWidth).decode b := by
  let j : Fin (2^s.h-1) := ⟨i.val, by omega⟩
  apply interiorCut output layout init config tag .right pad src addr j
  · apply Fin.ext
    change 2^s.h+i.val+1 = 2^s.h+(j.val+1)
    dsimp only [j]
    omega
  · rfl

end LiveHeaderProgram.Output

end VPVNP
end Computability
end OAI
