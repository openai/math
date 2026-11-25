import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorHeader
import OAI.Computability.NearSquareRoot.KernelComputableTemplateSearch
import OAI.Computability.NearSquareRoot.KernelPassComputablePacked
import OAI.Computability.IntegerMultiplication.Interface

/-! # Emit the interior gate's header while its record stream is parked -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileInteriorHeader

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode
open PhysicalWalshCompileSwapRulers CommonRegisters GeneratorSyntax PhysicalWalshCompile
open KernelPass.ComputableSyntax

/-- Width is taken from precisely the raw plan consumed by the recursive compiler. -/
def rawKey (e : ℕ × Raw) : Control :=
  (e.2.1, ((KernelPass.ComputableSyntax.Shape.algebra e.2.1).parse e.2.2).1.1,0,0,e.1)

theorem primrec_rawKey : Primrec rawKey := by
  have arity : Primrec (fun e : ℕ × Raw => e.2.1) := Primrec.fst.comp Primrec.snd
  have ops : Primrec (fun e : ℕ × Raw => e.2.2) := Primrec.snd.comp Primrec.snd
  have shape := KernelPass.ComputableSyntax.Shape.primrec_algebra.comp arity ops
  exact arity.pair (((Primrec.fst.comp Primrec.fst).comp shape).pair
    ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.fst)))

theorem key_width (a W D : ℕ) (ops : List Op) (hi : (Packed.decode (a+1) ops).i = W) :
    rawKey (D,(a+1,ops)) = (a+1,W,0,0,D) := by
  unfold rawKey
  rw [← Packed.decode_shape, show (Packed.decode (a+1) ops).shape.1.1 = W from hi]

/-- Build and install the key on the real, arbitrary padded row, preserving
every record and charging the live row to the volume of the node. -/
theorem compiledRaw : ∃ (R d : ℕ) (c : ℕ × Raw → Cmd), Effective ltr c ∧ 1 ≤ d ∧
    (∀ e, Within R (c e)) ∧
    ∀ (a W : ℕ) (ops : List Op), (Packed.decode (a+1) ops).i = W →
    ∀ (D : ℕ), 4 ≤ a → ∀ (I : Type) (s : I → PhysicalWalshNode.Shape), (∀ i, 0 < (s i).level) →
    ∀ row : I → Tree, Small (allowance (a+1) d ∘ s) row →
    let V := allowance (a+1) d ∘ s
    ClosedRuns (c (D,(a+1,ops))) V V
      (fun i => .fork (send (Header.wire (a+1) (s i))) (row i))
      (fun i => .fork (XorWindow.duskHeader
        (send (tally (Interior.P (a+1) W (s i)),tally (Interior.L (a+1) (s i))))
        (Interior.rows a W (s i)) (Interior.S a (s i)) (s i).w) (row i)) := by
  obtain ⟨R,d,emit,hd,eff,withinC,run⟩ := compiled
  refine ⟨R+1,d,fun e => left (emit (rawKey e)),
    KernelEffectiveFamily.effective_left (eff.comp primrec_rawKey.to_comp),hd,fun e =>
      KernelEffectiveFamily.within_left (Nat.succ_pos _) (RegisterSelect.within_mono (Nat.le_succ R) _ (withinC _)),?_⟩
  intro a W ops hi D ha I s hl row hrow V
  let t (i : I) : World := ⟨a,W,0,0,D,s i⟩
  have key : rawKey (D,(a+1,ops)) = (a+1,W,0,0,D) := key_width _ _ _ ops hi
  obtain ⟨C,prog⟩ := run a W 0 0 D ha
  have h : Scan (emit (a+1,W,0,0,D)) V (fun i => send (descriptor (t i)))
      (fun i => send (keys (t i))) := by
    refine ⟨⟨1,fun i => ?_⟩,⟨C,fun i env park => (prog (s i) (hl i)).1 env park⟩⟩
    change Header.scale (a+1) (s i) ≤ 1*(allowance (a+1) d (s i)+1)
    have q : Header.scale (a+1) (s i)+1 ≤ (Header.scale (a+1) (s i)+1)^d := by
      simpa only [pow_one] using Nat.pow_le_pow_right (n:=Header.scale (a+1) (s i)+1) (by omega) hd
    unfold allowance; omega
  change ClosedRuns (left (emit (rawKey (D,(a+1,ops))))) V V _ _
  rw [key]
  exact (h.park row hrow).closed

end PhysicalWalshCompileInteriorHeader

end NearSquareRoot
end Computability
end OAI
