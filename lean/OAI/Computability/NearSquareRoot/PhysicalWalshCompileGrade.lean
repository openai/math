import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSwapLiteral
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileElementaryAgenda

/-! # Computing a Walsh reserve degree from the runtime descriptor

A logarithmic degree gives a squared-logarithm reserve. Its value can be
supplied to the same universal header code as any literal degree, while the
physical caller retains one program for all shapes of its kernel template.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileGrade
open IntegerMultiplication Code Strip Staff Carry PhysicalWalsh PhysicalWalshNode
open PhysicalWalshCompileSwapRulers CommonRegisters GeneratorSyntax

def live (u : World) := Nat.clog 2 (Header.scale (u.a+1) u.shape + 1)

def regrade (u : World) : World := {u with depth := live u}

theorem live_realizes : Realizes regime live := (Figure.of_spoken (scale.plus (Realizes.fix 1))).short_log

theorem regrade_input : regime.Has (input ∘ regrade) :=
  (arity.pair (batch.pair (src.pair (dst.pair live_realizes)))).pair wire

/-- Regenerating the compact configuration, including its unary log, is a
polynomial-size transformation even with all four geometric literals varied. -/
theorem has {Z : Type} [Codec Z] {f : World → Z} (h : regime.Has f) : regime.Has (f ∘ regrade) :=
  regrade_input.chain ((Task.BT.map h regrade).mono regrade_input.extent)

theorem mint {Z : Type} [Codec Z] {f : World → Z} (h : Mint regime f) : Mint regime (f ∘ regrade) := by
  obtain ⟨t,dt,p⟩ := h
  obtain ⟨b,db,gate⟩ := regrade_input
  have scale : Dom regime.scale (regime.scale ∘ regrade) := regrade_input.extent
  refine ⟨fun u => b u+t (regrade u),db.add ((dt.map regrade).sub scale),?_⟩
  convert gate.compose (p.on regrade) using 1
  funext u;change b u+t (regrade u) + size (f (regrade u)) = b u+(t (regrade u)+size (f (regrade u)));omega
  rfl

/-- One physical emitter for the low elementary tickets, including the
cutoff computed from the current record descriptor. -/
theorem compiledAgenda (trim : Bool) :
    let f := PhysicalWalshCompileElementaryAgenda.agenda (PhysicalWalshCompileElementaryAgenda.steps trim) ∘ regrade
    ∃ (R d e : ℕ) (c : Control → Cmd), 1 ≤ d ∧ Effective ltr c ∧ (∀ k,Within R (c k)) ∧
      Configured f (fun _ => 0) d c ∧ ∀ (a W : ℕ) (i j : Fin (a+1)) (D : ℕ), ∃ C : ℕ, ∀ s : Shape,
        size (f ⟨a,W,i,j,D,s⟩) ≤ C*(Header.scale (a+1) s+1)^e := by
  intro f
  have h := has (PhysicalWalshCompileElementaryAgenda.generated _ (PhysicalWalshCompileElementaryAgenda.steps_realizes trim))
  obtain ⟨R,d,c,p,eff,reg,run⟩ := configured h
  obtain ⟨e,sz⟩ := compact_size h
  exact ⟨R,d,e,c,p,eff,reg,run,sz⟩

end PhysicalWalshCompileGrade

end NearSquareRoot
end Computability
end OAI
