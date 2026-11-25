import OAI.Computability.NearSquareRoot.PhysicalWalshCompileTie
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease

/-! # A physical two-way choice with separate time and space bounds -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code Space PhysicalWalsh GeneratorSyntax CommonRegisters

/-- Run the command selected by the bit at the head of the packet. Each
command needs to handle only the requests which take its branch. -/
theorem chooseNamed {X : Type} (P : X → Prop) [DecidablePred P] {T S : X → ℕ} {q r : X → Tree}
    {c d : Cmd} (small : ClosedRuns c (T ∘ Subtype.val) (S ∘ Subtype.val)
      (fun x : {x // ¬ P x} => q x.val) (r ∘ Subtype.val))
    (large : ClosedRuns d (T ∘ Subtype.val) (S ∘ Subtype.val)
      (fun x : {x // P x} => q x.val) (r ∘ Subtype.val)) :
    ClosedRuns (decodeBit c d) T S (fun x => .fork (.atom (decide (P x))) (q x)) r := by
  obtain ⟨E,es⟩ := (show BoundedTask _ _ _ _ from ⟨c,small⟩).endpointSize
  obtain ⟨F,ef⟩ := (show BoundedTask _ _ _ _ from ⟨d,large⟩).endpointSize
  obtain ⟨C,hc⟩ := small
  obtain ⟨D,hd⟩ := large
  let K := C+D+E+F+8
  refine ⟨K,fun x env parked base hpark => ?_⟩
  have bound : (q x).count ≤ (E+F)*(S x+1) := by
    rw [Nat.add_mul]
    by_cases h : P x
    · have v := (Nat.le_max_left ..).trans (ef ⟨x,h⟩)
      change (q x).count ≤ F*(S x+1) at v
      omega
    · have v := (Nat.le_max_left ..).trans (es ⟨x,h⟩)
      change (q x).count ≤ E*(S x+1) at v
      omega
  have tagged : DeckCap (base+K*(S x+1)) (pile 0 (.fork (.atom (decide (P x))) (q x)) parked) := by
    apply (hpark.pile 0 _).mono
    change base+(1+(q x).count+1) ≤ _
    dsimp only [K]; rw [Nat.add_mul] at bound
    simp only [Nat.add_mul]; omega
  have hdepth : 1 ≤ K*(S x+1) := Nat.mul_pos (by dsimp only [K];omega) (by omega)
  have run : BoundedFits env (bif decide (P x) then d else c) (pile 0 (q x) parked) (pile 0 (r x) parked)
      ((C+D)*(T x+1)) (base+K*(S x+1)) (K*(S x+1)) := by
    by_cases h : P x
    · simp only [h,decide_true,Bool.cond_true]
      apply (hd ⟨x,h⟩ env parked base hpark).mono <;>
        dsimp only [Function.comp_apply,K] <;> simp only [Nat.add_mul] <;> omega
    · simp only [h,decide_false,Bool.cond_false]
      apply (hc ⟨x,h⟩ env parked base hpark).mono <;>
        dsimp only [Function.comp_apply,K] <;> simp only [Nat.add_mul] <;> omega
  apply (BoundedFits.decodeBit run tagged hdepth).mono _ le_rfl le_rfl
  dsimp only [K]; simp only [Nat.add_mul]; omega

open private effective_splitRoot from OAI.Computability.NearSquareRoot.PhysicalWalshCompileTie

/-- Code generation inserts two fixed bit-inspection instructions. -/
theorem choose_effective {Z : Type} [Primcodable Z] {a b : Z → Cmd} (ea : Effective ltr a)
    (eb : Effective ltr b) : Effective ltr (fun z => decodeBit (a z) (b z)) := by
  apply effective_splitRoot 0 (fun _ _ => .pass) _ (fun _ => effective_const _ _)
  apply effective_splitRoot 0 (fun z t => bif t then b z else a z) (fun _ => .pass)
  · intro t; cases t <;> assumption
  · exact effective_const _ _

theorem choose_within {N : ℕ} (hn : 0<N) {a b : Cmd} (ha : Within N a) (hb : Within N b) :
    Within N (decodeBit a b) := PhysicalWalshCompile.tied_within hn ha hb

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
