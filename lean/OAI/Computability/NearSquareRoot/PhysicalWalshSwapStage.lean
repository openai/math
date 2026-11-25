import OAI.Computability.NearSquareRoot.PhysicalWalshSwapGeometry
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeMachine

/-! # Charging the fixed preprocessing and postprocessing passes of a slot swap -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SlotSwap
open IntegerMultiplication Code Space PhysicalWalsh
open ElementarySchedule (slotWidth)

noncomputable def wideExtra (ρ : ℝ) (A : ℕ) (s : Shape) :=
  ⌈(((count A s+1)*(s.w+1) : ℕ):ℝ) * ((slotWidth A s+1 : ℕ):ℝ)^ρ⌉₊

/-- The setup polynomial is additive. Its degree can increase when a new
descriptor program is linked, without changing the per-record charge. -/
def Stage {I : Type} (ρ : ℝ) (A : ℕ) (s : I → Shape) (q r : I → Tree) := ∃ d : ℕ,
  BoundedTask (fun t => allowance A d (s t) + wideExtra ρ A (s t)) (fun t => allowance A d (s t)) q r

namespace Stage

variable {I : Type} {ρ : ℝ} {A : ℕ} {s : I → Shape} {q r u : I → Tree}

theorem linear {d : ℕ} (h : BoundedTask (fun t => allowance A d (s t)) (fun t => allowance A d (s t)) q r) :
    Stage ρ A s q r := ⟨d,h.mono (fun _ => Nat.le_add_right ..) (fun _ => le_rfl)⟩

theorem thenRun (f : Stage ρ A s q r) (g : Stage ρ A s r u) : Stage ρ A s q u := by
  obtain ⟨d,h⟩ := f
  obtain ⟨e,k⟩ := g
  refine ⟨max d e,(h.compose k).bound 2 1 ?_ ?_⟩ <;> intro i
  all_goals
    have x := allowance_mono (A:=A) (le_max_left d e) (s i)
    have y := allowance_mono (A:=A) (le_max_right d e) (s i)
    omega

/-- Replace the header by the current pass's rulers and restore the compact
header on exit. Copying the compact descriptor takes one scan. The row can
already contain an arbitrary intermediate of the rectangular interchange. -/
theorem supply {H K X Y : Type} [Codec H] [Codec K] [Codec X] [Codec Y]
    {hdr : I → H} {key : I → K} {row : I → X} {out : I → Y}
    (mint : ∃ d, BoundedTask (fun t => allowance A d (s t)) (fun t => allowance A d (s t))
      (send ∘ hdr) (send ∘ key))
    (body : Stage ρ A s (fun t => send (key t,row t)) (send ∘ out)) :
    Stage ρ A s (fun t => send (hdr t,row t)) (fun t => send (hdr t,out t)) := by
  obtain ⟨a,keyRun⟩ := mint
  obtain ⟨b,run⟩ := body
  let V i := allowance A (max a b) (s i)
  let T i := V i + wideExtra ρ A (s i)
  have ha i : allowance A a (s i) ≤ V i := allowance_mono (le_max_left ..) _
  have hb i : allowance A b (s i) ≤ V i := allowance_mono (le_max_right ..) _
  have ks := keyRun.mono ha ha
  have op := run.mono (fun i => Nat.add_le_add_right (hb i) _) hb
  obtain ⟨C,cs⟩ := ks.endpointSize
  obtain ⟨E,es⟩ := op.endpointSize
  have sizes i : size (hdr i) ≤ C*(V i+1) ∧ size (row i) ≤ E*(V i+1) := by
    have d := cs i
    have f := es i
    change max (size (hdr i)) (size (key i)) ≤ _ at d
    change max (size (key i,row i)) (size (out i)) ≤ _ at f
    simp only [size_prod] at f
    omega
  let triple {B : Type} (p : H × B) := (p.1,p)
  have prep := PhysicalWalshGrid.easyWithin V (show Easy (triple (B:=X)) from Easy.fst.pair Easy.identity)
    (fun t => (hdr t,row t)) (C+E+1) (fun i => by
      have h := sizes i; simp only [size_prod,Nat.add_mul,Nat.one_mul]; omega)
  have get : BoundedTask V V (fun i => send (hdr i,row i)) (fun i => send (key i,row i)) := by
    apply (ks.left (send ∘ row)).bound 1 (E+2) <;> intro i
    · simp
    · change V i + size (row i)+1 ≤ _
      have h := sizes i; rw [Nat.add_mul]; omega
  have core : BoundedTask T V (fun i => send (hdr i,row i)) (send ∘ out) := by
    apply (get.compose op).bound 2 1 <;> intro i
    all_goals try dsimp only [T]
    all_goals omega
  have keep := core.right (send ∘ hdr)
  refine ⟨max a b,(prep.compose keep).bound (C+3) (C+2) ?_ ?_⟩ <;> intro i
  all_goals
    have h := sizes i
    have v : V i ≤ T i := Nat.le_add_right ..
    have lim : C*(V i+1) ≤ C*(T i+1) := Nat.mul_le_mul_left C (Nat.succ_le_succ v)
  · change V i+(size (hdr i)+T i)+1 ≤ (C+3)*(T i+1)
    rw [Nat.add_mul]; omega
  · change max (V i) (V i+size (hdr i))+1 ≤ (C+2)*(V i+1)
    rw [Nat.add_mul]; omega

end Stage
end PhysicalWalshNode.SlotSwap

end NearSquareRoot
end Computability
end OAI
