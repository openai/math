import OAI.Computability.NearSquareRoot.PhysicalWalshNodeIO
import OAI.Computability.NearSquareRoot.PhysicalWalshContext
import OAI.Computability.NearSquareRoot.PhysicalWalshFrameScan

/-! # Entering and leaving the recursive Walsh template's bank layout

The input descriptor generates both the lane-cut rulers and the arithmetic
header. The descriptor stays available while a plan acts on the ordered
bank, and is returned with the merged output on exit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication Code PhysicalWalsh PhysicalWalshContext Space

variable {I : Type} {a W : ℕ}

/-- Splitting and merging are charged to the parent's physical record volume. -/
theorem nodeVolume_le (A d : ℕ) (s : Shape) : nodeVolume A s ≤ allowance A d s :=
  (Nat.mul_le_mul_left (count A s+1) (show s.w+1 ≤ grow A s.level+s.w+1 by omega)).trans
    (Nat.le_add_right ..)

private theorem addition_le (A d : ℕ) (s : Shape) : count A s+s.w+1 ≤ allowance A d s := by
  apply le_trans _ (nodeVolume_le A d s)
  dsimp only [nodeVolume]
  nlinarith

/-- Generate both live layout headers from the compact input wire, with one
polynomial degree for all nonterminal shapes. -/
private theorem header_tasks (a W : ℕ) : ∃ d : ℕ, ∀ (I : Type) (s : I → Shape),
    (∀ i, 0 < (s i).level) →
    let V := allowance (a+1) d ∘ s
    let wire := Header.wire (a+1) ∘ s
    BoundedTask V V (send ∘ wire) (send ∘ Header.cuts (a+1) W ∘ s) ∧
    BoundedTask V V (send ∘ wire) (send ∘ PhysicalWalshGrid.header (coords a W) Shape.w ∘ s) := by
  obtain ⟨e,C,hc⟩ := Header.cuts_bounded (a+1) W
  obtain ⟨f,D,hg⟩ := Header.grid_bounded W a
  let d := max e f
  refine ⟨d,fun I s positive => ?_⟩
  intro V wire
  have power (t : Shape) (k : ℕ) (h : k ≤ d) :
      (Header.scale (a+1) t+1)^k ≤ allowance (a+1) d t :=
    (Nat.pow_le_pow_right (by omega) h).trans (Nat.le_add_left ..)
  have cut_bound (i : I) : C*(Header.scale (a+1) (s i)+1)^e + (count (a+1) (s i)+1) + 1 ≤
      (C+2)*(V i+1) := by
    have ha := Nat.mul_le_mul_left C (power (s i) e (le_max_left ..))
    have hb := addition_le (a+1) d (s i)
    change C*_ ≤ C*V i at ha
    change _ ≤ V i at hb
    rw [Nat.add_mul,Nat.mul_add C]; omega
  have grid_bound (i : I) : D*(Header.scale (a+1) (s i)+1)^f + (count (a+1) (s i)+(s i).w+1) + 1 ≤
      (D+2)*(V i+1) := by
    have ha := Nat.mul_le_mul_left D (power (s i) f (le_max_right ..))
    have hb := addition_le (a+1) d (s i)
    change D*_ ≤ D*V i at ha
    change _ ≤ V i at hb
    rw [Nat.add_mul,Nat.mul_add D]; omega
  exact ⟨(hc.on s).bound (C+2) (C+2) cut_bound cut_bound,
    (hg.on fun i => ⟨s i,positive i⟩).bound (D+2) (D+2) grid_bound grid_bound⟩

/-- All nonterminal inputs use one degree and one fixed prepare/restore
program per input family. The split and merge preserve every record, including
spectator positions that share the same active address. -/
theorem nodeFrames (a W : ℕ) (hW : 0 < W) : ∃ d : ℕ, ∀ (I : Type) (s : I → Shape),
    (∀ i, 0 < (s i).level) → (∀ i, W^(s i).level ∣ (s i).pref) →
    let V := allowance (a+1) d ∘ s
    let layout := routeLayout (coords a W) Shape.w (Header.wire (a+1))
    (∀ x : (i : I) → Data (s i), BoundedTask V V (fun i => buffer (a+1) (s i) (x i))
      (fun i => send (packet layout (s i) (lane (a+1) W (s i) (x i))))) ∧
    (∀ y : (i : I) → Fin W → Data (s i), BoundedTask V V (fun i => send (packet layout (s i) (y i)))
      (fun i => buffer (a+1) (s i) (unlane (a+1) hW (s i) (y i)))) := by
  obtain ⟨d,hd⟩ := header_tasks a W
  refine ⟨d,fun I s positive divides => ?_⟩
  intro V layout
  obtain ⟨cut,grid⟩ := hd I s positive
  have hle (i : I) : nodeVolume (a+1) (s i) ≤ V i := nodeVolume_le (a+1) d (s i)
  constructor
  · intro x
    have split := (nodeSplit (a := a) s positive divides x).mono hle hle
    exact framePrepare _ _ _ _ _ cut grid split
  · intro y
    have merge := (nodeMerge (a := a) s positive divides hW y).mono hle hle
    exact frameRestore _ _ _ _ _ cut grid merge

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
