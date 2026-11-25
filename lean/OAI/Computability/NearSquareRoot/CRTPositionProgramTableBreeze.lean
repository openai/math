import OAI.Computability.NearSquareRoot.CRTPositionProgramTableRun

/-! # Position permutation in a general header regime and arbitrary record width -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Adic IntegerMultiplication.Loom Reflections

theorem tableWidth_dom {X : Type} {r : Regime X} {k : X → ℕ} {p : (x : X) → Equiv.Perm (Fin (k x))}
    (h : r.Has (fun x => table (p x))) : Dom r.scale k := by
  apply (Regime.Small.extent h).mono
  intro x
  change k x ≤ size (table (p x))
  have eq : (table (p x)).length = k x := List.length_ofFn
  exact eq.ge.trans (duration (table (p x))).le

/-- All payload widths are legal. The fixed per-record polynomial overhead
is charged to the regime's scale, and the image table is read from its header. -/
theorem tableScheduleBreeze {ρ : ℝ} (hρ : 1/2 < ρ) {X : Type} {r : Regime X}
    (k w : X → ℕ) (p : (x : X) → Equiv.Perm (Fin (k x)))
    (tableTold : r.Has (fun x => table (p x))) (hk : Dom r.scale k)
    {U : X → Type} (u : (x : X) → Series (U x)) (hu : ∀ x, (u x).count ≤ w x)
    (f : (x : X) → Block 2 (k x) → U x → Bead) :
    Breeze (fun x => positionRate ρ (k x)) r (fun x => (line 2 (k x)).count) w
      (together r.header (cloth (fun x => line 2 (k x)) u f))
      (cloth (fun x => line 2 (k x)) u (fun x a => f x ((permuteNative (p x)).symm a))) := by
  let n (x : X) := (line 2 (k x)).count
  let rate (x : X) := positionRate ρ (k x)
  have hn (x : X) : 1 ≤ n x := by simp only [n,lineSize]; exact Nat.one_le_pow _ _ (by decide)
  have hr (x : X) : 1 ≤ rate x := one_le_positionRate (by linarith) _
  obtain ⟨D,hD⟩ := tableScheduleWithSlack hρ
  obtain ⟨A,C,hC⟩ := (hk.add (Dom.const r.scale 1)).pow D
  have scale (x : X) : tableRate ρ (k x) ((u x).count+(k x+1)^D) ≤ (C+1 : ℕ)*runrate rate r n w A x := by
    rw [tableRate_eq]
    have h : (u x).count+(k x+1)^D ≤ (C+1)*(w x + (r.scale x+1)^A) := by
      have e := hC x
      dsimp only at e
      have size := hu x
      rw [Nat.succ_mul,Nat.mul_add]
      omega
    have realH : (((u x).count+(k x+1)^D : ℕ):ℝ) ≤ ((C+1:ℕ):ℝ)*((w x:ℝ)+(r.scale x+1:ℝ)^A) := by
      exact_mod_cast h
    calc
      _ ≤ ((2^k x : ℕ):ℝ) * (((C+1:ℕ):ℝ)*((w x:ℝ)+(r.scale x+1:ℝ)^A)) * rate x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left realH (by positivity)) (zero_le_one.trans (hr x))
      _ = _ := by simp only [runrate,mass,n,lineSize]; ring
  have last := (hD k p u f).times (fun x => one_le_mul_of_one_le_of_one_le (unit_mass hn A x) (hr x)) (C+1) scale
  have body : Breeze rate r n w
      (together (fun x => send (table (p x))) (cloth (fun x => line 2 (k x)) u f)) _ := ⟨hr,A,last⟩
  have alive : Alive r n w (cloth (fun x => line 2 (k x)) u f) := by
    refine ⟨0,Carries.idles (unit_mass hn 0) ⟨3,?_⟩⟩
    intro x
    have e := (position_row_count (k x) (u x) (f x)).trans
      (Nat.mul_le_mul_left (3*2^(k x)) (Nat.add_le_add_right (hu x) 1))
    simp only [mass,n,lineSize,pow_zero]
    push_cast
    have h : (cloth (fun x => line 2 (k x)) u f x).count ≤ 3*(2^(k x)*(w x+1)) := by
      rw [← Nat.mul_assoc]
      exact e
    exact_mod_cast h
  have head : Rip r n w r.header (fun x => send (table (p x))) := Rip.header hn tableTold
  exact ((Breeze.launch head hr).prepend _ alive).next body

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
