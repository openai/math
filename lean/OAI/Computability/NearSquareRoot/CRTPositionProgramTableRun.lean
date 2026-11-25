import OAI.Computability.NearSquareRoot.CRTPositionProgramTableRawRate
import OAI.Computability.NearSquareRoot.CRTPositionProgramRowTransport

/-! # Time for a flat permutation of word positions from its image table -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Adic IntegerMultiplication.Loom Reflections

/-- Select the degree of the compiled physical program before the row family
or its payload widths. The sole input header is the unary image table. -/
theorem tableScheduleWithSlack {ρ : ℝ} (hρ : 1/2 < ρ) :
    ∃ D : ℕ, ∀ {X : Type} (k : X → ℕ) (p : (x : X) → Equiv.Perm (Fin (k x)))
      {U : X → Type} (u : (x : X) → Series (U x)) (f : (x : X) → Block 2 (k x) → U x → Bead),
      Carries (fun x => tableRate ρ (k x) ((u x).count+(k x+1)^D))
        (together (fun x => send (table (p x))) (cloth (fun x => line 2 (k x)) u f))
        (cloth (fun x => line 2 (k x)) u (fun x a => f x ((permuteNative (p x)).symm a))) := by
  obtain ⟨d,C,sweep⟩ := table_sweep (tableDispatcher hρ)
  obtain ⟨b,⟨a,B,hb⟩,setup⟩ := tableHeader_setup TableShape.k TableShape.p
  let D := max 2 (max a d)
  refine ⟨D,?_⟩
  intro X k p U u f
  let s (x : X) : TableShape := ⟨k x,p x,(u x).count⟩
  let w (x : X) : (s x).Data := fun v j => f x v ((u x).follow j)
  have ha : a ≤ D := le_trans (le_max_left ..) (le_max_right 2 (max a d))
  have hs : d ≤ D := le_trans (le_max_right ..) (le_max_right 2 (max a d))
  have h₂ (x : X) : (k x+1)^2 ≤ (k x+1)^D := Nat.pow_le_pow_right (by omega) (le_max_left ..)
  have hl (x : X) : 1 ≤ (k x+1)^D := Nat.one_le_pow _ _ (by omega)
  have rate (x : X) : 1 ≤ tableRate ρ (k x) ((u x).count + (k x+1)^D) :=
    one_le_tableRate (by linarith) _ ((hl x).trans (Nat.le_add_left ..))
  let forward (x : X) (v : Block 2 (k x) → U x → Bead) : (s x).Data :=
    fun a j => v a ((u x).follow j)
  have packed (x : X) (v : Block 2 (k x) → U x → Bead) :
      (s x).packet (forward x v) = stripe (line 2 (k x)) (fun a => stripe (u x) (fun j => send (v a j))) := by
    unfold TableShape.packet
    apply congrArg (stripe _)
    funext t
    exact stripe_natural_follow (u x) (fun i => send (v t i))
  let box (x : X) := (s x).packet (w x)
  have run := ((setup.on s).left box).compose (sweep.on (fun x : X => ⟨s x,w x⟩))
  have run' := run.conform (fun _ => rfl)
    (show ∀ x : X, _ = together (fun x => send (table (p x))) (cloth (fun x => line 2 (k x)) u f) x from
      fun x => congrArg (Tree.fork (send (table (p x)))) (packed x (f x)))
    (show ∀ x : X, _ = cloth (fun x => line 2 (k x)) u (fun x v => f x ((permuteNative (p x)).symm v)) x from
      fun x => packed x (fun v => f x ((permuteNative (p x)).symm v)))
  refine ⟨⟨rate,_,run',B+5412*(C+2)+2,?_⟩,9,?_⟩
  · intro x
    have c := table_raw_clock_le (by linarith : 0≤ρ) (s x) a d D B C ha hs
    have lower := hb (s x)
    apply le_trans _ c
    change ((b (s x) + ((s x).stream.length*((C+2)*⌈tableMass ρ (s x) d⌉₊)+1) : ℕ):ℝ) + 1 ≤ _
    exact_mod_cast (show b (s x) + ((s x).stream.length*((C+2)*⌈tableMass ρ (s x) d⌉₊)+1) + 1 ≤
      B*((s x).k+1)^a + (s x).stream.length*((C+2)*⌈tableMass ρ (s x) d⌉₊)+2 by omega)
  · intro x
    let n := (u x).count+(k x+1)^D
    let v := 2^(k x)*n
    have vol₁ : n ≤ v := Nat.le_mul_of_pos_left _ (by positivity)
    have roomy : (k x+1)^D ≤ n := Nat.le_add_left ..
    have vol_pos : 1≤v := ((hl x).trans roomy).trans vol₁
    have tab := (table_size (p x)).trans (Nat.mul_le_mul_left 2 ((h₂ x).trans roomy))
    have row := position_row_count (k x) (u x) (f x)
    have row' : (cloth (fun x => line 2 (k x)) u f x).count ≤ 3*v := by
      apply row.trans
      have h : (u x).count+1 ≤ n := Nat.add_le_add_left (hl x) _
      calc
        _ ≤ 3*2^(k x)*n := Nat.mul_le_mul_left _ h
        _ = _ := by dsimp [v]; ring
    have input : (together (fun x => send (table (p x))) (cloth (fun x => line 2 (k x)) u f) x).count ≤ 9*v := by
      change size (table (p x)) + _ + 1 ≤ 9*v
      omega
    have realVolume : (v : ℝ) ≤ tableRate ρ (k x) n := by
      simpa only [v,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
        (volume_le_rowRate (by linarith : 0 ≤ ρ) (k x) n).trans (rowRate_le_tableRate ρ (k x) n)
    calc
      _ ≤ ((9*v : ℕ):ℝ) := by exact_mod_cast input
      _ ≤ _ := by push_cast; exact mul_le_mul_of_nonneg_left realVolume (by norm_num)

/-- A fat payload absorbs the fixed polynomial overhead of the same executable. -/
theorem tableSchedule {ρ : ℝ} (hρ : 1/2 < ρ) :
    ∃ D : ℕ, ∀ {X : Type} (k : X → ℕ) (p : (x : X) → Equiv.Perm (Fin (k x)))
      {U : X → Type} (u : (x : X) → Series (U x)) (f : (x : X) → Block 2 (k x) → U x → Bead),
      (∀ x, (k x+1)^D ≤ (u x).count) →
      Carries (fun x => tableRate ρ (k x) (u x).count)
        (together (fun x => send (table (p x))) (cloth (fun x => line 2 (k x)) u f))
        (cloth (fun x => line 2 (k x)) u (fun x a => f x ((permuteNative (p x)).symm a))) := by
  obtain ⟨D,raw⟩ := tableScheduleWithSlack hρ
  refine ⟨D,?_⟩
  intro X k p U u f fit
  apply (raw k p u f).times (fun x => one_le_tableRate (by linarith) _ ((Nat.one_le_pow _ _ (by omega)).trans (fit x))) 2
  intro x
  simp only [tableRate_eq,Nat.cast_add]
  have extra : (((k x+1)^D : ℕ):ℝ) ≤ (u x).count := by exact_mod_cast fit x
  have rate := (one_le_positionRate (by linarith : 0≤ρ) (k x)).trans' (by norm_num : (0:ℝ)≤1)
  calc
    _ ≤ (2^(k x):ℕ) * (((u x).count:ℝ)+(u x).count) * positionRate ρ (k x) := by gcongr
    _ = _ := by push_cast; ring

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
