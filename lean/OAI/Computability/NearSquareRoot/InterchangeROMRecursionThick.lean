import OAI.Computability.NearSquareRoot.InterchangeROMRecursionOpen
import OAI.Computability.NearSquareRoot.InterchangeCenterThick

/-!
# Closing the literal native controller on its thick requests

First take the local polynomial bound of the selected body on all valid
requests. Its degree then selects a subtype preserved by both child lists.
Retyping those lists changes none of the physical code or recursion charges.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRecursion
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  NearSquareRoot.Space NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeAddress.Request
  NearSquareRoot.InterchangeSpace NearSquareRoot.InterchangeROMFrame

open private thick_mass sum_volume from OAI.Computability.NearSquareRoot.InterchangeFatRecursion

/-- Native row mass before the local degree is absorbed by thick records. -/
def localMass {b : ℕ} (a : Request b) (k : ℕ) :=
  a.rows.count*(a.recordWidth+(a.header.count+1)^k)

/-- The actual open body acts uniformly before the thickness restriction.
The two copied ledgers retain their order, multiplicity and actual volume.
The resulting constant scales the specified controller interpreted on arbitrary
outer environments, including the initial tie transition. -/
theorem close_native {b n m : ℕ} (hb : 2 ≤ b) (hm : 1 < m) (hmn : m ≤ n)
    (prelude stage : Cmd) {α θ : ℝ} (hα : 0 ≤ α) (hc : θ < (m:ℝ)^α)
    (valid : Request b → Prop) (ok : ∀ a, valid a → Admissible a) (positive : ∀ a, valid a → 0 < a.width)
    (k C H : ℕ) (small full : Subtype valid → List (Request b))
    (account : ∀ a, stepAccount valid n θ a.val (small a ++ full a))
    (shrink : ∀ a y, y ∈ small a → 3*y.rows.count ≤ 2*a.val.rows.count)
    (body : ∀ a, let cmd := node prelude stage b n
      let reserve := H*(Nat.log 2 a.val.recordVolume+1)
      At cmd cmd (job b) (small a) (full a) ((job b).issue a.val) ((job b).reply a.val)
        (C*(localMass a.val k+1)) reserve reserve) :
    Certified (controller prelude stage b n)
      (fun x : ThickRequest valid k => ⌈(x.val.recordVolume:ℝ)*(x.val.width:ℝ)^α⌉₊)
      (fun x => x.val.recordVolume) (fun x => (job b).issue x.val) (fun x => (job b).reply x.val) := by
  let X := ThickRequest valid k
  let a (i : X) : Subtype valid := ⟨i.val,i.property.1⟩
  let keep (y : Request b) := valid y ∧ Thick k y
  have closed (i : X) (y : Request b) (hy : y ∈ small (a i) ++ full (a i)) : keep y :=
    let good := (account (a i)).1 y hy
    ⟨good.1,thick_child i.property.2 good.2.2.1 good.2.2.2⟩
  let s (i : X) := (small (a i)).attachWith keep (fun y hy => closed i y (List.mem_append_left _ hy))
  let f (i : X) := (full (a i)).attachWith keep (fun y hy => closed i y (List.mem_append_right _ hy))
  have hs (i : X) : (s i).map Subtype.val = small (a i) := by simp [s]
  have hf (i : X) : (f i).map Subtype.val = full (a i) := by simp [f]
  have both (i : X) : (s i ++ f i).map Subtype.val = small (a i) ++ full (a i) := by rw [List.map_append,hs,hf]
  let V (i : X) := i.val.recordVolume
  let height (i : X) := i.val.width
  have power (i : X) : 2^height i ≤ V i := calc
    _ ≤ 2^i.val.digits := Nat.pow_le_pow_right (by decide) (by dsimp [height,digits]; omega)
    _ ≤ i.val.rows.count := pow_digits_le _ hb (ok i.val i.property.1)
    _ ≤ _ := rows_le_recordVolume _
  let A := (2*b+9)^k+1
  have sharp : Sharp (node prelude stage b n) (fun _ => node prelude stage b n) (thickJob valid k)
      s f V (C*(A+1)) H (thickJob valid k).issue (thickJob valid k).reply := by
    intro i
    have raw := (body (a i)).restrict_calls keep (s i) (f i) (hs i) (hf i)
    have hr := thick_mass (fun i : X => i.val) hb k (fun i => ok _ i.property.1) (fun i => i.property.2) i
    rw [← cast_massNat] at hr
    have mass : localMass i.val k ≤ A*V i := by exact_mod_cast hr
    have vp : 1 ≤ V i := (Nat.pow_pos (by decide)).trans_le (power i)
    have scaled : C*(localMass i.val k+1) ≤ C*(A+1)*V i := by
      rw [Nat.mul_assoc,Nat.add_mul,Nat.one_mul]
      exact Nat.mul_le_mul_left _ (by omega)
    exact raw.mono scaled le_rfl le_rfl
  have law (i : X) : stepAccount valid n θ i.val ((s i ++ f i).map Subtype.val) := both i ▸ account (a i)
  have child (x y : X) (hy : y ∈ s x ++ f x) := (law x).1 y.val (List.mem_map_of_mem hy)
  apply resolve_controller_width b n prelude stage sharp height m α θ hm hα hc
    (fun i => positive i.val i.property.1) power
  · intro x y hy
    change y.val.width * m ≤ x.val.width
    rw [(child x y hy).2.1]
    exact (Nat.mul_le_mul_left _ hmn).trans (lanes_mul_le _ _)
  · intro i
    simpa only [List.map_map,Function.comp_def] using sum_volume valid (law i)
  · intro x y hy
    have eq := (child x y (List.mem_append_left _ hy)).2.2.1
    have mem := List.mem_map_of_mem (f:=Subtype.val) hy
    rw [hs] at mem
    have counts := shrink (a x) y.val mem
    simpa only [V,recordVolume,eq,← Nat.mul_assoc] using
      Nat.mul_le_mul_right (x.val.recordWidth+1) counts
  · intro x y hy
    have facts := (child x y (List.mem_append_right _ hy)).2.2
    dsimp only [V,recordVolume]
    rw [facts.1]
    exact Nat.mul_le_mul_right _ facts.2

end InterchangeROMRecursion

end NearSquareRoot
end Computability
end OAI
