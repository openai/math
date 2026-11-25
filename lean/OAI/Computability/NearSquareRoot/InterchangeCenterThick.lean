import OAI.Computability.NearSquareRoot.InterchangeBQuestMixed
import OAI.Computability.NearSquareRoot.InterchangeCenterRetype
import OAI.Computability.NearSquareRoot.InterchangeFatRecursion

/-!
# Selecting the recursive center on thick requests

Compile the center on all internal requests, then use its local degree to
select the record thickness. Both child ledgers retain their order and
multiplicity under the admissible thick-request encoding.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom NearSquareRoot.Space NearSquareRoot.InterchangeSpace

open private thick_mass from OAI.Computability.NearSquareRoot.InterchangeFatRecursion

variable {b : ℕ}

abbrev ThickInternal (valid : Request b → Prop) (n k : ℕ) :=
  {x : ThickRequest valid k // n < x.val.width}

abbrev fromThick {valid : Request b → Prop} {n k : ℕ} (i : ThickInternal valid n k) :
    Internal valid n := ⟨⟨i.val.val,i.val.property.1⟩,i.property⟩

abbrev thickJob (valid : Request b → Prop) (k : ℕ) : Job (ThickRequest valid k) :=
  ⟨fun x => (job b).issue x.val, fun x => (job b).reply x.val⟩

/-- A single degree suffices to bound all local work linearly in record
volume while preserving the logarithmic reserve beside full-volume children. -/
theorem center_on_thick (valid : Request b → Prop) (hb : 2 ≤ b)
    (ok : ∀ a, valid a → Admissible a) (n : ℕ) (θ : ℝ)
    (small full : Internal valid n → List (Request b)) (park : Internal valid n → ℕ) (H : ℕ)
    (account : ∀ u, stepAccount valid n θ u.val.val (small u ++ full u))
    (head : ∀ u, park u ≤ H * (Nat.log 2 u.val.val.recordVolume + 1))
    (center : CenterBody (regime internalRequest) (fun u => u.val.val.rows.count)
      (fun u => u.val.val.recordWidth) (job b) small full park
      ((job b).issue ∘ internalRequest) ((job b).reply ∘ internalRequest)) :
    ∃ k, ∃ s f : ThickInternal valid n k → List (ThickRequest valid k),
      (∀ i, (s i).map Subtype.val = small (fromThick i)) ∧
      (∀ i, (f i).map Subtype.val = full (fromThick i)) ∧
      Mixed (thickJob valid k) s f (fun i => i.val.val.recordVolume)
        (fun i => (job b).issue i.val.val) (fun i => (job b).reply i.val.val) := by
  obtain ⟨k,K,cmd,run⟩ := center.build
  let S := ThickInternal valid n k
  let xs (i : S) := i.val.val
  let allowed (x : Request b) := valid x ∧ Thick k x
  have safe (i : S) (y : Request b) (hy : y ∈ small (fromThick i) ++ full (fromThick i)) :
      allowed y :=
    let h := (account (fromThick i)).1 y hy
    ⟨h.1,thick_child i.val.property.2 h.2.2.1 h.2.2.2⟩
  let s (i : S) := (small (fromThick i)).attachWith allowed fun y hy =>
    safe i y (List.mem_append_left _ hy)
  let f (i : S) := (full (fromThick i)).attachWith allowed fun y hy =>
    safe i y (List.mem_append_right _ hy)
  have hs (i : S) : (s i).map Subtype.val = small (fromThick i) := by simp [s]
  have hf (i : S) : (f i).map Subtype.val = full (fromThick i) := by simp [f]
  let A := (2*b+9)^k + 1
  refine ⟨k,s,f,hs,hf,cmd,K*(A+1),H+1,?_⟩
  intro i parent env time data depth children deck base hcap
  let V := (xs i).recordVolume
  let M := massNat (regime xs) (fun u => (xs u).rows.count) (fun u => (xs u).recordWidth) k i
  let L := K*(M+1)
  have hr := thick_mass xs hb k (fun u => ok _ u.val.property.1)
    (fun u => u.val.property.2) i
  rw [← cast_massNat] at hr
  have size : M ≤ A*V := by exact_mod_cast hr
  have pos : 1 ≤ V := ((Nat.pow_pos (by decide : 0 < 2)).trans_le
    (pow_digits_le (xs i) hb (ok _ i.val.property.1))).trans_le (xs i).rows_le_recordVolume
  have work : L ≤ K*(A+1)*V := by
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [Nat.add_mul,Nat.one_mul]
    omega
  let R := Nat.log 2 V+1
  have hdr : park (fromThick i) ≤ (H+1)*R :=
    (head (fromThick i)).trans (Nat.mul_le_mul_right R (Nat.le_succ _))
  have ret : 1 ≤ (H+1)*R := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have typed : CenterBody.CenterRun (thickJob valid k) (s i) (f i) cmd
      ((job b).issue (xs i)) ((job b).reply (xs i)) L (park (fromThick i)) 1 :=
    CenterBody.CenterRun.restrict_calls (run (fromThick i)) allowed (s i) (f i) (hs i) (hf i)
  apply (typed parent env time data depth children deck base hcap).mono
  · exact Nat.add_le_add_right work _
  · exact Nat.add_le_add_left (max_le_max (Nat.add_le_add_right work _)
      (Nat.add_le_add_right hdr _)) _
  · exact max_le_max (Nat.add_le_add_right work _) (Nat.add_le_add_right ret _)

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
