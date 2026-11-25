import OAI.Computability.NearSquareRoot.InterchangeROMRepair
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPRMatrix

/-! # Row-major ground repair tables and little-endian sign masks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Raw

open KernelComputableAddress

abbrev Tape := List (List ℕ)

def atSlot (t : Tape) (u cols : ℕ) : Mat := read cols (t.getD u [])

theorem primrec_atSlot {X : Type*} [Primcodable X] {t : X → Tape} {u cols : X → ℕ}
    (ht : Primrec t) (hu : Primrec u) (hc : Primrec cols) :
    EntryPR fun x => atSlot (t x) (u x) (cols x) :=
  primrec_read hc ((Primrec.list_getD []).comp ht hu)

def mask {m : ℕ} : (Fin m → Bool) ≃ Fin (2^m) :=
  (Equiv.piCongrRight fun _ => finTwoEquiv.symm).trans finFunctionFinEquiv

theorem mask_bit {m : ℕ} (η : Fin m → Bool) (j : Fin m) :
    digit 2 (mask η).val j.val = (η j).toNat := by
  have h := congrArg (fun f : Fin m → Fin 2 => (f j).val)
    (finFunctionFinEquiv.symm_apply_apply (fun i => finTwoEquiv.symm (η i)))
  change digit 2 _ _ = _ at h
  rw [show digit 2 (mask η).val j.val = _ from h]
  cases h' : η j <;> rfl

theorem mask_surjective (m : ℕ) : Function.Surjective (mask (m := m)) := mask.surjective

def decode (p w s m : ℕ) (t : Tape) : Spec (ZMod (p+1)) (Fin w) (Fin s) m where
  base := interpret p w w (atSlot t 0 w)
  term j := interpret p w w (atSlot t (1+j.val) w)
  extract := interpret p s w (atSlot t (1+m) w)
  restore := interpret p w s (atSlot t (2+m) s)
  correct η out input := interpret p s s (atSlot t
    (3+m+4*(mask η).val+2*out.toNat+input.toNat) s)

def matrixTape {p a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod (p+1))) : List ℕ :=
  write a b fun i j => if hi : i < a then if hj : j < b then (M ⟨i,hi⟩ ⟨j,hj⟩).val else 0 else 0

@[simp] theorem interpret_matrixTape {p a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod (p+1))) :
    interpret p a b (read b (matrixTape M)) = M := by
  ext i j
  simp [interpret,matrixTape,read_write _ i.isLt j.isLt]

/-- The contents of each matrix slot in the serialized table. -/
private def slot {p w s m : ℕ} (t : Spec (ZMod (p+1)) (Fin w) (Fin s) m) (u : ℕ) : List ℕ :=
  if u = 0 then matrixTape t.base
  else if h : u-1 < m then matrixTape (t.term ⟨u-1,h⟩)
  else if u = 1+m then matrixTape t.extract
  else if u = 2+m then matrixTape t.restore
  else
    let n := u-(3+m)
    if h : n/4 < 2^m then
      matrixTape (t.correct (mask.symm ⟨n/4,h⟩) (decide (2 ≤ n%4)) (decide (n%2 = 1)))
    else []

def encode {p w s m : ℕ} (t : Spec (ZMod (p+1)) (Fin w) (Fin s) m) : Tape :=
  (List.range (3+m+4*2^m)).map (slot t)

private theorem atSlot_encode {p w s m : ℕ} (t : Spec (ZMod (p+1)) (Fin w) (Fin s) m)
    (u cols : ℕ) (h : u < 3 + m + 4*2^m) :
    atSlot (encode t) u cols = read cols (slot t u) := by
  rw [atSlot,List.getD_eq_getElem _ _ (by simpa [encode] using h)]
  simp [encode]

private theorem slot_correct {p w s m : ℕ} (t : Spec (ZMod (p+1)) (Fin w) (Fin s) m)
    (η : Fin m → Bool) (o i : Bool) :
    slot t (3+m+4*(mask η).val+2*o.toNat+i.toNat) = matrixTape (t.correct η o i) := by
  let v := 3+m+4*(mask η).val+2*o.toNat+i.toNat
  change slot t v = _
  have ho : o.toNat ≤ 1 := by cases o <;> decide
  have hi : i.toNat ≤ 1 := by cases i <;> decide
  have h0 : v ≠ 0 := by dsimp [v]; omega
  have h1 : ¬ v-1 < m := by dsimp [v]; omega
  have h2 : v ≠ 1+m := by dsimp [v]; omega
  have h3 : v ≠ 2+m := by dsimp [v]; omega
  have div : (v-(3+m))/4 = (mask η).val := by dsimp [v]; omega
  have out : decide (2 ≤ (v-(3+m))%4) = o := by
    cases o <;> cases i <;> simp [v] <;> omega
  have inp : decide ((v-(3+m))%2 = 1) = i := by
    cases o <;> cases i <;> simp [v] <;> omega
  simp [slot,h0,h1,h2,h3,div,out,inp]

@[simp] theorem decode_encode {p w s m : ℕ} (t : Spec (ZMod (p+1)) (Fin w) (Fin s) m) :
    decode p w s m (encode t) = t := by
  obtain ⟨b,f,h,g,k⟩ := t
  rw [decode, Spec.mk.injEq]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp (disch := omega) [atSlot_encode,slot]
  · funext j
    have hj := j.isLt
    simp (disch := omega) [atSlot_encode,slot]
  · simp (disch := omega) [atSlot_encode,slot]
  · simp (disch := omega) [atSlot_encode,slot]
  · funext η o i
    have hk := (mask η).isLt
    have ho : o.toNat ≤ 1 := by cases o <;> decide
    have hi : i.toNat ≤ 1 := by cases i <;> decide
    simp (disch := omega) only [atSlot_encode,slot_correct,interpret_matrixTape]

theorem decode_surjective (p w s m : ℕ) : Function.Surjective (decode p w s m) :=
  fun t => ⟨encode t,decode_encode t⟩

end InterchangeROMRepair.Raw

end NearSquareRoot
end Computability
end OAI
