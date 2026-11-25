import OAI.Computability.BorderVNP.CellTypedRecordSize
import OAI.Computability.BorderVNP.CellPacketInputSize
import OAI.Computability.BorderVNP.CellLocalFactorLength

/-! # Physical size of the private compiler's typed directory

Each nested list quotes its elements and contributes one empty-list tag.
The scalar transport has one count field per list. Charging those tags against
the transported fields controls the real compiler input even for empty boxes
and empty reported words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet

open ExactQuantumFactoring.BitStackProgram

private theorem list_charge {α : Type} (raw : α → List ℕ) (enc : α → List Bool) (xs : List α)
    {C W : ℕ} (hW : 0 < W) (hr : ∀ x ∈ xs, 0 < (raw x).length)
    (he : ∀ x ∈ xs, (enc x).length ≤ C*(raw x).length*W) :
    (listCode enc xs).length ≤ (2*C+2)*(fieldList raw xs).length*W := by
  induction xs with
  | nil =>
    change 1 ≤ (2*C+2)*1*W
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  | cons x xs ih =>
    have hx := he x List.mem_cons_self
    have hpos := hr x List.mem_cons_self
    have htail := ih (fun z hz => hr z (.tail _ hz)) (fun z hz => he z (.tail _ hz))
    have hlen : (fieldList raw (x::xs)).length = (raw x).length + (fieldList raw xs).length := by
      simp only [fieldList,List.flatMap_cons,List.length_cons,List.length_append,Nat.add_assoc]
    rw [listCode_length_cons,hlen,Nat.mul_add,Nat.add_mul]
    apply Nat.add_le_add _ htail
    calc 2*(enc x).length+2 ≤ 2*(C*(raw x).length*W)+2*((raw x).length*W) := by
           have h := Nat.mul_pos hpos hW
           omega
         _ = _ := by ring

private theorem typed_vector (bs : List ℕ) {U : ℕ} (h : ∀ i ∈ bs, i ≤ U) :
    (Typed.naturals bs).length ≤ 4*(vector bs).length*(U.size+1) := by
  have hh := list_charge (fun i : ℕ => [i]) Nat.bits bs (C := 1) (W := U.size+1)
    (by omega) (fun _ _ => by simp)
    (fun i hi => by simp only [List.length_singleton,Nat.size_eq_bits_len,Nat.one_mul]; have := Nat.size_le_size (h i hi); omega)
  have hv : fieldList (fun i : ℕ => [i]) bs = vector bs := by simp [fieldList,vector]
  simpa only [hv] using hh

/-- The complete typed CQF directory has length linear in its scalar count and largest
field width. Every stored factor is charged, including factors in unreferenced boxes. -/
theorem typed_directory_length (D : Directory) (p : ℕ) {U : ℕ} (h : RawFields D p U) :
    (Typed.directory D).length ≤ 300*(words D p).length*(U.size+1) := by
  let W := U.size+1
  have hW : 0 < W := by dsimp [W]; omega
  have hf (f : Factor) : 0 < (factor f).length := by cases f <;> simp [factor,port,vector]
  have hr (r : Record) : 0 < (record r).length := by cases r <;> simp [record,port,vector,fieldList]
  have hbox (fs : List Factor) (hm : fs ∈ D.boxes) :
      (listCode Typed.factor fs).length ≤ 66*(fieldList factor fs).length*W :=
    list_charge factor Typed.factor fs (C := 32) hW (fun f _ => hf f)
      (fun f hf' => typed_factor_length f ((h.boxes fs hm).2 f hf'))
  have hb := list_charge (fieldList factor) (listCode Typed.factor) D.boxes (C := 66) hW
    (fun fs _ => by simp [fieldList]) hbox
  have hrec := list_charge record Typed.record D.records (C := 64) hW (fun r _ => hr r)
    (fun r hm => typed_record_length r (h.records r hm))
  have hrep := list_charge vector Typed.naturals D.reportedCounts (C := 4) hW
    (fun bs _ => by simp [vector]) (fun bs hm => typed_vector bs ((h.reports bs hm).2))
  simp only [Typed.directory,prodCode,pairBits_length,words,List.length_append,List.length_singleton]
  change _ ≤ 300*(1+_+_+_)*W
  rw [show 300*(1+(fieldList (fieldList factor) D.boxes).length+(fieldList record D.records).length+
      (fieldList vector D.reportedCounts).length)*W =
      300*W+300*((fieldList (fieldList factor) D.boxes).length*W)+300*((fieldList record D.records).length*W)+
      300*((fieldList vector D.reportedCounts).length*W) by ring]
  rw [Nat.mul_assoc] at hb hrec hrep
  omega

/-- The private-wire count precedes the directory as one canonical quoted scalar. -/
theorem typed_input_length (D : Directory) (p : ℕ) {U : ℕ} (h : RawFields D p U) :
    (Typed.input (p,D)).length ≤ 320*(words D p).length*(U.size+1) := by
  have hd := typed_directory_length D p h
  have hp := Nat.size_le_size h.privateWires
  have hw : 0 < (words D p).length := by simp [words]
  have hW := Nat.le_mul_of_pos_left (U.size+1) hw
  simp only [Typed.input,prodCode,pairBits_length,Nat.size_eq_bits_len]
  rw [Nat.mul_assoc] at hd ⊢
  omega

private theorem static_size (D : Directory) (p : ℕ) {A M U B j n C T : ℕ}
    (hs : D.StaticBounds A M) (hstore : storedMass D ≤ A*(M+1)^2) (hu : U ≤ B*(n+2)^j)
    (hT : T ≤ C*(words D p).length*(U.size+1)) :
    T ≤ C*(8*A+4)*(B.size+j+1)*(M+1)^2*(n.size+1) := by
  have h₁ := words_length_from_static D p hs hstore
  have h₂ := CellMacro.Generator.size_of_polynomial_field hu
  have hw : U.size+1 ≤ (B.size+j+1)*(n.size+1) := by
    rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
    have := Nat.le_mul_of_pos_right B.size (by omega : 0 < n.size+1)
    omega
  calc T ≤ C*(words D p).length*(U.size+1) := hT
       _ ≤ C*((8*A+4)*(M+1)^2)*((B.size+j+1)*(n.size+1)) :=
         Nat.mul_le_mul (Nat.mul_le_mul_left C h₁) hw
       _ = _ := by ring

/-- The complete typed directory occupies quadratic local-load space times one binary-width factor. -/
theorem typed_directory_length_static (D : Directory) (p : ℕ) {A M U B j n : ℕ}
    (hs : D.StaticBounds A M) (hstore : storedMass D ≤ A*(M+1)^2) (h : RawFields D p U)
    (hu : U ≤ B*(n+2)^j) :
    (Typed.directory D).length ≤ 300*(8*A+4)*(B.size+j+1)*(M+1)^2*(n.size+1) :=
  static_size D p hs hstore hu (typed_directory_length D p h)

/-- The same static scale bounds the complete typed input to the finite compiler. -/
theorem typed_input_length_static (D : Directory) (p : ℕ) {A M U B j n : ℕ}
    (hs : D.StaticBounds A M) (hstore : storedMass D ≤ A*(M+1)^2) (h : RawFields D p U)
    (hu : U ≤ B*(n+2)^j) :
    (Typed.input (p,D)).length ≤ 320*(8*A+4)*(B.size+j+1)*(M+1)^2*(n.size+1) :=
  static_size D p hs hstore hu (typed_input_length D p h)

end CellSparse.Packet

end BorderVNP
end Computability
end OAI
