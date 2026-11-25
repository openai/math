import OAI.Computability.NearSquareRoot.InterchangeNumericMinor
import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasTypes

/-! # Numerical reconstruction of rectangle matrices and incidence bounds -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.TemplateMasks

open InterchangeROMRepair.Raw FlatAtlas KernelComputableAddress StageLedger

def flag (bits : List Bool) (l t : ℕ) (s : Bool) (key v : ℕ) : ℕ :=
  if mask bits l t s key v then 1 else 0

def matrix (bits : List Bool) (l t : ℕ) : Mat :=
  add ident (mult t (fun i j => flag bits l t true j i) (flag bits l t false))

def degree (bits : List Bool) (l t : ℕ) (s : Bool) (v : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, flag bits l t s i v

def MaskRepresents {l t : ℕ} (bits : List Bool) (r : Fin t → Rectangle (Fin l)) :=
  ∀ s (i : Fin t) (v : Fin l), (v ∈ if s then (r i).destinations else (r i).sources) ↔
    mask bits l t s i v = true

theorem degree_eq {l t : ℕ} (bits : List Bool) (r : Fin t → Rectangle (Fin l))
    (hr : MaskRepresents bits r) (s : Bool) (v : Fin l) :
    degree bits l t s v = Fintype.card (Incident r s v) := by
  rw [degree,← Fin.sum_univ_eq_sum_range]
  change _ = Fintype.card {i : Fin t // v ∈ if s then (r i).destinations else (r i).sources}
  rw [Fintype.card_subtype, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [flag,hr s i v]

theorem matrix_eq (p l t : ℕ) [Fact (p+1).Prime] (bits : List Bool) (r : Fin t → Rectangle (Fin l))
    (hr : MaskRepresents bits r) :
    interpret p l l (matrix bits l t) = rectangleMatrix r := by
  rw [matrix,interpret_add,interpret_ident,interpret_mult]
  ext i j
  simp only [Matrix.add_apply,Matrix.mul_apply,rectangleMatrix,Matrix.of_apply,Matrix.one_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hd : i ∈ (r k).destinations ↔ mask bits l t true k i = true := hr true k i
  have hs : j ∈ (r k).sources ↔ mask bits l t false k j = true := hr false k j
  simp only [interpret,flag,hd,hs]
  cases mask bits l t true k i <;> cases mask bits l t false k j <;> simp

variable {X : Type} [Primcodable X]

theorem primrec_flag {bits : X → List Bool} {l t key v : X → ℕ} (s : Bool)
    (hs : Primrec bits) (hl : Primrec l) (ht : Primrec t) (hk : Primrec key) (hv : Primrec v) :
    Primrec fun x => flag (bits x) (l x) (t x) s (key x) (v x) := by
  let idx := Primrec.nat_add.comp (Primrec.nat_mul.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const s.toNat) ht) hk) hl) hv
  have hbit := (Primrec.list_getD false).comp hs idx
  exact Primrec.ite (Primrec.eq.comp hbit (Primrec.const true)) (Primrec.const 1) (Primrec.const 0)

theorem primrec_matrix {bits : X → List Bool} {l t : X → ℕ}
    (hs : Primrec bits) (hl : Primrec l) (ht : Primrec t) : EntryPR fun x => matrix (bits x) (l x) (t x) :=
  primrec_ident.add (EntryPR.mult ht
    (primrec_flag true (hs.comp .fst) (hl.comp .fst) (ht.comp .fst) (Primrec.snd.comp .snd) (Primrec.fst.comp .snd))
    (primrec_flag false (hs.comp .fst) (hl.comp .fst) (ht.comp .fst) (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)))

theorem primrec_degree {bits : X → List Bool} {l t v : X → ℕ} (s : Bool)
    (hs : Primrec bits) (hl : Primrec l) (ht : Primrec t) (hv : Primrec v) :
    Primrec fun x => degree (bits x) (l x) (t x) s (v x) :=
  primrec_rangeSum ht (primrec_flag s (hs.comp .fst) (hl.comp .fst) (ht.comp .fst) .snd (hv.comp .fst)).to₂

end Interchange.TemplateMasks

end NearSquareRoot
end Computability
end OAI
