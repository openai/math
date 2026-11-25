import OAI.Computability.BorderVNP.CellDirectoryInputSize
import OAI.Computability.BorderVNP.CellPacketFields

/-! # Physical length of a typed sparse cell packet

All boxes in the directory contribute, even if no public row uses them. The encoded
words also contain raw IDs and histogram values. Their binary widths are measured
before either the presence checks or the equality tests have been compiled.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet

open CellMacro.Generator RationalHitting.StackLanguage

/-- Static one-copy factor table mass of all *stored* boxes, including one header
per box, whether or not a public row refers to it. -/
def storedMass (D : Directory) : ℕ :=
  D.boxes.length + (D.boxes.map fun fs => (fs.map Factor.staticMass).sum).sum

private theorem flatMap_le {α β : Type} (xs : List α) (f : α → List β) (w : α → ℕ) (C : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ C*w x) : (xs.flatMap f).length ≤ C*(xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih fun y hy => h y (.tail _ hy))

private theorem factor_length_le (f : Factor) : (factor f).length ≤ 5*f.staticMass := by
  cases f with
  | truth ws rs | sign ws rs | gadget ws rs =>
    simp [factor,vector,Factor.staticMass]
    nlinarith [Nat.zero_le (ws.length*rs.length)]
  | unary w p => rfl

private theorem record_length_le (r : Record) : (record r).length ≤ r.guardMassBound := by
  cases r with
  | zero c l p | equal c l p q | box id b c stride => simp [record,port,Record.guardMassBound]
  | profile c p w hist rs =>
    have hr := flatMap_le rs route (fun _ => 1) 8 (fun _ _ => le_rfl)
    simp only [List.map_const',List.sum_replicate_nat,Nat.mul_one] at hr
    simp only [record,Record.guardMassBound,port,vector,fieldList,List.length_cons,List.length_append,List.length_nil]
    nlinarith [Nat.zero_le (w*hist.length),Nat.zero_le (w*rs.length)]

private theorem boxes_words_le (bs : List (List Factor)) :
    (bs.flatMap (fieldList factor)).length ≤
      bs.length + 5*(bs.map fun fs => (fs.map Factor.staticMass).sum).sum := by
  induction bs with
  | nil => simp
  | cons fs bs ih =>
    have h := flatMap_le fs factor Factor.staticMass 5 (fun f _ => factor_length_le f)
    simp only [List.flatMap_cons,List.length_append,fieldList,List.length_cons,List.map_cons,List.sum_cons] at ⊢
    omega

private theorem reports_words (reports : List (List ℕ)) :
    (reports.flatMap vector).length = reports.length + (reports.map List.length).sum := by
  induction reports with
  | nil => rfl
  | cons bs r ih => simp [vector,ih]; omega

/-- Number of transported scalar fields; all emitted private factors and public rows
are charged directly to the input that contains them. -/
theorem words_length_le (D : Directory) (p : ℕ) : (words D p).length ≤
    5*storedMass D + D.recordMass + D.reportWidth + D.reportedCounts.length + 4 := by
  have hb := boxes_words_le D.boxes
  have hr := flatMap_le D.records record Record.guardMassBound 1 (fun r _ => by simpa using record_length_le r)
  simp only [Nat.one_mul] at hr
  simp only [words,fieldList,List.length_append,List.length_cons,List.length_nil,
    storedMass,Directory.recordMass,Directory.reportWidth,reports_words]
  omega

private theorem scalar_records_le (ws : List ℕ) {L : ℕ} (h : ∀ x ∈ ws, x.size ≤ L) :
    (records (ws.map Nat.bits)).length ≤ ws.length*(2*L+2) := by
  induction ws with
  | nil => simp [records]
  | cons x ws ih =>
    have ht := ih fun y hy => h y (.tail _ hy)
    have hx := h x List.mem_cons_self
    simp only [List.map_cons,records,List.length_cons,List.length_append,codeWord_length,Nat.size_eq_bits_len]
    rw [Nat.succ_mul ws.length]
    omega

/-- The numerical width factor accounts for uncompiled values of all transported words. -/
theorem bits_length_le (D : Directory) (p : ℕ) {U : ℕ} (h : RawFields D p U) :
    (bits D p).length ≤ (5*storedMass D + D.recordMass + D.reportWidth + D.reportedCounts.length + 4) *
      (2*(max 3 U).size+2) :=
  (scalar_records_le _ (fun x hx => Nat.size_le_size (words_bounded D p h x hx))).trans (Nat.mul_le_mul_right _ (words_length_le D p))

/-- A certified scalar count for the raw directory suffices directly; no unused tables
or zero-valued metadata may be omitted from that count. -/
theorem input_length_of_word_count (D : Directory) (p : ℕ) (ext : List Bool) {W U B j n : ℕ}
    (hw : (words D p).length ≤ W) (hwords : ∀ x ∈ words D p, x ≤ U) (hu : U ≤ B*(n+2)^j) :
    (input D p ext).length ≤ 4*W*(B.size+j+1)*(n.size+1) + 1 + ext.length := by
  have hsize := size_of_polynomial_field hu
  have hb : U.size+1 ≤ (B.size+j+1)*(n.size+1) := by
    simp only [Nat.add_mul,Nat.one_mul,Nat.mul_add,Nat.mul_one] at hsize ⊢
    omega
  have hd : 2*U.size+2 ≤ 2*((B.size+j+1)*(n.size+1)) := by
    simpa only [Nat.mul_add,Nat.mul_one] using Nat.mul_le_mul_left 2 hb
  have hs : (bits D p).length ≤ W*(2*((B.size+j+1)*(n.size+1))) :=
    (scalar_records_le _ (fun x hx => Nat.size_le_size (hwords x hx))).trans (Nat.mul_le_mul hw hd)
  rw [input,List.length_append,codeWord_length]
  calc
    _ ≤ 2*(W*(2*((B.size+j+1)*(n.size+1)))) + 1 + ext.length := by omega
    _ = _ := by ring

/-- Bounding all stored one-copy factors and the public rows bounds the number
of transported scalars quadratically in the local load scale. -/
theorem words_length_from_static (D : Directory) (p : ℕ) {A M : ℕ}
    (hstatic : D.StaticBounds A M) (hstore : storedMass D ≤ A*(M+1)^2) :
    (words D p).length ≤ (8*A+4)*(M+1)^2 := by
  let X := M+1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hX2 : X ≤ X^2 := by simpa [pow_two] using Nat.mul_le_mul_left X hX
  have hr := hstatic.records
  have hd := hstatic.digits
  have hl := hstatic.reports.trans (Nat.mul_le_mul_left A hX2)
  have hw : 5*storedMass D + D.recordMass + D.reportWidth + D.reportedCounts.length + 4 ≤
      (8*A+4)*X^2 := by
    change storedMass D ≤ A*X^2 at hstore
    change D.recordMass ≤ A*X^2 at hr
    change D.reportWidth ≤ A*X^2 at hd
    nlinarith only [hstore,hr,hd,hl,hX2,hX]
  exact (words_length_le D p).trans hw

/-- The true framed private input includes one copy of every external value. If its
source word fields have polynomial magnitude, their transport costs a single factor
of the binary input width. -/
theorem input_length_le_of_words (D : Directory) (p : ℕ) (ext : List Bool) {A M U B j n : ℕ}
    (hstatic : D.StaticBounds A M) (hstore : storedMass D ≤ A*(M+1)^2)
    (hwords : ∀ x ∈ words D p, x ≤ U) (hu : U ≤ B*(n+2)^j) :
    (input D p ext).length ≤ (4*(8*A+4)*(B.size+j+1))*(M+1)^2*(n.size+1) + 1 + ext.length := by
  have h := input_length_of_word_count D p ext (words_length_from_static D p hstatic hstore) hwords hu
  apply h.trans_eq
  ring

/-- A source-level proof of the data-field bounds suffices for the physical input estimate. -/
theorem input_length_le (D : Directory) (p : ℕ) (ext : List Bool) {A M U B j n : ℕ}
    (hstatic : D.StaticBounds A M) (hstore : storedMass D ≤ A*(M+1)^2)
    (hraw : RawFields D p U) (hu : U ≤ B*(n+2)^j) :
    (input D p ext).length ≤ (4*(8*A+4)*((B+3).size+j+1))*(M+1)^2*(n.size+1) + 1 + ext.length := by
  have hn : 1 ≤ (n+2)^j := Nat.one_le_pow _ _ (by omega)
  apply input_length_le_of_words _ _ _ hstatic hstore (words_bounded _ _ hraw)
  rw [Nat.add_mul]; omega

end CellSparse.Packet

end BorderVNP
end Computability
end OAI
