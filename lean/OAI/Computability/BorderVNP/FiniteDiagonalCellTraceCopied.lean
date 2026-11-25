import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceAssignment
import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceBurst
import OAI.Computability.BorderVNP.FiniteCellCopiesScan

/-! # Connecting repeated field boxes to one private wire-guess prefix

The repeated box addresses each copy's interior and exterior wires together.
The private interpreter instead guesses one contiguous prefix. Guess the entire
repeated wire interval and use one strided equality record to tie every exterior
position to its delivered literal. The actual bit-major joint report follows
the delivered exterior bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.CellTrace.Copied

open Crossing CellSparse FieldDirectory VPVNP.RAMSerialization
open scoped Classical BigOperators

variable {d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network d P bits)

/-- The private edge lanes of one copy. -/
abbrev Internal := Σ e : N.Edge, Fin (N.width e)
/-- The supplied port lanes of one copy. -/
abbrev Supplied (bits : P → ℕ) := Σ p : P, Fin (bits p)

private noncomputable def index {copies : ℕ} (i : Fin copies) (wire : Wire N) : Fin (Copies.width N copies) :=
  finProdFinEquiv (i,wireNumber N wire)

/-- Every initial guessed bit is an interior or exterior lane of exactly one copy. -/
noncomputable def guessedEquiv (copies : ℕ) :
    (Fin copies → N.Assignment) × (Fin copies → Ports bits) ≃ (Fin (Copies.width N copies) → Bool) where
  toFun pair j :=
    let i := finProdFinEquiv.symm j
    match (wireNumber N).symm i.2 with
    | .inl ⟨e,k⟩ => pair.1 i.1 e k
    | .inr ⟨p,k⟩ => pair.2 i.1 p k
  invFun f := (fun i e k => f (index N i (.inl ⟨e,k⟩)), fun i p k => f (index N i (.inr ⟨p,k⟩)))
  left_inv := by
    rintro ⟨a,y⟩
    apply Prod.ext <;> funext i v k <;> simp only [index,Equiv.symm_apply_apply]
  right_inv := by
    intro g
    funext j
    obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective j
    obtain ⟨u,rfl⟩ := (wireNumber N).surjective k
    cases u <;> simp [index]

/-- Supplied lanes arrive in copy order, then the directory's exterior-bit order. -/
noncomputable def publicBits {copies : ℕ} (x : Fin copies → Ports bits) : List Bool :=
  List.ofFn fun j : Fin (copies * Fintype.card (Supplied bits)) =>
    let i := finProdFinEquiv.symm j
    let p := (Fintype.equivFin (Supplied bits)).symm i.2
    x i.1 p.1 p.2

variable {F : Type*} [Fintype F]

/-- Same payload as the single-tape field scalar multiplier. -/
def reportBits {w : ℕ} (c : Fin (Fintype.card F) → Fin w → Bool) :=
  Burst.payload fun i j => c j i

private theorem reportBits_eq {w : ℕ} (c : Fin (Fintype.card F) → Fin w → Bool) :
    reportBits c = List.ofFn fun j : Fin (w*Fintype.card F) =>
      c (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm j).1 := by
  rw [List.ofFn_mul]
  unfold reportBits Burst.payload
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  symm
  simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using
    congrArg (fun z : Fin w × Fin (Fintype.card F) => c z.2 z.1) (finProdFinEquiv.symm_apply_apply (i,j))

/-- The native external literal stack includes the delivered boundary and joint subtotal. -/
noncomputable def external {copies w : ℕ} (x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) :=
  publicBits x ++ reportBits c

/-- Source and destination of the repeated equality row tying each guessed exterior lane. -/
noncomputable def guessedPort : CellSparse.Port :=
  ⟨Fintype.card (Internal N),Fintype.card (Wire N),1⟩

/-- Beginning and stride of the corresponding delivered exterior lane. -/
noncomputable def deliveredPort (copies : ℕ) : CellSparse.Port :=
  ⟨Copies.width N copies,Fintype.card (Supplied bits),1⟩

/-- Both repetitions use a single stored table list and a single stored tie
record for all exterior lanes, independent of the multiplicity. -/
noncomputable def directory (sites : List N.Site) (table : N.Tables F) (copies w : ℕ) : Directory :=
  let original := Copies.directory N sites table copies w
  { original with
    records := .equal copies (Fintype.card (Supplied bits)) (guessedPort N) (deliveredPort N copies) :: original.records
    reportedCounts := original.reportedCounts.map (List.map (copies * Fintype.card (Supplied bits) + ·)) }

private theorem lookupPrefix {k : ℕ} (f : Fin k → Bool) (tail : List Bool) (i : Fin k) :
    CellSparse.lookup (List.ofFn f ++ tail) i.val = f i := by
  simp only [CellSparse.lookup,List.head?_drop,List.getElem?_append_left (by simp : i.val < (List.ofFn f).length),
    List.getElem?_ofFn,dite_eq_left i.isLt,Fin.eta,Option.getD_some]

private theorem lookupSuffix {k : ℕ} (f : Fin k → Bool) (tail : List Bool) (i : ℕ) :
    CellSparse.lookup (List.ofFn f ++ tail) (k+i) = CellSparse.lookup tail i := by
  simp only [CellSparse.lookup,List.head?_drop,List.getElem?_append_right (by simp : (List.ofFn f).length ≤ k+i),
    List.length_ofFn,Nat.add_sub_cancel_left]

/-- Every physical wire address in the interpreter's stack agrees with the
repeated field-box bank. The supplied suffix remains present verbatim. -/
theorem lookup_guessed {copies : ℕ} (a : Fin copies → N.Assignment) (y : Fin copies → Ports bits) (tail : List Bool) :
    CellSparse.lookup (List.ofFn (guessedEquiv N copies (a,y)) ++ tail) = Copies.bank N a y (CellSparse.lookup tail) := by
  funext j
  by_cases h : j < Copies.width N copies
  · let i : Fin (Copies.width N copies) := ⟨j,h⟩
    rw [lookupPrefix (guessedEquiv N copies (a,y)) tail i]
    simp only [Copies.bank,dite_eq_left h,FieldDirectory.bank,Fin.eta]
    rw [dite_eq_left ((finProdFinEquiv.symm (⟨j,h⟩ : Fin (copies*Fintype.card (Wire N)))).2.isLt)]
    rfl
  · obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    rw [lookupSuffix,Copies.bank,dite_eq_right (by omega),Nat.add_sub_cancel_left]

private theorem guessed_read {copies : ℕ} (a : Fin copies → N.Assignment) (y : Fin copies → Ports bits)
    (tail : List Bool) (i : Fin copies) (j : Fin (Fintype.card (Supplied bits))) :
    CellSparse.lookup (List.ofFn (guessedEquiv N copies (a,y)) ++ tail) ((guessedPort N).atBit i.val j.val) =
      let p := (Fintype.equivFin (Supplied bits)).symm j
      y i p.1 p.2 := by
  let p := (Fintype.equivFin (Supplied bits)).symm j
  have pos : (guessedPort N).atBit i.val j.val = (index N i (.inr p)).val := by
    simp [guessedPort,CellSparse.Port.atBit,index,number_external,p,Nat.add_comm,Nat.mul_comm]; omega
  rw [pos,lookupPrefix]
  simp [guessedEquiv,index,p]

private theorem delivered_read {copies w : ℕ} (g : Fin (Copies.width N copies) → Bool)
    (x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool)
    (i : Fin copies) (j : Fin (Fintype.card (Supplied bits))) :
    CellSparse.lookup (List.ofFn g ++ external x c) ((deliveredPort N copies).atBit i.val j.val) =
      let p := (Fintype.equivFin (Supplied bits)).symm j
      x i p.1 p.2 := by
  have pos : (deliveredPort N copies).atBit i.val j.val = Copies.width N copies + (finProdFinEquiv (i,j)).val := by
    simp [deliveredPort,CellSparse.Port.atBit,Nat.add_comm,Nat.mul_comm]; omega
  rw [pos,lookupSuffix,external,publicBits,lookupPrefix]
  let read := fun (u : Fin copies × Fin (Fintype.card (Supplied bits))) =>
    let p := (Fintype.equivFin (Supplied bits)).symm u.2
    x u.1 p.1 p.2
  exact congrArg read (finProdFinEquiv.symm_apply_apply (i,j))

/-- The one repeated public record admits precisely the guessed exterior
bits supplied on this actual external literal stack. -/
theorem ties_iff {copies w : ℕ} (a : Fin copies → N.Assignment) (y x : Fin copies → Ports bits)
    (c : Fin (Fintype.card F) → Fin w → Bool) :
    equalValid (CellSparse.lookup (List.ofFn (guessedEquiv N copies (a,y)) ++ external x c))
      copies (Fintype.card (Supplied bits)) (guessedPort N) (deliveredPort N copies) ↔ y = x := by
  constructor
  · intro h
    funext i p k
    let j := Fintype.equivFin (Supplied bits) ⟨p,k⟩
    have hj := h i.val i.isLt j.val j.isLt
    rw [guessed_read N a y _ i j,delivered_read N _ x c i j] at hj
    let ly := fun s : Supplied bits => y i s.1 s.2
    let lx := fun s : Supplied bits => x i s.1 s.2
    have he := (Fintype.equivFin (Supplied bits)).symm_apply_apply ⟨p,k⟩
    exact (congrArg ly he).symm.trans (hj.trans (congrArg lx he))
  · rintro rfl i hi j hj
    exact (guessed_read N a y _ ⟨i,hi⟩ ⟨j,hj⟩).trans (delivered_read N _ y c ⟨i,hi⟩ ⟨j,hj⟩).symm

/-- For every interior assignment there is exactly one aligned full guess
prefix, and every aligned prefix decodes to exactly one interior assignment. -/
noncomputable def alignedEquiv {copies w : ℕ} (x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) :
    (Fin copies → N.Assignment) ≃ {g : Fin (Copies.width N copies) → Bool //
      equalValid (CellSparse.lookup (List.ofFn g ++ external x c)) copies (Fintype.card (Supplied bits))
        (guessedPort N) (deliveredPort N copies)} where
  toFun a := ⟨guessedEquiv N copies (a,x),(ties_iff N a x x c).mpr rfl⟩
  invFun g := ((guessedEquiv N copies).symm g.val).1
  left_inv := by intro a; simp
  right_inv := by
    rintro ⟨g,hg⟩
    obtain ⟨⟨a,y⟩,rfl⟩ := (guessedEquiv N copies).surjective g
    have hy := (ties_iff N a y x c).mp hg
    subst y
    apply Subtype.ext
    simp

/-- The shifted joint-report address reads exactly its bit in the suffix of the
actual interpreter stack and in the original repeated-box validator. -/
theorem report_read {copies w : ℕ} (g : Fin (Copies.width N copies) → Bool) (x : Fin copies → Ports bits)
    (c : Fin (Fintype.card F) → Fin w → Bool) (v : Fin (Fintype.card F)) (i : Fin w) :
    lookup (List.ofFn g ++ external x c) (copies*Fintype.card (Supplied bits)+Copies.claimAddress N copies w v i) =
      c v i := by
  have h : copies*Fintype.card (Supplied bits)+Copies.claimAddress N copies w v i =
    Copies.width N copies + (copies*Fintype.card (Supplied bits)+(finProdFinEquiv (i,v)).val) := by
    unfold Copies.claimAddress; omega
  rw [h,lookupSuffix,external,publicBits,lookupSuffix,reportBits_eq]
  simp only [lookup,List.head?_drop,List.getElem?_ofFn,dite_eq_left (finProdFinEquiv (i,v)).isLt,
    Fin.eta,Option.getD_some]
  exact congrArg (fun z : Fin w × Fin (Fintype.card F) => c z.2 z.1) (finProdFinEquiv.symm_apply_apply (i,v))

private theorem wordShift (b old : ℕ → Bool) (shift : ℕ) (as : List ℕ)
    (h : ∀ i ∈ as, b (shift+i) = old i) :
    word b (as.map (shift+·)) = word old as := by
  induction as with
  | nil => rfl
  | cons i is ih =>
    rw [List.map_cons,word,word,h i List.mem_cons_self,ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

open private bank_claim from OAI.Computability.BorderVNP.FiniteCellCopiesScan

/-- The literal field-directory entry of an aligned guessed prefix is exactly
the original repeated-box entry. Every prefix with a false exterior guess
contributes zero, even if its guessed field counts happen to pass. -/
theorem directory_weight {copies w : ℕ} (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (y x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) :
    (directory N sites table copies w).weight
        (lookup (List.ofFn (guessedEquiv N copies (a,y)) ++ external x c)) =
      if y = x then (Copies.directory N sites table copies w).weight (Copies.bank N a x (Copies.claimBits w c)) else 0 := by
  let b := lookup (List.ofFn (guessedEquiv N copies (a,y)) ++ external x c)
  let old := Copies.bank N a y (Copies.claimBits w c)
  let B := Copies.directory N sites table copies w
  let D := directory N sites table copies w
  let obs := (Copies.ids N sites table a y).map fun j => (false,some j)
  have hd : D.observations b = some obs := by
    change B.observations b = some obs
    dsimp only [b]
    rw [lookup_guessed]
    apply Copies.observations
  have ho : B.observations old = some obs := Copies.observations N sites table w a y (Copies.claimBits w c)
  have hguard : ((∀ r ∈ D.records, r.Valid D.boxes b) ↔ y = x) := by
    simpa [D,directory,Copies.directory,Record.Valid] using (ties_iff N a y x c)
  have recOld : ∀ r ∈ B.records, r.Valid B.boxes old := by simp [B,Copies.directory,Record.Valid]
  have hw (row : List ℕ) (hr : row ∈ B.reportedCounts) :
      word b (row.map (copies*Fintype.card (Supplied bits)+·)) = word old row := by
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hr
    apply wordShift
    intro j hj
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
    exact (report_read N _ x c v i).trans (bank_claim N a y c v i).symm
  have counts : (countsValid b D.reportedCounts obs ↔ countsValid old B.reportedCounts obs) := by
    change countsValid b (B.reportedCounts.map (List.map (copies*Fintype.card (Supplied bits)+·))) obs ↔ _
    constructor
    · rintro ⟨hr,hc⟩
      refine ⟨by simpa using hr,fun i => ?_⟩
      have hi := hc ⟨i.val,by simp⟩
      simpa only [Fin.getElem_fin,List.getElem_map,hw _ (List.getElem_mem _)] using hi
    · rintro ⟨hr,hc⟩
      refine ⟨by simpa using hr,fun i => ?_⟩
      have hi := hc ⟨i.val,by simpa using i.isLt⟩
      simpa only [Fin.getElem_fin,List.getElem_map,hw _ (List.getElem_mem _)] using hi
  by_cases hy : y = x
  · subst y
    change D.weight b = if x = x then B.weight old else 0
    have hg : ((∀ r ∈ D.records, r.Valid D.boxes b) ∧ countsValid b D.reportedCounts obs) ↔
      ((∀ r ∈ B.records, r.Valid B.boxes old) ∧ countsValid old B.reportedCounts obs) :=
      ⟨fun h => ⟨recOld,counts.mp h.2⟩,fun h => ⟨hguard.mpr rfl,counts.mpr h.2⟩⟩
    simp only [ite_true,Directory.weight,hd,ho,hg]
  · change D.weight b = if y = x then _ else 0
    have bad : ¬((∀ r ∈ D.records, r.Valid D.boxes b) ∧ countsValid b D.reportedCounts obs) := fun h => hy (hguard.mp h.1)
    simp only [ite_eq_right hy,Directory.weight,hd,ite_eq_right bad]

/-- Conditioning on the true interior and guessed boundary before summing
residual native checker tapes gives the guarded repeated-box entry. -/
theorem residual_sum {copies w : ℕ} (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (y x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) :
    (∑ p ∈ Compact.assignmentTails (directory N sites table copies w) [] (List.ofFn (guessedEquiv N copies (a,y)))
      (external x c), TeamTape.haltWeight true p.2) =
      if y = x then (Copies.directory N sites table copies w).weight (Copies.bank N a x (Copies.claimBits w c)) else 0 :=
  (Compact.assignmentTails_sum ..).trans (directory_weight ..)

end FiniteDiagonal.CellTrace.Copied

end BorderVNP
end Computability
end OAI
