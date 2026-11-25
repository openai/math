import OAI.Computability.BorderVNP.PackedFinalReportTemplate
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryGateCost
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryKeys
import OAI.Computability.BorderVNP.DiagonalExternalSewFields

/-! # Real count fields and the skipped owner in the native history template

The physical address frame ranges over the real cells. The history sorter
also has one last, skipped owner for unused rows. That owner's private-size
word uses one shared false pin and its empty report list contributes one
encoded length word. Other public fields include the original slot offsets.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.FinalReports.Spare

open Crossing CellAddresses CellAddressViews CellAddressPhysical CellAddressCircuit ParseBatchSort
  VPVNP.VerifierNetwork CellPacketGeometry CellPacketGeometry.LiveWords CellPacketGeometry.SiteWords
  Inherited Inherited.FrozenTape CellSparse.Packet DiagonalTallyCellReports
open Diagonal.ExternalSew.FieldExport (constants constants_eval constants_size)
open private zero_value from OAI.Computability.BorderVNP.PackedWordCircuit
open scoped Classical

/-- Shared report pins, the spare's literal zero, and the independent public
fields used elsewhere by the chronological packet emitter. -/
abbrev Field (C g digits : ℕ) (E : Type) := Option (Pin C g digits) ⊕ E

variable {a s m n C g digits w : ℕ} {E I Orig : Type}

/-- Source of the true private-wire word for each owner of the history table. -/
def priv : Fin (C+1) → Field C g digits E :=
  Fin.lastCases (.inl none) (fun c => .inl (some (.inl c)))

/-- Real rows have the complete gadget-major field list. The skipped owner
has an empty report list, including when there are no real cells. -/
def reports : Fin (C+1) → List (List (Field C g digits E)) :=
  Fin.lastCases [] (fun c => (countPins c).map (List.map (fun p => .inl (some p))))

/-- Install the spare-aware public report metadata on the full history roster. -/
def install (T : Template E I Orig s (C+1)) (g digits : ℕ) : Template (Field C g digits E) I Orig s (C+1) where
  boxes := T.boxes
  format := T.format
  privateWires := priv
  reports := reports

/-- Select a report wire, the shared literal-zero wire, or an independent
public operand at its original bit position. -/
def fieldPin {σ : Type*} (live : (Pin C g digits ⊕ E) × Fin w → σ) (zero : σ) :
    Field C g digits E × Fin w → σ
  | (.inl none,_) => zero
  | (.inl (some p),j) => live (.inl p,j)
  | (.inr p,j) => live (.inr p,j)

variable {σ : Type*} [Fintype σ] [Fintype E]

/-- Actual word frame for all real cells, plus the single constant wire
used for every bit of the skipped cell's private size. -/
noncomputable def fields (base : Frame σ (View s m n C × Fin w)) (rest : Frame σ (E × Fin w)) :
    Frame σ (Field C g digits E × Fin w) :=
  ((constants _).subst (joinFields base rest)).select (fieldPin Sum.inl (.inr false))

/-- The optional field costs at most two shared constant gates in addition
to the real physical address frame and the independent public operand frame. -/
theorem fields_size (base : Frame σ (View s m n C × Fin w)) (rest : Frame σ (E × Fin w)) :
    (fields (g := g) (digits := digits) base rest).size ≤
      base.size+(C+C*g*digits)*w*(100*(w+1))+rest.size+2 := by
  rw [fields,Frame.select_size,Frame.subst_size]
  have h := joinFields_size (g := g) (digits := digits) base rest
  have hc := constants_size ((Pin C g digits ⊕ E) × Fin w)
  omega

/-- Evaluation exposes the same physical report and public operands for
every real cell, and a genuine false Boolean at the spare. -/
theorem fields_eval (base : Frame σ (View s m n C × Fin w)) (rest : Frame σ (E × Fin w))
    (x : σ → Bool) (p : Field C g digits E) (j : Fin w) :
    (fields base rest).eval x (p,j) =
      p.elim (fun o => o.elim false (fun r => (FinalReports.frame base).eval x (r,j))) (fun z => rest.eval x (z,j)) := by
  rcases p with (_|r) | z <;>
    simp [fields,fieldPin,Frame.select_eval,Frame.subst_eval,constants_eval,joinFields]

variable {cap d t : ℕ} {R B U V : Type} (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
    (sh : ∀ r, (S.tags r).length ≤ cap) (lh : ∀ r, (L.tags r).length ≤ cap)
    (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)

omit [Fintype E] in
/-- Numeric directory fields at a real physical owner of the chronological
roster, after the stable site regrouping. -/
theorem directory_real (args : Field C g digits E → ℕ) (c : Fin C) :
    let D := History.directory S L boxes sh lh priv reports args x y cells off box
    D.privateWires c.castSucc = args (.inl (some (.inl c))) ∧
      D.reports c.castSucc = (countPins c).map (List.map (fun p => args (.inl (some p)))) := by
  simp only [History.directory,Directory.regroup,Template.directory,History.template,priv,reports,
    Fin.lastCases_castSucc,List.map_map,Function.comp_def,and_self]

omit [Fintype E] in
/-- The actual skipped directory entry reads the designated zero operand
and contains exactly the empty report list. -/
theorem directory_spare (args : Field C g digits E → ℕ) :
    let D := History.directory S L boxes sh lh priv reports args x y cells off box
    D.privateWires (Fin.last C) = args (.inl none) ∧ D.reports (Fin.last C) = [] := by
  simp only [History.directory,Directory.regroup,Template.directory,History.template,priv,reports,
    Fin.lastCases_last,List.map_nil,and_self]

omit [Fintype E] in
/-- Each real native packet has one count-list prefix and the fixed
row length and digit addresses of each gadget field. -/
theorem reportWordCount_real (c : Fin C) :
    (History.template S L boxes sh lh (priv (g := g) (digits := digits) (E := E)) reports).reportWordCount c.castSucc =
      1+g*(1+digits) := by
  change 1+((reports (g := g) (digits := digits) (E := E) c.castSucc).map (fun r => 1+r.length)).sum = _
  simp [reports,countPins,List.map_ofFn,Function.comp_def]

omit [Fintype E] in
/-- The skipped native packet still encodes the zero length of its empty
count-list directory. -/
theorem reportWordCount_spare :
    (History.template S L boxes sh lh (priv (C := C) (g := g) (digits := digits) (E := E)) reports).reportWordCount
      (Fin.last C) = 1 := by
  change 1+((reports (g := g) (digits := digits) (E := E) (Fin.last C)).map (fun r => 1+r.length)).sum = _
  simp [reports]

omit [Fintype E] in
/-- Total report words, with each actual row prefix, every real cell prefix,
and the one empty skipped-cell prefix. -/
theorem reportWords_sum :
    (∑ c : Fin (C+1), (1+((reports (g := g) (digits := digits) (E := E) c).map (fun r => 1+r.length)).sum)) =
      C*(1+g*(1+digits))+1 := by
  rw [Fin.sum_univ_castSucc]
  simp [reports,countPins,List.map_ofFn,Function.comp_def]

/-- Exact static source volume for the full native template, including the
extra operand and the skipped owner's one report word. -/
theorem sourceVolume_eq :
    History.sourceVolume S L boxes (reports (C := C) (g := g) (digits := digits) (E := E)) =
      1+a+C+S.rows.length+History.tagWords S+L.rows.length+History.tagWords L+
      (C+C*g*digits+1+Fintype.card E)+(∑ i, (boxes i).length)+
      (∑ i, (CellPacketGeometry.SiteWords.boxWords (boxes i)).length)+(C*(1+g*(1+digits))+1) := by
  rw [History.sourceVolume,reportWords_sum]
  simp only [Field,Pin,Fintype.card_sum,Fintype.card_option,Fintype.card_prod,Fintype.card_fin]
  ring

variable {D d₀ k : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  (cell : N.Site → Fin C) (state : N.Site → Site)
  (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
  (F : Fields s m n C d₀ k w σ) (z : σ → Bool) (h : Represents N cell (fun v => (state v).size) siteID edgeID portID F z)
  (fit : ∀ c, guessedSize N cell c + siteSize N cell c (fun v => (state v).size) + suppliedSize N cell c < 2^w)
  (rest : Frame σ (E × Fin w))
local notation3 "args₀" => fun p => value fun j => (fields (g := g) (digits := digits) (CellAddressViews.frame F) rest).eval z (p,j)

include h fit in
/-- The real owners of the native history directory contain the physical
private-bit size and canonical report addresses computed from the terminal network. -/
theorem emitted_real (c : Fin C)
    (room : guessedSize N cell c + siteSize N cell c (fun v => (state v).size) + suppliedSize N cell c + g*digits ≤ 2^w) :
    let G := History.directory S L boxes sh lh priv reports args₀ x y cells off box
    G.privateWires c.castSucc = FinalCell.privateBits N (fun v => (cell v).val) state c.val ∧
      G.reports c.castSucc = countFields (FinalCell.countBase N (fun v => (cell v).val) state c.val) g digits := by
  obtain ⟨hp,hr⟩ := directory_real S L boxes sh lh x y cells off box args₀ c
  obtain ⟨h₁,h₂,h₃⟩ := bank_sizes N cell state c
  dsimp only
  rw [hp,hr]
  simp only [fields_eval,Sum.elim_inl,Option.elim_some,FinalCell.privateBits,FinalCell.countBase,h₁,h₂,h₃]
  exact ⟨private_value N cell _ siteID edgeID portID F h fit c,
    countPins_value N cell _ siteID edgeID portID F h fit c room⟩

include h in
/-- The measured terminal tile load and external report length supply
the required word capacity for a real owner. -/
theorem emitted_real_of_load (c : Fin C) (M E₀ : ℕ)
    (hin : ∀ v, (state v).incoming = incoming N v)
    (hexp : ∀ u : Fin C, Shortening.localRecords N true (fun v => (state v).staticNodes)
      (fun v => (state v).expandedLoad) (fun v => cell v=u) ≤ M)
    (hext : suppliedSize N cell c + g*digits ≤ E₀) (width : 3*M+E₀ < 2^w) :
    let G := History.directory S L boxes sh lh priv reports args₀ x y cells off box
    G.privateWires c.castSucc = FinalCell.privateBits N (fun v => (cell v).val) state c.val ∧
      G.reports c.castSucc = countFields (FinalCell.countBase N (fun v => (cell v).val) state c.val) g digits := by
  have cap (u : Fin C) := (merged_bank_capacity N state cell u hin).trans (Nat.mul_le_mul_left 3 (hexp u))
  apply emitted_real S L boxes sh lh x y cells off box N cell state siteID edgeID portID F z h
    (fun u => (cap u).trans_lt (by omega)) rest c
  have hp := (Nat.le_add_right _ (suppliedSize N cell c)).trans (cap c)
  omega

/-- The spare entry of this actual Boolean frame emits numerical zero even
at width zero and never emits a subtotal field. -/
theorem emitted_spare (base : Frame σ (View s m n C × Fin w)) (z : σ → Bool) :
    let args := fun p => value fun j => (fields (g := g) (digits := digits) base rest).eval z (p,j)
    let G := History.directory S L boxes sh lh priv reports args x y cells off box
    G.privateWires (Fin.last C) = 0 ∧ G.reports (Fin.last C) = [] := by
  intro args G
  obtain ⟨hp,hr⟩ := directory_spare S L boxes sh lh x y cells off box args
  refine ⟨hp.trans ?_,hr⟩
  simpa only [args,fields_eval,Sum.elim_inl,Option.elim_none] using zero_value w

end Packing.FinalReports.Spare

namespace CellPacketGeometry.History.Native

open Packing.FinalReports

/-- Route the single additional emitter operand to the already shared zero
pin of the native access frame. -/
def Access.withSpareReports {a d t k w C g digits : ℕ} {R B U V E σ : Type}
    (A : Access R B U V (Pin C g digits ⊕ E) σ a d t k w) :
    Access R B U V (Spare.Field C g digits E) σ a d t k w where
  history := A.history
  binding := A.binding
  table := A.table
  field := Spare.fieldPin A.field A.zero
  valid := A.valid
  zero := A.zero

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
