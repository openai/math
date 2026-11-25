import OAI.Hierarchy.TaggedWideRowPrefixes
import OAI.Hierarchy.TaggedWideBondSum

namespace OAI
/-! # The joint positive and private endpoint assignment on every reported link -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open scoped Classical BigOperators
variable {T F : Type*} [Fintype T] [CommSemiring F] {n : T→ℕ}
    (groups γ : T→ℕ) (rows : ∀t,Fin (n t)→ProtocolRAMEmit.Row) (w m : ℕ)
    (unique : ∀t,Function.Injective (fun i=>(rows t i).link))

set_option quotPrecheck false in
local notation "row" => Occ groups γ rows w m
set_option quotPrecheck false in
local notation "bits" => fun r : row=>(rows r.1 r.2.2.val).width
set_option quotPrecheck false in
local notation "width" => fun r : row=>⌈dyadic (γ r.1)*w⌉₊
set_option quotPrecheck false in
local notation "units" => fun r : row=>pieces (rows r.1) w r.2.2.val

/-- Place the original row bits at the physical common IDs and subslot
positions. This is the voltage on the two ends after the shorter switches
identify them and the suffix guards have removed their high pins. -/
def expandedLabels (a : ((r : row) × Fin (bits r))→Bool) :
    Lanes groups γ rows w m :=
  (rowLanes groups γ rows w m unique).symm
    (allSlices bits width units (fun r j=>a ⟨r,j⟩))

theorem sum_reported_labels (hw : 0<w) (φ : Lanes groups γ rows w m→F) :
    (∑ z : Lanes groups γ rows w m,
      if ∀t e j,z t e j=true → originalPrefix groups γ rows w m unique t e j then φ z else 0) =
      ∑ a : ((r : row) × Fin (bits r))→Bool,φ (expandedLabels groups γ rows w m unique a) := by
  classical
  let ord := rowLanes groups γ rows w m unique
  let f := fun raw=>φ (ord.symm raw)
  let align := Equiv.piCurry (fun (r : row) (_ : Fin (bits r))=>Bool)
  let val := fun b=>f (allSlices bits width units b)
  calc
    _ = ∑ z,if highZeros bits width units (ord z) then f (ord z) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [originalPrefix_iff groups γ rows w m unique,f,Equiv.symm_apply_apply,ord]
    _ = ∑ a,val a := sum_row_words groups γ rows w m unique hw f
    _ = ∑ a,val (align a) := (align.sum_comp val).symm
    _ = _ := rfl

section
variable {N : ℕ} (key : T ↪ ℕ×ℕ) (raw : Fin N→ProtocolRAMEmit.Row)
    (positive : Fin N→Prop) (stage : Fin N→ℕ)
set_option quotPrecheck false in
local notation "reported" => fun t:T=>atScale positive stage (key t).1 raw
set_option quotPrecheck false in
local notation "ords" => Occ groups (fun t:T=>(key t).2) reported w m
set_option quotPrecheck false in
local notation "liveBits" => (r : ords) × Fin ((reported r.1 r.2.2.val).width)
set_option quotPrecheck false in
local notation "free" => {i : Fin N // ¬positive i}
set_option quotPrecheck false in
local notation "freeWidth" => fun e : free=>(raw e.val).width

/-- The labels left after closing all fixed positive cuts and both private
endpoints have precisely the original one-word-per-ordinal finite sum.
The scalar may depend jointly on all endpoint bits and any site data. -/
theorem reported_bonds (hw : 0<w)
    (unique : ∀t,Function.Injective fun i=>(reported t i).link)
    (capacity : free→ℕ) (room : ∀i,freeWidth i≤capacity i)
    (cover : ∀ i,positive i → 0<(raw i).width →
      ∃t, key t=(stage i,widthIndex m ((raw i).width/(w:ℝ))) ∧ (raw i).group<groups t)
    (φ : Lanes groups (fun t=>(key t).2) reported w m → PrivatePorts capacity → F) :
    let γ := fun t:T=>(key t).2
    let labels := expandedLabels groups γ reported w m unique
    (∑ z : Lanes groups γ reported w m,
      if ∀t e j,z t e j=true → originalPrefix groups γ reported w m unique t e j then
        ∑ y : PrivatePorts capacity,
          (∏e,if ∀j : Fin (capacity e),j.val<freeWidth e → y false e j=y true e j then (1:F) else 0)*
          (if EndsPadded freeWidth capacity y then φ z y else 0) else 0) =
      ∑ a : (i:Fin N)→Fin (2^(raw i).width),
        φ (labels (fun p=>let q := edgeBit key groups raw positive stage w m p
                          (a q.1.val).val.testBit q.2.val))
          (privateEncode freeWidth capacity (fun e j=>(a e.val).val.testBit j.val)) := by
  intro γ labels
  rw [sum_reported_labels groups γ reported w m unique hw]
  exact terminal_bonds key groups raw positive stage w m capacity room cover (fun a y=>φ (labels a) y)
end

end Hierarchy.Tagged.WideStack

end
end OAI
