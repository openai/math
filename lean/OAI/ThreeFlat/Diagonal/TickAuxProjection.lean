import OAI.ThreeFlat.Diagonal.TickAuxiliary

namespace OAI
/-! # Exact physical auxiliary coordinates for the switched chronological scan -/

namespace ThreeFlat.Diagonal.TickAuxiliary

open TickChronology
variable {a : ℕ}

structure Fields (L : Layout a) where
  marker : Bool
  history : Fin (L.wiresEnd-1) → Bool
  pairs : Fin (L.pairsEnd-L.wiresEnd) → Bool
  padding : Fin (a-L.pairsEnd) → Bool

def markerAt (L : Layout a) : Fin a := ⟨0,L.marker.trans_le (L.ordered.trans L.fits)⟩

def historyAt (L : Layout a) (i : Fin (L.wiresEnd-1)) : Fin a :=
  ⟨1+i.val,by have := L.ordered.trans L.fits; have := i.isLt; omega⟩

def pairAt (L : Layout a) (i : Fin (L.pairsEnd-L.wiresEnd)) : Fin a :=
  ⟨L.wiresEnd+i.val,by have := L.fits; have := i.isLt; omega⟩

def paddingAt (L : Layout a) (i : Fin (a-L.pairsEnd)) : Fin a :=
  ⟨L.pairsEnd+i.val,by have := i.isLt; omega⟩

def project (L : Layout a) (v : Fin a → Bool) : Fields L :=
  ⟨v (markerAt L),fun j => v (historyAt L j),fun j => v (pairAt L j),fun j => v (paddingAt L j)⟩

def pack (L : Layout a) (x : Fields L) (i : Fin a) : Bool :=
  if hz : i.val = 0 then x.marker else if hh : i.val < L.wiresEnd then
    x.history ⟨i.val-1,by omega⟩
  else if hp : i.val < L.pairsEnd then x.pairs ⟨i.val-L.wiresEnd,by omega⟩
  else x.padding ⟨i.val-L.pairsEnd,by have := i.isLt; omega⟩

@[simp] theorem pack_project (L : Layout a) (v : Fin a → Bool) : pack L (project L v) = v := by
  funext i
  unfold pack
  split_ifs <;> apply congrArg v <;> apply Fin.ext <;>
    dsimp only [markerAt,historyAt,pairAt,paddingAt] <;> omega

@[simp] theorem project_pack (L : Layout a) (x : Fields L) : project L (pack L x) = x := by
  have hm := L.marker
  have ho := L.ordered
  have hf := L.fits
  cases x with
  | mk z h q b =>
    change Fields.mk _ _ _ _ = Fields.mk _ _ _ _
    congr 1
    · funext i
      have hi := i.isLt
      dsimp [project,pack,historyAt]
      simp [show 1+i.val < L.wiresEnd by omega]
    · funext i
      have hi := i.isLt
      dsimp [project,pack,pairAt]
      simp [show L.wiresEnd ≠ 0 by omega,show ¬L.wiresEnd+i.val < L.wiresEnd by omega,
        show L.wiresEnd+i.val < L.pairsEnd by omega]
    · funext i
      have hi := i.isLt
      dsimp [project,pack,paddingAt]
      simp [show L.pairsEnd ≠ 0 by omega,show ¬L.pairsEnd+i.val < L.wiresEnd by omega,
        show ¬L.pairsEnd+i.val < L.pairsEnd by omega]

/-- Coordinate changes have multiplicity one, including empty pair fields and
zero-length padding. -/
def auxEquiv (L : Layout a) : (Fin a → Bool) ≃ Fields L :=
  ⟨project L,pack L,pack_project L,project_pack L⟩

def activeFields (L : Layout a) (ph : Phase) (x y : Fields L) : Prop :=
  (markerRule ph).holds x.marker y.marker ∧
  (∀ j, (historyRule ph).holds (x.history j) (y.history j)) ∧
  (∀ j, (pairRule ph).holds (x.pairs j) (y.pairs j)) ∧
  (∀ j, x.padding j = false ∧ y.padding j = false)

theorem accepts_iff_fields (L : Layout a) (ph : Phase) (old new : Fin a → Bool) :
    L.accepts ph true old new ↔ activeFields L ph (project L old) (project L new) := by
  have hm := L.marker
  have ho := L.ordered
  have hf := L.fits
  rw [split_run]
  constructor
  · rintro ⟨z,h,q,b⟩
    refine ⟨z (markerAt L) rfl,?_,?_,?_⟩
    · intro i
      have hi := i.isLt
      exact h (historyAt L i) (by simp [historyAt]) (by dsimp [historyAt]; omega)
    · intro i
      have hi := i.isLt
      exact q (pairAt L i) (by simp [pairAt]) (by dsimp [pairAt]; omega)
    · exact fun i => b (paddingAt L i) (by simp [paddingAt])
  · rintro ⟨z,h,q,b⟩
    refine ⟨?_,?_,?_,?_⟩
    · rintro i iz
      have eq : markerAt L = i := Fin.ext iz.symm
      simpa only [project,eq] using z
    · intro i nonzero before
      let j : Fin (L.wiresEnd-1) := ⟨i.val-1,by omega⟩
      have eq : historyAt L j = i := Fin.ext (by dsimp [j,historyAt]; omega)
      simpa only [project,eq] using h j
    · intro i after before
      let j : Fin (L.pairsEnd-L.wiresEnd) := ⟨i.val-L.wiresEnd,by omega⟩
      have eq : pairAt L j = i := Fin.ext (by dsimp [j,pairAt]; omega)
      simpa only [project,eq] using q j
    · intro i after
      let j : Fin (a-L.pairsEnd) := ⟨i.val-L.pairsEnd,by have := i.isLt; omega⟩
      have eq : paddingAt L j = i := Fin.ext (by dsimp [j,paddingAt]; omega)
      simpa only [project,eq] using b j

/-- Proposed pair bits are arbitrary on the group opening, fixed during
the scan and evaluation, and forgotten by the group clear. -/
def phaseFields (L : Layout a) (ph : Phase) (x y : Fields L) : Prop :=
  (x.padding = fun _ => false) ∧ (y.padding = fun _ => false) ∧
  match ph with
  | .opening => x.marker = false ∧ y.marker = true ∧ x.history = (fun _ => false) ∧
      x.pairs = (fun _ => false) ∧ y.pairs = (fun _ => false)
  | .closing => x.marker = true ∧ y.marker = false ∧ y.history = (fun _ => false) ∧
      x.pairs = (fun _ => false) ∧ y.pairs = (fun _ => false)
  | .propose => x.marker = true ∧ y.marker = true ∧ x.history = y.history ∧ x.pairs = (fun _ => false)
  | .clear => x.marker = true ∧ y.marker = true ∧ x.history = y.history ∧ y.pairs = (fun _ => false)
  | _ => x.marker = true ∧ y.marker = true ∧ x.history = y.history ∧ x.pairs = y.pairs

theorem accepts_phase (L : Layout a) (ph : Phase) (old new : Fin a → Bool) :
    L.accepts ph true old new ↔ phaseFields L ph (project L old) (project L new) := by
  rw [accepts_iff_fields]
  cases ph <;> simp only [activeFields,phaseFields,markerRule,historyRule,pairRule,Rule.holds,
    funext_iff, forall_and] <;> tauto

end ThreeFlat.Diagonal.TickAuxiliary

end OAI
