import OAI.ThreeFlat.Diagonal.TickGroupRegister

namespace OAI
/-! # Exact phase transitions between canonical group boundary and working states -/

noncomputable section
namespace ThreeFlat.Diagonal.TickAuxiliary.GroupRegister

open TickChronology HistoryContraction
variable {F : Type*} [CommSemiring F] {S : Shape} {P : Plan F S} {E : P.Codes}
    {bits : P.History → ℕ} {a n : ℕ} (R : GroupRegister P E bits a) (fit : 1+R.capacity+2*n ≤ a)

private theorem fields_eq {L : Layout a} {x y : Fields L}
    (z : x.marker=y.marker) (h : x.history=y.history) (p : x.pairs=y.pairs)
    (b : x.padding=y.padding) : x=y := by
  cases x; cases y; simp_all

theorem opening_iff (v : Plan.Terminal P bits) (dest : Fin a → Bool) :
    (R.layout n fit).accepts .opening true (fun _ => false) dest ∧
      decode P E bits R.base dest = some v ↔ dest=R.ready v := by
  rw [R.ready_boundary fit]
  exact opening P E bits (R.layout n fit) (R.room_layout fit)

theorem propose_iff (v : Plan.Terminal P bits) (dest : Fin a → Bool) :
    (R.layout n fit).accepts .propose true (R.ready v) dest ↔
      ∃ p r : Fin n → Bool, dest = R.work fit v p r := by
  rw [accepts_phase,R.ready_fields]
  constructor
  · rintro ⟨_,pad,_,marker,hist,_⟩
    obtain ⟨p,r,words⟩ := R.pairWords_surjective fit (project (R.layout n fit) dest).pairs
    refine ⟨p,r,(auxEquiv (R.layout n fit)).injective ?_⟩
    change project (R.layout n fit) dest = project (R.layout n fit) (R.work fit v p r)
    rw [R.work_fields]
    exact fields_eq marker hist.symm words.symm pad
  · rintro ⟨p,r,rfl⟩
    rw [R.work_fields]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem clear_iff (v : Plan.Terminal P bits) (p r : Fin n → Bool) (dest : Fin a → Bool) :
    (R.layout n fit).accepts .clear true (R.work fit v p r) dest ↔ dest=R.ready v := by
  rw [accepts_phase,R.work_fields]
  constructor
  · rintro ⟨_,pad,_,marker,hist,pairs⟩
    apply (auxEquiv (R.layout n fit)).injective
    change project (R.layout n fit) dest = project (R.layout n fit) (R.ready v)
    rw [R.ready_fields]
    exact fields_eq marker hist.symm pairs pad
  · rintro rfl
    rw [R.ready_fields]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem preserve_iff (L : Layout a) (ph : Phase) (kind : ph=.scan ∨ ph=.evaluate ∨ ph=.idle)
    (old dest : Fin a → Bool) (mark : (project L old).marker=true)
    (padding : (project L old).padding = fun _ => false) :
    L.accepts ph true old dest ↔ dest=old := by
  have eq (x y : Fields L) : phaseFields L ph x y ↔
      x.padding=(fun _ => false) ∧ y.padding=(fun _ => false) ∧ x.marker=true ∧
      y.marker=true ∧ x.history=y.history ∧ x.pairs=y.pairs := by
    rcases kind with rfl|rfl|rfl <;> rfl
  rw [accepts_phase,eq]
  constructor
  · rintro ⟨_,pad,_,z,h,p⟩
    exact (auxEquiv L).injective (fields_eq (z.trans mark.symm) h.symm p.symm (pad.trans padding.symm))
  · rintro rfl
    exact ⟨padding,padding,mark,mark,rfl,rfl⟩

theorem preserve_work_iff (ph : Phase) (kind : ph=.scan ∨ ph=.evaluate ∨ ph=.idle)
    (v : Plan.Terminal P bits) (p r : Fin n → Bool) (dest : Fin a → Bool) :
    (R.layout n fit).accepts ph true (R.work fit v p r) dest ↔ dest=R.work fit v p r :=
  preserve_iff _ _ kind _ _ (by rw [R.work_fields]) (by rw [R.work_fields])

theorem idle_ready_iff (v : Plan.Terminal P bits) (dest : Fin a → Bool) :
    (R.layout n fit).accepts .idle true (R.ready v) dest ↔ dest=R.ready v :=
  preserve_iff _ _ (Or.inr (Or.inr rfl)) _ _ (by rw [R.ready_fields]) (by rw [R.ready_fields])

theorem closing_iff (v : Plan.Terminal P bits) (dest : Fin a → Bool) :
    (R.layout n fit).accepts .closing true (R.ready v) dest ↔ dest=(fun _ => false) := by
  rw [accepts_phase,R.ready_fields]
  constructor
  · rintro ⟨_,pad,_,marker,hist,_,pairs⟩
    exact (auxEquiv (R.layout n fit)).injective (fields_eq marker hist pairs pad)
  · rintro rfl
    simp [phaseFields,project]

end ThreeFlat.Diagonal.TickAuxiliary.GroupRegister

end
end OAI
