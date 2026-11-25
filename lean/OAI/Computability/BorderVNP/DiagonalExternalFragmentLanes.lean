import OAI.Computability.BorderVNP.DiagonalExternalFreeCell
import OAI.Computability.BorderVNP.DiagonalExternalFragmentCandidates

/-! # Bit positions of live fragment rows in the final supplied bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.Directory Packing.CellAddresses
open scoped Classical

variable {R r w link V g entries desc : ℕ}

/-- Final cell and supplied-bank displacement of a lane of the original grouped word. -/
def laneAddress (lp : ℕ → ℕ × ℕ) (a : Σ _ : FreeBlock R V, Fin g) : ℕ × ℕ :=
  let place := lp (a.1.1.val*V+a.1.2.val)
  (place.1,place.2+a.2.val)

/-- Every bit in a positive live row is the placed lane of the original processor
and field that the row names. The field bit is exactly the source offset plus the
position within the emitted slice. -/
theorem live_row_lane (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (lp : ℕ → ℕ × ℕ) (t : Fin (R+1)) (p : Fin r) (f : Fin 2) (k : ℕ)
    (off : Fin ((freeDirectory R r w link V g entries desc).liveRow lp t p f k).width) :
    let row := (freeDirectory R r w link V g entries desc).liveRow lp t p f k
    ∃ j : Fin w, row.offset+off.val = j.val ∧
      (row.cell,row.slot+off.val) = laneAddress lp (freeLane hg room (fromField t p f j)) := by
  intro row
  let start := p.val*(2*w+R*link)+f.val*(w+R*link)
  let sl := slice start w g k
  let pos := sl.1+off.val
  let d := freeDirectory R r w link V g entries desc
  have hstart : p.val*d.stride + f.val*(d.literal+(d.teams-1)*d.link) = start := by
    simp [d,start,freeDirectory,Layout.stride]
  have hwidth : row.width = sl.2 := by
    change (slice _ w g k).2 = sl.2
    rw [hstart]
  have hl := (mem_slice_iff start w g k pos).mp
    ⟨Nat.le_add_right ..,Nat.add_lt_add_left (off.isLt.trans_eq hwidth) _⟩
  let j : Fin w := ⟨pos-start,by omega⟩
  have hj : freeFieldOrdinal p f j R link = pos := by
    change start+(pos-start) = pos
    exact Nat.add_sub_of_le hl.1
  have hdiv : pos/g = start/g+k :=
    (Nat.div_eq_iff hg).mpr ⟨hl.2.2.1,by have := hl.2.2.2; omega⟩
  have ha := freeLane_field hg room t p f j
  let a := freeLane hg room (fromField t p f j)
  change a.1.1 = t ∧ a.1.2.val = freeFieldOrdinal p f j R link/g ∧
    a.2.val = freeFieldOrdinal p f j R link%g at ha
  rw [hj,hdiv] at ha
  have hmod := Nat.div_add_mod' pos g
  rw [hdiv] at hmod
  have hleft : start ≤ sl.1 := le_max_left ..
  have hblock : (start/g+k)*g ≤ sl.1 := le_max_right ..
  refine ⟨j,?_,?_⟩
  · change (slice _ w g k).1-_+off.val = pos-start
    rw [hstart]
    change sl.1-start+off.val = pos-start
    dsimp only [pos]
    omega
  · change ((lp (t.val*V+(_/g+k))).1,(lp (t.val*V+(_/g+k))).2 +
      ((slice _ w g k).1-(_/g+k)*g) + off.val) =
      ((lp (a.1.1.val*V+a.1.2.val)).1,(lp (a.1.1.val*V+a.1.2.val)).2+a.2.val)
    rw [hstart,ha.1,ha.2.1,ha.2.2]
    change (_, _ + (sl.1-(start/g+k)*g) + off.val) = (_, _ + pos%g)
    congr 1
    dsimp only [pos] at hmod ⊢
    omega

variable {D C m n : ℕ} (N : Network D (FreeBlock R V) (fun _ => g)) (cell : N.Site → Fin C)
    (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin n)

/-- The whole grouped word fits before the end of the actual compact supplied bank. -/
theorem live_base_fits {lp : ℕ → ℕ × ℕ} (place : LivePlacement N cell edgeID portID lp)
    (supplied : ℕ → ℕ) (counts : ∀ c : Fin C, supplied c.val = suppliedSize N cell c) (a : FreeBlock R V) :
    let dest := lp (a.1.val*V+a.2.val)
    dest.2+g ≤ supplied dest.1 := by
  intro dest
  have h := place a
  let c := cell (N.attach a)
  change lp _ = (c.val,_) at h
  change (lp _).2+g ≤ supplied (lp _).1
  rw [h,counts]
  apply (CellSlabs.end_le_capacity (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c) (.inr ⟨a,rfl⟩)).trans_eq
  exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)

/-- Distinct original team/site/lane indices stay distinct in the compact
supplied bank, including co-located words from different teams. -/
theorem laneAddress_injective {lp : ℕ → ℕ × ℕ} (place : LivePlacement N cell edgeID portID lp) :
    Function.Injective (laneAddress (R := R) (V := V) (g := g) lp) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  change ((lp (a.1.val*V+a.2.val)).1,(lp (a.1.val*V+a.2.val)).2+i.val) =
    ((lp (b.1.val*V+b.2.val)).1,(lp (b.1.val*V+b.2.val)).2+j.val) at h
  have placed (p : FreeBlock R V) (c : Fin C) (hc : cell (N.attach p) = c) :
      lp (p.1.val*V+p.2.val) = (c.val,CellSlabs.start (suppliedRow N cell c edgeID portID)
        (suppliedWidth N cell c) (.inr ⟨p,hc⟩)) := by
    subst c
    exact place p
  have hh := congrArg Prod.fst h
  rw [place a,place b] at hh
  let c := cell (N.attach a)
  have hc : cell (N.attach b) = c := (Fin.ext hh).symm
  let x : Supplied N cell c := .inr ⟨a,rfl⟩
  let y : Supplied N cell c := .inr ⟨b,hc⟩
  rw [placed a c rfl,placed b c hc] at h
  have hoff := congrArg Prod.snd h
  let ord := CellSlabs.ordinal (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c)
  have eq : ord ⟨x,i⟩ = ord ⟨y,j⟩ := Fin.ext hoff
  have same := ord.injective eq
  have hw := congrArg Sigma.fst same
  have hab : a = b := congrArg Subtype.val (Sum.inr.inj hw)
  have hij := congrArg (fun z : Σ u, Fin (suppliedWidth N cell c u) => z.2.val) same
  subst b
  exact congrArg (Sigma.mk a) (Fin.ext hij)

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
