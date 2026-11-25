import OAI.Computability.BorderVNP.DiagonalExternalSewPorts
import OAI.Computability.BorderVNP.PackedDirectoryKeys

/-! # The real literal and pin fields as one public word per team and grid tile

The coordinate includes the gap occupied by the exterior fields. The sparse
delivery writer and the unchanged local factors use the same position inside
the site's input word. Unused positions may take arbitrary values.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Packing.Directory Function

variable {R r w link V g : ℕ}

/-- One surviving input word per team and original site, in team-major order. -/
abbrev FreeBlock (R V : ℕ) := Fin (R+1) × Fin V

/-- Original public row and slot within the team, including exterior fields. -/
def teamOrdinal (p : PublicPort R r w link) : Fin (r*(2*w+R*link)) := finProdFinEquiv p.2

/-- The numerical slot in a team's processor array. -/
theorem teamOrdinal_val (p : PublicPort R r w link) :
    (teamOrdinal p).val = p.2.1.val*(2*w+R*link)+p.2.2.val := by
  simp only [teamOrdinal,finProdFinEquiv_apply_val]
  ac_rfl

/-- Split a team's original processor ordinals at the grid site block boundaries. -/
def publicLane (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g) :
    PublicPort R r w link ↪ Σ _ : FreeBlock R V, Fin g where
  toFun p :=
    let a := (teamOrdinal p).val
    ⟨(p.1,⟨a/g,(Nat.div_lt_iff_lt_mul hg).mpr ((teamOrdinal p).isLt.trans_le room)⟩),
      ⟨a%g,Nat.mod_lt _ hg⟩⟩
  inj' := by
    intro p q h
    have ht := congrArg (fun a : Σ _ : FreeBlock R V, Fin g => a.1.1) h
    have hs := congrArg (fun a : Σ _ : FreeBlock R V, Fin g => a.1.2.val*g+a.2.val) h
    change (teamOrdinal p).val/g*g+(teamOrdinal p).val%g =
      (teamOrdinal q).val/g*g+(teamOrdinal q).val%g at hs
    simp only [Nat.div_add_mod'] at hs
    exact Prod.ext ht (finProdFinEquiv.injective (Fin.ext hs))

/-- The literal and pin slots alone are injected into the same padded site words. -/
def freeLane (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g) :
    FreePort R r w ↪ Σ _ : FreeBlock R V, Fin g :=
  (Embedding.inl.trans (publicPortEquiv R r w link).toEmbedding).trans (publicLane hg room)

/-- The literal and the additional pin field select the physical offsets used by
the native placement writer. -/
def freeFieldOrdinal (p : Fin r) (f : Fin 2) (j : Fin w) (R link : ℕ) :=
  p.val*(2*w+R*link)+f.val*(w+R*link)+j.val

/-- The free port selected by the placement writer's field index. -/
def fromField (t : Fin (R+1)) (p : Fin r) (f : Fin 2) (j : Fin w) : FreePort R r w :=
  (t,p,if f=0 then .inl j else .inr j)

/-- The actual ordinal has the original processor offset, even when its site
contains both exterior and free fields. -/
theorem fromField_ordinal (t : Fin (R+1)) (p : Fin r) (f : Fin 2) (j : Fin w) (link : ℕ) :
    (teamOrdinal (publicPortEquiv R r w link (.inl (fromField t p f j)))).val =
      freeFieldOrdinal p f j R link := by
  rw [teamOrdinal_val]
  fin_cases f <;> simp [fromField,freeFieldOrdinal,publicPortEquiv_literal,publicPortEquiv_pin,Nat.add_assoc]

/-- Team, site and lane of either field, in the stable row-major storage order. -/
theorem freeLane_field (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (t : Fin (R+1)) (p : Fin r) (f : Fin 2) (j : Fin w) :
    let a := freeLane hg room (fromField t p f j)
    a.1.1 = t ∧ a.1.2.val = freeFieldOrdinal p f j R link/g ∧ a.2.val = freeFieldOrdinal p f j R link%g := by
  refine ⟨?_,?_,?_⟩
  · change (publicPortEquiv R r w link (.inl (fromField t p f j))).1 = t
    fin_cases f <;> simp [fromField,publicPortEquiv_literal,publicPortEquiv_pin]
  · exact congrArg (· /g) (fromField_ordinal t p f j link)
  · exact congrArg (· %g) (fromField_ordinal t p f j link)

/-- Fill only the addressed free coordinates. The exterior and trailing padding lanes
retain their chosen initial values. -/
noncomputable def fillFree (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (input : FreePort R r w → Bool) (unused : (Σ _ : FreeBlock R V, Fin g) → Bool) :
    Crossing.Ports (fun _ : FreeBlock R V => g) :=
  fun a j => Function.extend (freeLane hg room) input unused ⟨a,j⟩

/-- Restricting the grouped words recovers every individual literal and pin bit. -/
theorem fillFree_read (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (input : FreePort R r w → Bool) (unused : (Σ _ : FreeBlock R V, Fin g) → Bool) (p : FreePort R r w) :
    let a := freeLane hg room p
    fillFree hg room input unused a.1 a.2 = input p :=
  (freeLane hg room).injective.extend_apply ..

/-- Directory dimensions of the two free fields, with one supplied word per original
team and site and the real processor spacing. -/
def freeDirectory (R r w link V g entries desc : ℕ) : Packing.Directory.Layout :=
  { teams := R+1, processors := r, literal := w, link := link, fields := 2, sites := V,
    block := g, entries := entries, description := desc }

/-- Every physical free lane belongs to an actual emitted delivery. The receiver
reads its group's cell-local base plus exactly the surviving lane number. -/
theorem freeLane_delivered (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g) (entries desc : ℕ)
    (pp lp : ℕ → ℕ × ℕ) (t : Fin (R+1)) (p : Fin r) (f : Fin 2) (j : Fin w) :
    let D := freeDirectory R r w link V g entries desc
    let a := freeLane hg room (fromField t p f j)
    let dest := lp (a.1.1.val*V+a.1.2.val)
    ∃ row ∈ D.directory pp lp, ∃ off < row.width, row.team = t.val ∧ row.processor = p.val ∧
      row.field = f.val ∧ row.offset+off = j.val ∧ row.cell = dest.1 ∧ row.slot+off = dest.2+a.2.val := by
  intro D a dest
  obtain ⟨team,site,lane⟩ := freeLane_field hg room t p f j
  change a.1.1 = t at team
  change a.1.2.val = _ at site
  change a.2.val = _ at lane
  dsimp only [dest]
  rw [team,site,lane]
  exact D.live_delivered pp lp t p f hg j

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
