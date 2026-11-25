import OAI.Hierarchy.DescentDatedStageVenue

namespace OAI
/-! # The exact memory footprint of the reached date's source observations -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentPackedColony DescentColonies DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

def readsFrom (start : ℕ) : Expr→Prop
  | .row | .lit _ => True
  | .lookup b e => start≤b.base ∧ readsFrom start e
  | .op _ e f => readsFrom start e ∧ readsFrom start f
  | .branch _ a b e f => readsFrom start a ∧ readsFrom start b ∧ readsFrom start e ∧ readsFrom start f

theorem read_from_eq {w start : ℕ} (e : Expr) (row : Word w) (m n : Memory w)
    (equal : ∀a,start≤a→n a=m a) (bounds : readsFrom start e) :
    e.eval n row=e.eval m row := by
  induction e with
  | row | lit => rfl
  | lookup b e ih =>
    change n (b.base+_)=m (b.base+_)
    rw [ih bounds.2]
    apply equal
    exact bounds.1.trans (Nat.le_add_right ..)
  | op t a b ha hb => simp only [Expr.eval,ha bounds.1,hb bounds.2]
  | branch t a b x y ha hb hx hy =>
    simp only [Expr.eval,ha bounds.1,hb bounds.2.1,hx bounds.2.2.1,hy bounds.2.2.2]

structure VenueFrom (i : Dated.Operands) (D start : ℕ) : Prop where
  ids : ∀j : Fin D,start≤(i.ids j.val).base
  roster : start ≤ i.roster.base
  offsets : start ≤ i.offsets.base
  chunks : start ≤ i.chunks.base
  actors : start ≤ i.actors.base
  signed : ∀x j,start≤(i.wire x j).base
  hubs : start ≤ i.hubs.base
  atoms : ∀x,readsFrom start (i.atoms x)

theorem stageVenue_frame {F P : Type} [Field F] {u : ℕ} {bits : P→ℕ} {W : MarkedWorld F u P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D wire s H w : ℕ}
    (r : Reached W G q ε S k age z D wire s) (wide : Fintype.card r.V≤H)
    (i : Dated.Operands) (M countBits floor start : ℕ) (rs : Fin H→Fin D→Option (Fin H)) (m n : Memory w)
    (old : stageVenue r wide i M countBits floor rs m) (bounds : VenueFrom i D start)
    (frame : ∀a,start≤a→n a=m a) : stageVenue r wide i M countBits floor rs n := by
  have same {a base : ℕ} (low : start≤base) : n (base+a)=m (base+a):=frame _ (low.trans (Nat.le_add_right ..))
  rcases old with ⟨acc,board,actor,sign,fit,hosts,hub,atomFit,atom⟩
  refine ⟨acc,?_,?_,?_,fit,hosts,?_,atomFit,?_⟩
  · constructor
    · intro p j
      exact (same (bounds.ids j)).trans (board.ids p j)
    · intro h j
      exact (same bounds.roster).trans (board.roster h j)
    · intro h
      exact (same bounds.offsets).trans (board.offsets h)
    · intro p
      exact (same bounds.chunks).trans (board.chunks p)
  · intro p
    exact (same bounds.actors).trans (actor p)
  · intro x j p
    exact (same (bounds.signed x.val j.val)).trans (sign x j p)
  · intro h
    exact (same bounds.hubs).trans (hub h)
  · intro x p
    exact (read_from_eq _ _ m n frame (bounds.atoms x.val)).trans (atom x p)

end
end Hierarchy.DescentSixParty

end OAI
