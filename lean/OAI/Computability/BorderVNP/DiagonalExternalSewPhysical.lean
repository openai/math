import OAI.Computability.BorderVNP.DiagonalExternalSew
import OAI.Computability.BorderVNP.DiagonalExternalSewBlockAddress
import OAI.Computability.BorderVNP.DiagonalExternalSewPorts
import OAI.Computability.BorderVNP.DiagonalExternalSewAncestry

/-! # Sewing the actual partner fields on a compressed physical pack

An original processor input keeps its initial block number through the
history, although the host of that block moves and its sparse name may
change. A paired interval uses the two resulting stored vertices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening CellEntries TeamContraction ParseBatch
open scoped BigOperators Classical

variable {R r w link g D : ℕ} {P : Type}
    {N M : Network D P (fun _ => 1)} {physical : PublicPort R r w link ≃ P}

/-- The initial block of a fine public processor slot, in team-local order. -/
def rawBlock (g : ℕ) (p : PublicPort R r w link) : Fin (R+1) × ℕ :=
  (p.1, (p.2.1.val*(2*w+R*link) + p.2.2.val)/g)

/-- The real final vertex occupied by each original input block. -/
structure BlockHosts (N : Network D P (fun _ => 1)) (physical : PublicPort R r w link ≃ P) (g : ℕ) where
  /-- Vertex where the original team and block are read. -/
  host : Fin (R+1) × ℕ → N.Site
  attach : ∀ p, N.attach (physical p) = host (rawBlock g p)

/-- The initial block association persists under an actual retained-site map. -/
def BlockHosts.retained (h : BlockHosts N physical g) (s : Retains N M) : BlockHosts M physical g :=
  ⟨s.site ∘ h.host,fun p => (s.attach _).trans (congrArg s.site (h.attach p))⟩

/-- Actual live cable intervals, obtained by cutting each processor's
partner field at the site-block boundaries at both ends. -/
abbrev Cables (R r w link g : ℕ) :=
  Pieces (fieldStart (R := R) (r := r) w (2*w+R*link) link) g link

/-- Number of ordered bit positions in the physical cable interval. -/
abbrev cableWidth (c : Cables R r w link g) := pieceWidth _ _ c

/-- The exterior bit named by each physical cable and offset. -/
noncomputable def cableBits (R r w link g : ℕ) :
    (Σ c : Cables R r w link g, Fin (cableWidth c)) ≃ Exterior R r link :=
  (pieceBits _ g).trans (Equiv.prodAssoc _ _ _)

/-- This physical cable bit names the unordered team pair, the original
processor, and the increasing offset within that partner field. -/
theorem cableBits_at (c : Cables R r w link g) (j : Fin (cableWidth c)) :
    cableBits R r w link g ⟨c,j⟩ = (c.1.1,c.1.2,pieceOffset _ _ c j) := rfl

/-- The actual pairing at the terminal host, with literals and pins still free. -/
noncomputable def BlockHosts.bundle (h : BlockHosts N physical g) :
    Bundle N (FreePort R r w) (Cables R r w link g) cableWidth where
  ports := ((Equiv.sumCongr (Equiv.refl _) ((Equiv.refl Bool).prodCongr (cableBits R r w link g))).trans
    (publicPortEquiv R r w link)).trans physical
  endpoint c side := h.host (fieldBlock w (2*w+R*link) link g c side)
  atEnd c side j := by
    change N.attach (physical (publicPortEquiv R r w link
      (.inr (side,c.1.1,c.1.2,pieceOffset _ _ c j)))) = _
    rw [h.attach, publicPortEquiv_exterior, fieldBlock_bit w (2*w+R*link) link g c side j]
    simp only [rawBlock, Nat.add_assoc]

/-- Assigning the physical interval words is exactly assigning one Boolean
to each original exterior wire in the diagonal. -/
noncomputable def exteriorAssignments (R r w link g : ℕ) :
    (Exterior R r link → Bool) ≃ Ports (cableWidth (R := R) (r := r) (w := w) (link := link) (g := g)) :=
  ((cableBits R r w link g).symm.arrowCongr (Equiv.refl Bool)).trans
    (Equiv.piCurry fun _ _ => Bool)

/-- Each bit of the resulting interval word reads the same global wire
assignment as the two physical ends. -/
theorem exteriorAssignments_at (ext : Exterior R r link → Bool) (c : Cables R r w link g)
    (j : Fin (cableWidth c)) :
    exteriorAssignments R r w link g ext c j = ext (cableBits R r w link g ⟨c,j⟩) := rfl

variable {t d inner n : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    {physical : PublicPort R r (G.program.length+t) link ≃ P} (h : BlockHosts N physical g)

/-- The joined inputs, with the physical free literal and pin values, are
the actual prewired processor words at every public slot. -/
theorem physical_inputs (pin : Fin d → Bool) (ext : Exterior R r link → Bool) :
    h.bundle.joined (fun p _ => freeBits G pin p) (exteriorAssignments R r _ link g ext) =
      fun p _ => Prewire.publicBits G (physical.symm p).1 pin ext (physical.symm p).2 := by
  funext p j
  obtain ⟨s,rfl⟩ := h.bundle.ports.surjective p
  rw [Bundle.joined, Equiv.symm_apply_apply]
  let z := (Equiv.sumCongr (Equiv.refl (FreePort R r (G.program.length+t)))
    ((Equiv.refl Bool).prodCongr (cableBits R r (G.program.length+t) link g))) s
  change Bundle.slotValue _ _ s j =
    Prewire.publicBits G (physical.symm (physical (publicPortEquiv R r _ link z))).1 pin ext
      (physical.symm (physical (publicPortEquiv R r _ link z))).2
  rw [physical.symm_apply_apply, publicBits_at G pin ext z]
  cases s <;> rfl

/-- The contraction of this genuine post-sew network on the supplied
literals and pin equals the sum over the original physical exterior
variables, over any coefficient semiring. -/
theorem physical_value {S : Type*} [CommSemiring S] (T : N.Tables S) (pin : Fin d → Bool) :
    h.bundle.layout.value (h.bundle.tables T) (fun p _ => freeBits G pin p) =
      ∑ ext : Exterior R r link → Bool, N.value T
        (fun p _ => Prewire.publicBits G (physical.symm p).1 pin ext (physical.symm p).2) := by
  rw [h.bundle.value]
  let eqv := exteriorAssignments R r (G.program.length+t) link g
  apply Fintype.sum_equiv eqv.symm
  intro y
  exact congrArg (N.value T) ((congrArg (h.bundle.joined _) (eqv.apply_symm_apply y).symm).trans
    (physical_inputs G h pin (eqv.symm y)))

/-- The same physical sum retains the unary owners and the formal
parameter and gadget factors that the cube evaluator consumes. -/
theorem physical_tracked {Team Param Gadget E : Type*} [Fintype Team] [Fintype Param] [CommSemiring E]
    {b : ℕ} (t0 : Tracked Team Param Gadget b N) (values : Gadget → E) (pin : Fin d → Bool) :
    ((h.bundle.tracked t0).valued values).tensor (fun p _ => freeBits G pin p) =
      ∑ ext : Exterior R r link → Bool, (t0.valued values).tensor
        (fun p _ => Prewire.publicBits G (physical.symm p).1 pin ext (physical.symm p).2) :=
  physical_value G h (t0.valued values).table pin

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
