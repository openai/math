import OAI.Hierarchy.TaggedWidePortPartition
import OAI.Hierarchy.TaggedWireNamedPlaces
import OAI.Hierarchy.TaggedWireRowGraph

namespace OAI
/-! # The native per-chord port partition carried to the public site slots -/

noncomputable section
namespace Hierarchy.Tagged.PassiveWindow
open AdaptiveProbe WireTelescope NamedAperture LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical BigOperators

variable {S n W : ℕ} (ends : Fin n → Chord S) (bits : Fin n→ℕ) (s : Fin S)

abbrev EndsAt := {p : (rowGraph ends).Port s // 0<bits p.val.1}

def byRow (p : EndsAt ends bits s) : (portGraph S).Port s :=
  ⟨(ends p.val.val.1,p.val.val.2),p.val.property⟩

def prefixAt (i : Fin n) := TaggedShorterCommonScan.earlier (key ends) bits i.val (key ends i)

theorem segment_top (i : Fin n) : prefixAt ends bits i+bits i ≤ installedWidths ends bits (ends i) := by
  rw [prefixAt,← NativeSlot.next,←measured,←NativeSlot.full]
  exact NativeSlot.earlier_mono _ _ _ i.isLt

/-- Genuine positive-only original physical rows. Zero-width fictional rows
never enlarge a site's occupation. Coverage follows from the bijective
weighted prefix order over all ordinal rows, including parallel arcs. -/
def originalParts (fit : ∀i,bits i ≤ W) :
    Parts ((portGraph S).Port s) (EndsAt ends bits s) W
      (fun p=>installedWidths ends bits p.val.1) where
  owner i := some (byRow ends bits s i)
  base i := prefixAt ends bits i.val.val.1
  width i := bits i.val.val.1
  within i := fit _
  top i p h := by cases Option.some.inj h;exact segment_top ends bits _
  covers p j := by
    obtain ⟨⟨i,u⟩,hit⟩ := (chordBits ends bits).surjective ⟨p.val.1,j⟩
    have edge : ends i=p.val.1 := (chord_at ends bits ⟨i,u⟩).symm.trans (congrArg Sigma.fst hit)
    have ord := congrArg (fun q : (e : Chord S) × Fin (installedWidths ends bits e)=>q.2.val) hit
    rw [offset] at ord
    have site : (rowGraph ends).vertex i p.val.2 = (portGraph S).vertex (ends i) p.val.2 := by
      cases p.val.2 <;> rfl
    let row : (rowGraph ends).Port s := ⟨(i,p.val.2), site.trans ((congrArg (fun e => (portGraph S).vertex e p.val.2) edge).trans p.property)⟩
    refine ⟨⟨row,by exact (Nat.zero_le u.val).trans_lt u.isLt⟩,?_,u,ord⟩
    apply congrArg some
    exact Subtype.ext (Prod.ext edge rfl)

/-- Remaining fixed public apertures have no bits and no physical neighbor.
This transports without ordering or enumerating zero-width protocol rows. -/
def Parts.expand {P A B : Type*} {t : P→ℕ} (o : Parts P A W t) (place : A ↪ B) : Parts P B W t where
  owner := Function.extend place o.owner (fun _=>none)
  base := Function.extend place o.base (fun _=>0)
  width := Function.extend place o.width (fun _=>0)
  within b := by
    by_cases hit : ∃a,place a=b
    · obtain ⟨a,rfl⟩ := hit
      rw [place.injective.extend_apply]
      exact o.within a
    · rw [Function.extend_apply' _ _ _ hit];exact Nat.zero_le _
  top b p hp := by
    by_cases hit : ∃a,place a=b
    · obtain ⟨a,rfl⟩ := hit
      rw [place.injective.extend_apply] at hp
      rw [place.injective.extend_apply,place.injective.extend_apply]
      exact o.top a p hp
    · rw [Function.extend_apply' _ _ _ hit] at hp
      contradiction
  covers p j := by
    obtain ⟨i,hi,u,hu⟩ := o.covers p j
    refine ⟨place i,by rwa [place.injective.extend_apply],⟨u.val,by simpa only [place.injective.extend_apply] using u.isLt⟩,?_⟩
    simpa only [place.injective.extend_apply] using hu

section
variable {S n cap : ℕ} {A : Type} (ends : Fin n → Chord S) (bits : Fin n→ℕ) (s : Fin S)
    (room : ∀i,bits i ≤ cap) (slot : EndsAt ends bits s ↪ A)
    {total : Widths S} (shape : installedWidths ends bits=total)

def carried : Parts ((portGraph S).Port s) A cap (fun p=>total p.val.1) :=
  shape ▸ (originalParts ends bits s room).expand slot

end

end Hierarchy.Tagged.PassiveWindow

end
end OAI
