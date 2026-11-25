import OAI.Hierarchy.TaggedWireNamedPlaces
import OAI.Hierarchy.TaggedWideTraceBits
import OAI.Hierarchy.TaggedWireNativeSlot
import OAI.Hierarchy.TaggedWireChordRouter

namespace OAI
/-! # Immutable site/port/bit apertures for the actual chronological edge rows -/

noncomputable section
namespace Hierarchy.WireTelescope.NamedAperture
open LinearAlgebra.SpectralBooks ChordGraph
open AdaptiveProbe CalendarTape Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators

variable {S n : ℕ} (ends : Fin n→Chord S) (bits : Fin n→ℕ)

variable {H : Type} (port : Fin n × Bool ↪ H) (cap : H→ℕ)
variable (room : ∀j b,bits j≤cap (port (j,b)))

/-- The numeric index of this original row contribution is precisely the
bit read by the canonical chord port's native mixed-radix decode. -/
theorem bit_address (j : Fin n) (b : Fin (bits j)) :
    TaggedShorterCommonScan.earlier (key ends) bits j.val (key ends j)+b.val =
      b.val+∑i : Fin j.val,(bits (Fin.castLE j.isLt.le i) • unitChord (ends (Fin.castLE j.isLt.le i))) (ends j) := by
  unfold TaggedShorterCommonScan.earlier
  rw [←Fin.sum_univ_eq_sum_range]
  simp [key,unitChord,Finsupp.single_apply,eq_comm,
    show ∀i:Fin j.val,i.val<n from fun i=>i.isLt.trans j.isLt,Nat.add_comm]
  rfl

theorem chord_pair (q : Bundle bits) : chordBits ends bits q=⟨ends q.1,sourceBit ends bits q⟩ := by
  apply Sigma.ext (chord_at ends bits q)
  exact (Fin.heq_ext_iff (congrArg (installedWidths ends bits) (chord_at ends bits q))).mpr rfl

def atPort {s : Fin S} (p : (bitGraph (rowGraph ends) bits).Port s) :
    SiteBit (installedWidths ends bits) s := ⟨sourcePort ends bits p,sourceBit ends bits p.1.1⟩

theorem at_half {s : Fin S} (p : (bitGraph (rowGraph ends) bits).Port s) :
    halfBits ends bits (p.1.1,p.1.2)=⟨s,atPort ends bits p⟩ := by
  change sides _ (chordBits ends bits p.1.1,p.1.2)=_
  rw [chord_pair]
  rcases p with ⟨⟨⟨i,j⟩,side⟩,hp⟩
  cases side <;> subst s <;> rfl

theorem rowBits_siteBits {s : Fin S} (x : State (installedWidths ends bits) s)
    (p : (bitGraph (rowGraph ends) bits).Port s) :
    rowBits ends bits x p=siteBits (installedWidths ends bits) s x (atPort ends bits p) := by
  let i := p.1.1.1
  let j := p.1.1.2
  let q : Bundle bits := ⟨i,j⟩
  let blocks := fun i=>bits i • unitChord (ends i)
  let word : Index (installedWidths ends bits) (ends i) := x (sourcePort ends bits p)
  have width : blocks i (ends i)=bits i := by simp [blocks,unitChord]
  let bit := Fin.cast width.symm j
  have rd := blockWireIndex_testBit blocks (ends i) word i bit
  have idx : (sourceBit ends bits q).val =
      j.val+∑l : Fin i.val,blocks (Fin.castLE i.isLt.le l) (ends i) :=
    (offset ends bits q).trans (bit_address ends bits i j)
  change wordBits (bits i) (chunk ends bits i word) j=
    wordBits (installedWidths ends bits (ends i)) word (sourceBit ends bits q)
  calc
    _ = (chunk ends bits i word).val.testBit j.val := (Computability.VPVNP.LiveHeader.testBit_wordBits _ j).symm
    _ = word.val.testBit (j.val+∑l : Fin i.val,blocks (Fin.castLE i.isLt.le l) (ends i)) := rd
    _ = word.val.testBit (sourceBit ends bits q).val := congrArg (Nat.testBit word.val) idx.symm
    _ = _ := Computability.VPVNP.LiveHeader.testBit_wordBits word (sourceBit ends bits q)

theorem port_read {s : Fin S} (p : (bitGraph (rowGraph ends) bits).Port s) :
    place ends bits port cap room ⟨s,atPort ends bits p⟩=⟨port (p.1.1.1,p.1.2),p.1.1.2.castLE (room _ _)⟩ := by
  rw [←at_half ends bits p,read]

theorem live_read {H : Type} (ports : LiveEnd bits ↪ H) (caps : H→ℕ) (fits : ∀p,bits p.val.1≤caps (ports p))
    {s : Fin S} (p : (bitGraph (rowGraph ends) bits).Port s) :
    let r : LiveEnd bits := ⟨(p.1.1.1,p.1.2),Nat.zero_lt_of_lt p.1.1.2.isLt⟩
    livePlace ends bits ports caps fits ⟨s,atPort ends bits p⟩=⟨ports r,p.1.1.2.castLE (fits r)⟩ := by
  dsimp only
  rw [←at_half ends bits p]
  simp [livePlace,live]
  rfl

end Hierarchy.WireTelescope.NamedAperture

end
end OAI
