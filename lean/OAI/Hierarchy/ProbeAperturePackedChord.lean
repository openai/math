import OAI.Hierarchy.ProbeApertureCompactor
import OAI.Hierarchy.ProbePlacedTerm
import OAI.LinearAlgebra.SpectralBooks.RawTiledTables

namespace OAI
/-! # The ordered physical mask circuit packs exactly one signed half-chord -/

noncomputable section
namespace Hierarchy.Probe.ApertureCompactor
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Diagonal MotifBinaryPacking Routing
open AdaptiveProbe
open scoped Classical BigOperators
variable {k n d b : ℕ}

def slices (ends : Fin n→Chord k) (bits : Fin n→ℕ) (c : Chord k) (i : Fin n) :=
  (bits i • unitChord (ends i)) c

theorem slices_bound (ends : Fin n→Chord k) (bits : Fin n→ℕ) (c : Chord k) (bound : ∀i,bits i≤d) :
    ∀i,slices ends bits c i≤d := by
  intro i
  simp only [slices,unitChord,Finsupp.smul_apply,Finsupp.single_apply,nsmul_eq_mul]
  split <;> simp [bound]

theorem slices_mass (ends : Fin n→Chord k) (bits : Fin n→ℕ) (c : Chord k) :
    (∑i,slices ends bits c i)=installedWidths ends bits c := by
  simp [installedWidths,slices,Finsupp.finsetSum_apply]

def bitsAt (ends : Fin n→Chord k) (bits : Fin n→ℕ) (c : Chord k) (a : Index (installedWidths ends bits) c)
    (i : Fin n) (j : Fin (slices ends bits c i)) : Bool :=
  (blockWireIndex (fun u=>bits u • unitChord (ends u)) c a i).val.testBit j.val

/-- Hole-free data from one sorted endpoint, including all aliased original
roles, is the exact little-endian word requested by the signed table. -/
theorem chord_bits (ends : Fin n→Chord k) (bits : Fin n→ℕ) (c : Chord k)
    (a : Index (installedWidths ends bits) c) (j : Fin (n*d)) :
    compacted (slices ends bits c) (bitsAt ends bits c a) j=a.val.testBit j.val := by
  let L:=slices ends bits c
  by_cases inside : j.val<∑i,L i
  · let u : Fin (∑i,L i):=⟨j.val,inside⟩
    obtain ⟨⟨i,t⟩,hh⟩:=(finSigmaFinEquiv (n:=L)).surjective u
    have num : ((finSigmaFinEquiv (n:=L) ⟨i,t⟩).val)=j.val:=congrArg Fin.val hh
    have wire:=blockWireIndex_testBit (fun v=>bits v • unitChord (ends v)) c a i t
    change (if h : j.val<∑i,L i then flatten L (bitsAt ends bits c a) ⟨j.val,h⟩ else false)=_
    rw [dite_eq_left inside]
    change flatten L (bitsAt ends bits c a) u=_
    rw [←hh]
    have eqpos : t.val+(∑v : Fin i.val,L (Fin.castLE i.isLt.le v))=j.val := calc
      _ = (∑v : Fin i.val,L (Fin.castLE i.isLt.le v)) + t.val := Nat.add_comm _ _
      _ = ((finSigmaFinEquiv (n:=L) ⟨i,t⟩).val) := (finSigmaFinEquiv_apply (n:=L) ⟨i,t⟩).symm
      _ = j.val := num
    let read (q : (i : Fin n) × Fin (L i)) := bitsAt ends bits c a q.1 q.2
    have recover := congrArg read (finSigmaFinEquiv.symm_apply_apply ⟨i,t⟩)
    exact recover.trans (wire.trans (congrArg (fun m => a.val.testBit m) eqpos))
  · have tall:=slices_mass ends bits c
    have high : a.val<2^j.val := a.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2)
      (tall.symm.le.trans (Nat.le_of_not_gt inside)))
    simp [compacted,L,inside,Nat.testBit_eq_false_of_lt high]

theorem pack_chord (F : Type*) [CommRing F] (ends : Fin n→Chord k) (bits : Fin n→ℕ)
    (c : Chord k) (bound : ∀i,bits i≤d) (room : d<2^b)
    (a : Index (installedWidths ends bits) c) (out : Fin (n*d)→Bool) :
    (network F n d b).eval (pins (slices ends bits c)
      (TrackData.padded finProdFinEquiv.symm (slices ends bits c) (bitsAt ends bits c a)) out)=
      if out=(fun j=>a.val.testBit j.val) then 1 else 0 := by
  rw [packed_eval F _ (slices_bound ends bits c bound) room]
  have same:=funext (chord_bits (d:=d) ends bits c a)
  rw [same]

end Hierarchy.Probe.ApertureCompactor
end

end OAI
