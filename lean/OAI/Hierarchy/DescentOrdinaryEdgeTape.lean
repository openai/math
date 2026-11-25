import OAI.Hierarchy.DescentSubroundNormalize
import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # Chronological ordinals of genuine surviving ordinary and motif cables -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open Computability.BorderVNP.Crossing DescentHostDirectory GadgetNetwork DescentNetworkPartition DescentCableUnbundling
open scoped Classical BigOperators
noncomputable section
variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
local notation "N" => W.graph
variable {ne ni : ℕ} (edge : W.graph.Edge≃Fin ne) (pair : I≃Fin ni)
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "supply" => branchWidth G z p
local notation "lay" => bestLayout supply
local notation "phys" => physical N pick supply
local notation "loc" => newSite N pick lay pack
local notation "sel" => W.selected G pick z hz fit pack p
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g : ℕ)
local notation "coarse" => coalesced sel key flag k g
local notation "pub" => address sel key flag k g

/-- The first band holds the incoming edges. The ten fresh edge types per
pair use its true compact rank in the matched 9-word table. -/
def edgeNumber : GadgetNetwork.Edge (I:=I) N→ℕ
  | .inl e=>(edge e).val
  | .inr (.inl (i,s))=>ne+10*(pair i).val+s.val
  | .inr (.inr (i,j))=>ne+10*(pair i).val+2+j.val

omit [Field F] [Fintype I] in
theorem edgeNumber_inj : Function.Injective (edgeNumber W edge pair) := by
  rintro (u|⟨i,s⟩|⟨i,j⟩) (v|⟨b,t⟩|⟨b,l⟩) equal <;> simp only [edgeNumber] at equal
  · exact congrArg Sum.inl (edge.injective (Fin.ext equal))
  · have := (edge u).isLt;omega
  · have := (edge u).isLt;omega
  · have := (edge v).isLt;omega
  · have hs := s.isLt;have ht := t.isLt
    have ab : i=b := pair.injective (Fin.ext (by omega))
    have xy : s=t := Fin.ext (by omega)
    simp [ab,xy]
  · have hs := s.isLt;have ht := l.isLt;omega
  · have := (edge v).isLt;omega
  · have hs := j.isLt;have ht := t.isLt;omega
  · have hs := j.isLt;have ht := l.isLt
    have ab : i=b := pair.injective (Fin.ext (by omega))
    have xy : j=l := Fin.ext (by omega)
    simp [ab,xy]

omit [Field F] [Fintype I] in
theorem edgeNumber_room (e : GadgetNetwork.Edge (I:=I) N) :
    edgeNumber W edge pair e<ne+10*ni := by
  rcases e with prev|⟨i,s⟩|⟨i,j⟩
  · have := (edge prev).isLt; simp only [edgeNumber]; omega
  · have := s.isLt; have := (pair i).isLt; simp only [edgeNumber]; omega
  · have := j.isLt; have := (pair i).isLt; simp only [edgeNumber]; omega

/-- The concrete coalesced endpoints decide survival in both successive
quotients. This test includes all native arm and supply wires. -/
theorem appears_iff (e : (phys).Edge) :
    (∃ q : (coarse).graph.Edge,q.val.val=e) ↔ pub (loc ((phys).src e))≠pub (loc ((phys).dst e)) := by
  constructor
  · rintro ⟨u,rfl⟩
    exact u.property
  · intro differ
    have first : loc ((phys).src e)≠loc ((phys).dst e) := fun h=>differ (congrArg pub h)
    exact ⟨⟨⟨e,first⟩,differ⟩,rfl⟩

def survivorNumber (e : (coarse).graph.Edge) := edgeNumber W edge pair e.val.val

theorem survivorNumber_inj : Function.Injective (survivorNumber W G edge pair pick z hz fit pack p key flag k g) :=
  fun _ _ h=>Subtype.ext (Subtype.ext ((edgeNumber_inj W edge pair) h))

end
end Hierarchy.DescentSixParty.MarkedWorld

namespace Hierarchy.DescentCableUnbundling
open Computability.BorderVNP.Crossing ProtocolRAMPortRanks
open scoped Classical BigOperators
noncomputable section
variable {d : ℕ} {P : Type} {bits : P→ℕ} (N : Network d P bits)
variable (core : Finset N.Edge) (m : N.Edge→ℕ) (q : ℕ) (order : N.Edge→ℕ) (honest : Function.Injective order)
local notation "S" => network N core m q

def span (e : N.Edge) := if e∈core then m e else 1

def pieceUnit : (S).Edge ≃ Units (span N core m) where
  toFun
    | .inl ⟨e,no⟩=>⟨e,⟨0,by simp [span,no]⟩⟩
    | .inr ⟨⟨e,yes⟩,j⟩=>⟨e,⟨j.val,by simp [span,yes]⟩⟩
  invFun e := if yes : e.1∈core then .inr ⟨⟨e.1,yes⟩,⟨e.2.val,by simpa [span,yes] using e.2.isLt⟩⟩
    else .inl ⟨e.1,yes⟩
  left_inv := by rintro (⟨e,no⟩|⟨⟨e,yes⟩,j⟩) <;> simp [*]
  right_inv := by
    rintro ⟨e,j⟩
    by_cases yes : e∈core
    · simp [yes]
    · have h := j.isLt
      have hj : j.val=0 := by simpa [span,yes] using h
      simp [yes]
      exact Fin.ext hj.symm

theorem span_count : Fintype.card (S).Edge=∑e,span N core m e := by
  rw [Fintype.card_congr (pieceUnit N core m q)]
  simp [ProtocolRAMPortRanks.Units,Fintype.card_sigma]

def chronological : (S).Edge ≃ Fin (Fintype.card (S).Edge) :=
  ((pieceUnit N core m q).trans (enumerate (span N core m) order honest)).trans (finCongr (span_count N core m q).symm)

/-- A paid sparse prefix, followed by the chunk's local offset. The
expression involves precisely the retained parents in original chronology. -/
theorem chronological_read (e : (S).Edge) :
    let a:=(pieceUnit N core m q) e
    (chronological N core m q order honest e).val=ProtocolRAMPortRanks.«prefix» (span N core m) order a.1+a.2.val := rfl

end
end Hierarchy.DescentCableUnbundling

end OAI
