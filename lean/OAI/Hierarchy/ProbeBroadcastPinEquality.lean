import OAI.Hierarchy.ProbeBroadcastReadout
import OAI.Hierarchy.TaggedWireEquality

namespace OAI
/-! # A linear trivalent check of the actual incident selector sockets -/

noncomputable section
namespace Hierarchy.Probe.BroadcastPins
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Routing
open WireTelescope
open scoped Classical BigOperators

variable {k n : ℕ} {F : Type*} [CommSemiring F]
abbrev Bits (q : Widths k) (i : Fin k) := Σ p : (portGraph k).Port i,Fin (q p.val.1)

/-- Recover the candidate selector from the low bits of one genuine
incident wire. Every other incidence is checked against this word. -/
def candidate (q : Widths k) (i : Fin k) (root : (portGraph k).Port i)
    (z : State q i) (n : ℕ) : Fin (2^n) :=
  ⟨(z root).val % 2^n,Nat.mod_lt _ (by positivity)⟩

def read (q : Widths k) (i : Fin k) (z : State q i) (p : Bits q i) :=
  (z p.1).val.testBit p.2.val

def compare (q : Widths k) (i : Fin k) (root : (portGraph k).Port i) (room : n≤q root.val.1)
    (bit : Equality.Pins (Fintype.card (Bits q i))) : Bits q i ⊕ Bool :=
  let u:=(Fintype.equivFin (Bits q i)).symm bit.1
  if bit.2=0 then .inr true else if bit.2=1 then .inl u else
    if small : n≤q u.1.val.1 ∧ u.2.val<n then .inl ⟨root,⟨u.2.val,small.2.trans_le room⟩⟩
    else .inr false

/-- One comparison per actually present bit. Its true/false constant pins
enforce both short-wire and spare high-bit zero padding. -/
def network (F : Type*) [Zero F] [One F] (q : Widths k) (i : Fin k) (root : (portGraph k).Port i)
    (room : n≤q root.val.1) : BitNetwork F (Fintype.card (Bits q i)) :=
  Tagged.RadixStage.pullPins (Equality.network F _) (compare q i root room)

private theorem word_ext {b : ℕ} (u v : Fin (2^b))
    (bits : ∀j : Fin b,u.val.testBit j.val=v.val.testBit j.val) : u=v := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases inside : j<b
  · exact bits ⟨j,inside⟩
  · have cap := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt inside)
    rw [Nat.testBit_eq_false_of_lt (u.isLt.trans_le cap),Nat.testBit_eq_false_of_lt (v.isLt.trans_le cap)]

private theorem expected (q : Widths k) (i : Fin k) (root : (portGraph k).Port i) (z : State q i)
    (u : Bits q i) :
    ((colourState q i (candidate q i root z n) u.1).val).testBit u.2.val=
      if n≤q u.1.val.1 ∧ u.2.val<n then (z root).val.testBit u.2.val else false := by
  by_cases fit : n≤q u.1.val.1
  · by_cases lo : u.2.val<n
    · simp [colourState,extendColour,candidate,fit,lo,Nat.testBit_mod_two_pow]
    · simp [colourState,extendColour,candidate,fit,lo,Nat.testBit_mod_two_pow]
  · simp [colourState,extendColour,fit]

theorem eval (q : Widths k) (i : Fin k) (root : (portGraph k).Port i) (room : n≤q root.val.1)
    (z : State q i) :
    TypedWiring.value (network F q i root room) (read q i z)=
      if z=colourState q i (candidate q i root z n) then 1 else 0 := by
  rw [network,Tagged.RadixStage.pullPins_value,Equality.eval]
  congr 1
  apply propext
  simp only [compare,Function.comp_apply,ite_true,Sum.elim_inr,id_eq,true_implies,
    show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide]
  constructor
  · intro checks
    have indexed (t : Fin (Fintype.card (Bits q i))) :
        let u:=(Fintype.equivFin (Bits q i)).symm t
        (z u.1).val.testBit u.2.val=(colourState q i (candidate q i root z n) u.1).val.testBit u.2.val := by
      intro u
      have chk:=checks t
      change (z u.1).val.testBit u.2.val=Sum.elim (read q i z) id
        (if h : n≤q u.1.val.1 ∧ u.2.val<n then .inl ⟨root,⟨u.2.val,h.2.trans_le room⟩⟩ else .inr false) at chk
      rw [expected q i root z u]
      by_cases fits : n≤q u.1.val.1 ∧ u.2.val<n
      · rw [dite_eq_left fits] at chk
        simpa only [ite_eq_left fits,Sum.elim_inl,read] using chk
      · rw [dite_eq_right fits] at chk
        simpa only [ite_eq_right fits,Sum.elim_inr,id_eq] using chk
    funext p
    apply word_ext
    intro j
    let holds (u : Bits q i) : Prop := (z u.1).val.testBit u.2.val =
      (colourState q i (candidate q i root z n) u.1).val.testBit u.2.val
    obtain ⟨t,ht⟩ := (Fintype.equivFin (Bits q i)).symm.surjective (⟨p,j⟩ : Bits q i)
    have chk : holds ((Fintype.equivFin (Bits q i)).symm t):=indexed t
    rw [ht] at chk
    exact chk
  · intro all index
    let u:=(Fintype.equivFin (Bits q i)).symm index
    have bit:=congrArg (fun y : State q i=>(y u.1).val.testBit u.2.val) all
    change (z u.1).val.testBit u.2.val=((colourState q i (candidate q i root z n) u.1).val.testBit u.2.val) at bit
    rw [expected] at bit
    by_cases fits : n≤q u.1.val.1 ∧ u.2.val<n
    · simpa [u,read,fits] using bit
    · simpa [u,read,fits] using bit

theorem size (q : Widths k) (i : Fin k) (root : (portGraph k).Port i) (room : n≤q root.val.1) :
    (network F q i root room).cells+(network F q i root room).internal=
      ∑ p : (portGraph k).Port i,q p.val.1 := by
  simp [network,Tagged.RadixStage.pullPins,Equality.network,Bits,Fintype.card_sigma]

theorem per_copy {B : Type} [Fintype B] (G : PortGraph (Fin k) B) (i : Fin k)
    (root : (portGraph k).Port i) (room : n≤G.chordWidths (fun _=>n) root.val.1) :
    let N:=network F (G.chordWidths (fun _=>n)) i root room
    N.cells+N.internal≤Fintype.card ((portGraph k).Port i)*(Fintype.card B*n) := by
  intro N
  rw [show N.cells+N.internal=_ from size (F:=F) _ _ _ _]
  have one (e : B) (c : Chord k) : G.chordWidth e n c≤n := by
    unfold PortGraph.chordWidth
    split_ifs <;> simp [Finsupp.single_apply] <;> split <;> simp
  have perPort (p : (portGraph k).Port i) : G.chordWidths (fun _=>n) p.val.1≤Fintype.card B*n := by
    simp only [PortGraph.chordWidths,Finsupp.finsetSum_apply]
    exact (Finset.sum_le_sum (fun e _=>one e p.val.1)).trans_eq (by simp)
  exact (Finset.sum_le_sum (fun p _=>perPort p)).trans_eq (by simp)

end Hierarchy.Probe.BroadcastPins
end

end OAI
