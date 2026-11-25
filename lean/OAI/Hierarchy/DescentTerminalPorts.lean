import OAI.Computability.BorderVNP.CrossingNetwork
import OAI.ThreeFlat.Routing.CallBatches
import OAI.Hierarchy.TaggedShorterFields

namespace OAI
/-! # Full cable assignments from canonical uniform terminal words -/

namespace Hierarchy.DescentTerminalPorts
open Computability.BorderVNP.Crossing ThreeFlat.Routing CallPool
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)

abbrev Piece (w : ℕ) := Batch N.width w
abbrev Words (w : ℕ) := Piece N w → Fin w → Bool

def splitWords (w : ℕ) (a : N.Assignment) : Words N w :=
  fun u => TaggedShorterFields.slice w (a u.1) u.2.val

def Slack {w : ℕ} (z : Words N w) : Prop :=
  ∀ u j, N.width u.1≤u.2.val*w+j.val → z u j=false

def joinWords {w : ℕ} (hw : 0<w) (z : Words N w) : N.Assignment :=
  fun e i => z (batchIndex hw e i) ⟨i.val%w,Nat.mod_lt _ hw⟩

theorem slack_split (w : ℕ) (a : N.Assignment) : Slack N (splitWords N w a) := by
  intro u j past
  simp [splitWords,TaggedShorterFields.slice,Nat.not_lt.mpr past]

private theorem div_mod (v w : ℕ) : v/w*w+v%w=v := by
  simpa [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div v w

theorem join_split {w : ℕ} (hw : 0<w) (a : N.Assignment) :
    joinWords N hw (splitWords N w a)=a := by
  funext e i
  simp only [joinWords,splitWords,batchIndex,TaggedShorterFields.slice,div_mod,i.isLt,dite_eq_left]

theorem split_join {w : ℕ} (hw : 0<w) (z : Words N w) (hz : Slack N z) :
    splitWords N w (joinWords N hw z)=z := by
  funext u j
  rcases u with ⟨e,k⟩
  by_cases active : k.val*w+j.val<N.width e
  · have quotient : (k.val*w+j.val)/w=k.val := by
      rw [Nat.mul_comm k.val w,Nat.mul_add_div hw,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
    have residue : (k.val*w+j.val)%w=j.val := by
      simp [Nat.mul_comm k.val w,Nat.mod_eq_of_lt j.isLt]
    have unit : batchIndex (c:=N.width) hw e ⟨k.val*w+j.val,active⟩=⟨e,k⟩ :=
      congrArg (Sigma.mk e) (Fin.ext quotient)
    have digit : (⟨(k.val*w+j.val)%w,Nat.mod_lt _ hw⟩ : Fin w)=j := Fin.ext residue
    simp only [splitWords,TaggedShorterFields.slice,active,dite_eq_left,joinWords,unit,digit]
  · simpa [splitWords,TaggedShorterFields.slice,active] using
      (hz ⟨e,k⟩ j (Nat.le_of_not_lt active)).symm

/-- Terminal words with canonical last-row padding and complete cable
assignments are in bijection. Even a loop uses just one assigned word. -/
def assignmentEquiv {w : ℕ} (hw : 0<w) : N.Assignment ≃ {z : Words N w // Slack N z} where
  toFun a := ⟨splitWords N w a,slack_split N w a⟩
  invFun z := joinWords N hw z.val
  left_inv := join_split N hw
  right_inv z := Subtype.ext (split_join N hw z.val z.property)

/-- The local tensor reads the original incident cable bits and the
original named exterior pins. Other cables never enter its lookup. -/
def localTable {F : Type*} (T : N.Tables F) {w : ℕ} (hw : 0<w)
    (z : Words N w) (x : Ports bits) (v : N.Site) : F :=
  T v (fun e i => z (batchIndex hw e.val i) ⟨i.val%w,Nat.mod_lt _ hw⟩) (fun p => x p.val)

theorem value_words {F : Type*} [CommSemiring F] (T : N.Tables F) {w : ℕ} (hw : 0<w)
    (x : Ports bits) :
    N.value T x = ∑ z : Words N w, if Slack N z then ∏ v,localTable N T hw z x v else 0 := by
  let f (z : Words N w) := ∏ v,localTable N T hw z x v
  change ∑ a : N.Assignment, (∏ v,N.read T a x v) =
    ∑ z : Words N w, if Slack N z then f z else 0
  calc
    _ = ∑ a : N.Assignment, f (splitWords N w a) := by
      apply Finset.sum_congr rfl
      intro a _
      change (∏ v,N.read T a x v)=∏ v,N.read T (joinWords N hw (splitWords N w a)) x v
      rw [join_split]
    _ = ∑ z : {z : Words N w // Slack N z},f z.val :=
      (assignmentEquiv N hw).sum_comp (fun z=>f z.val)
    _ = _ := by
      rw [←Finset.sum_subtype (Finset.univ.filter (Slack N)) (by simp) f,Finset.sum_filter]

theorem piece_count (w : ℕ) :
    Fintype.card (Piece N w) = ∑ e,poolBatchCount (N.width e) w := by
  simp [Piece,Batch,Fintype.card_sigma]

theorem piece_volume {w : ℕ} (hw : 0<w) :
    Fintype.card (Piece N w)*w ≤ (∑ e,N.width e)+Fintype.card N.Edge*w := by
  rw [piece_count,Finset.sum_mul]
  calc
    _ ≤ ∑ e,(N.width e+w) := Finset.sum_le_sum fun e _ => by
      unfold poolBatchCount
      exact (Nat.div_mul_le_self _ _).trans (by omega)
    _ = _ := by simp [Finset.sum_add_distrib]

end
end Hierarchy.DescentTerminalPorts

end OAI
