import OAI.ThreeFlat.Diagonal.TraceEndpointSlice
import OAI.ThreeFlat.Diagonal.TraceBucketImage
import OAI.ThreeFlat.Diagonal.TraceBucketInitial

namespace OAI
/-! # Initial history atoms with exactly two external bits per true endpoint coordinate -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

open scoped Classical

private theorem atZero {F : Type*} [CommSemiring F] {p k low offsets slots copies : ℕ}
    {N : BitNetwork F p} {P : RowLayout N (k+1) low offsets slots} {lane : Lane (k+1)}
    (I : BucketIndex P lane) (i : Fin (k+1)) (hi : i.val=0) (pin : Fin p→Bool)
    (o a : PortData copies offsets low slots) :
    (I.initialNetwork (r:=copies) true i).eval (I.initialInputs pin o a true) =
      portTensor P.mask (P.localTensor pin) i lane o a := by
  have equal : i=0 := Fin.ext hi
  have selected := I.initial_eval i pin o a
  have bit : decide (i=0)=true := decide_eq_true equal
  rw [bit] at selected
  exact selected

end ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner TraceSuffix
open scoped Classical Fin.CommRing
variable {F : Type*} [Fintype F] [CommRing F] {w p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (base : ℕ) (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low))) (L : Lane (q+1))
set_option quotPrecheck false
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k d
local notation "I" => bitIndex hF hw hp base st hs hf r k fit L
local notation "A" => bitAddress hF hw hp base st hs hf r k fit L I
local notation "N" => network hF hw hp base st hs hf r k d
local notation "P" => layout hF hw hp base st hs hf r k fit
local notation "ln" => (finFunctionFinEquiv L).val

noncomputable def trueNetwork {T : ℕ} (size : 2*T≤S) (pub : ℕ→Bool) : BitNetwork F (2*T) :=
  TraceSuffix.network (ports:=0) N size 0 pub

theorem trueNetwork_eval {T : ℕ} (size : 2*T≤S) (pub : ℕ→Bool) (pin : Fin (2*T)→Bool) :
    (trueNetwork hF hw hp base st hs hf r k (q:=q) (low:=low) size pub).eval pin=(N).eval (fullHeader size pin pub) := by
  rw [trueNetwork,TraceSuffix.eval]
  apply congrArg (N).eval
  funext i
  by_cases h : i.val<2*T <;> simp [fullHeader,fullPin,h]

def localPairPins {T : ℕ} (_size : 2*T≤S) (pin : Fin (2*T)→Bool)
    (low lane : ℕ) : Fin (retained T low lane)→Bool := fun j =>
  pin ⟨laneStart low lane+j.val,at_true j.isLt⟩

noncomputable def pairLeaf (copies T : ℕ) (size : 2*T≤S) (pub : ℕ→Bool) :
    BitNetwork F (retained T low ln + BucketIndex.ports copies (I).t) :=
  TraceSuffix.network ((I).firstNetwork (r:=copies) A 0)
    (show retained T low ln ≤ (I).x from retained_le size) (laneStart low ln) pub

theorem pairLeaf_eval (copies T : ℕ) (size : 2*T≤S) (pub : ℕ→Bool) (pin : Fin (2*T)→Bool)
    (o a : BucketIndex.PortData copies (1+(d+d)) low (G).cells) :
    (pairLeaf hF hw hp base st hs hf r k fit L copies T size pub).eval
      (Fin.append (localPairPins size pin low ln) (RelayNetwork.pins (I).tag o a)) =
        portTensor (P).mask ((P).localTensor (fullHeader size pin pub)) 0 L o a := by
  have localId (i : Fin (I).x) : ((I).ext i).val.val=laneStart low ln+i.val := by
    exact bitExt_apply_val hF hw hp base st hs hf r k fit L i
  have matched := fullPin_append (show retained T low ln≤(I).x from retained_le size)
    (laneStart low ln) pub (fun j => fullHeader size pin pub ((I).ext j).val)
    (localPairPins size pin low ln) (RelayNetwork.pins (I).tag o a)
    (by
      intro j
      have live : laneStart low ln + j.val < 2*T := at_true j.isLt
      simp only [fullHeader,localPairPins,localId,Fin.val_castLE,dite_eq_left live])
    (by
      intro j hj
      have fixed : ¬ laneStart low ln + j.val < 2*T := Nat.not_lt.mpr (past_true size j.isLt hj)
      simp only [fullHeader,localId,dite_eq_right fixed])
  refine (TraceSuffix.eval ((I).firstNetwork (r:=copies) A 0)
    (show retained T low ln ≤ (I).x from retained_le size) (laneStart low ln) pub _).trans ?_
  rw [matched,(I).firstNetwork_eval]
  exact BucketIndex.atZero (I) (0 : Fin (q+1)) rfl (fullHeader size pin pub) o a


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
