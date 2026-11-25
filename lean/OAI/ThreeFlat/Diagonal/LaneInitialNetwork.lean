import OAI.ThreeFlat.BitNetwork.OrderedPair
import OAI.ThreeFlat.BitNetwork.PinMap
import OAI.ThreeFlat.Diagonal.LaneRelayNetwork

namespace OAI
/-! # The entire initial lane cursor cell on its actual pin and half-port bits -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

open TraceCircuit
open scoped BigOperators Classical

variable {F : Type*} [CommSemiring F] {p k low offsets slots r : ℕ} {N : BitNetwork F p}
    {P : RowLayout N (k+1) low offsets slots} {lane : Lane (k+1)} (I : BucketIndex P lane)

abbrev PortData (r offsets low slots : ℕ) := PortFields r (Fin offsets) (PayloadAddress low slots)
private abbrev rows (r : ℕ) := (r+1)*2
private abbrev both (r t : ℕ) := rows r*t + rows r*t

/-- Source in the first layer's joined `[owned pins | outgoing | incoming]` vector. -/
def initialSource : Fin (both r I.t + I.arity) → Fin (I.x + both r I.t) :=
  let send (u : Fin I.t) := finProdFinEquiv (selected (r:=r) P.mask (I.tag u).1 (0 : Fin (k+1)),u)
  let recv (u : Fin I.t) := finProdFinEquiv (selected (r:=r) P.mask (I.tag u).1 (Fin.last k),u)
  Fin.append (Fin.natAdd I.x) (Fin.append (Fin.castAdd _) (Fin.append
    (fun u => Fin.natAdd I.x ((send u).castAdd _))
    (fun u => Fin.natAdd I.x (Fin.natAdd _ (recv u)))))

private def firstPin (pin : Fin p → Bool) (outwards inwards : PortData r offsets low slots) :
    Fin (I.x + both r I.t) → Bool :=
  Fin.append (fun j => pin (I.ext j).val) (RelayNetwork.pins I.tag outwards inwards)

omit [CommSemiring F] in
private theorem first_read (pin : Fin p → Bool) (o a : PortData r offsets low slots) :
    (fun i => ((some (I.initialSource (r:=r) i)).map (I.firstPin pin o a)).getD false) =
    Fin.append (RelayNetwork.pins I.tag o a) (I.inputs pin
      (fun t => o (selected P.mask t.1 (0:Fin (k+1))) t)
      (fun t => a (selected P.mask t.1 (Fin.last k)) t)) := by
  funext i
  dsimp only [arity,both,rows] at i ⊢
  refine Fin.addCases (fun z => ?_) (fun z => ?_) i
  · simp only [initialSource,firstPin,arity,both,rows,Fin.append_left,Fin.append_right,Option.map_some,Option.getD_some]
    exact (Fin.append_left (RelayNetwork.pins I.tag o a) (I.inputs pin
      (fun t=>o (selected P.mask t.1 0) t) (fun t=>a (selected P.mask t.1 (Fin.last k)) t)) z).symm
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) z
    · simp only [initialSource,firstPin,arity,both,rows,inputs,Fin.append_left,Fin.append_right,Option.map_some,Option.getD_some]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp only [initialSource,firstPin,arity,both,rows,inputs,RelayNetwork.pins,Function.comp_apply,Fin.append_left,Fin.append_right,
          blocks_at,Option.map_some,Option.getD_some]

/-- Only the first cursor layer owns the original trace input pins and
hidden witnesses. The other layers consist entirely of relay equalities. -/
noncomputable def initialNetwork : (first : Bool) → (i : Fin (k+1)) → BitNetwork F (if first then I.x + both r I.t else both r I.t)
  | true,i => ((BitNetwork.Ordered.pair (RelayNetwork.network (r:=r) I.tag P.mask i) I.network)).restrictPins
      (some ∘ I.initialSource)
  | false,i => RelayNetwork.network I.tag P.mask i

def initialInputs (pin : Fin p → Bool) (o a : PortData r offsets low slots) :
    (first : Bool) → Fin (if first then I.x + both r I.t else both r I.t) → Bool
  | true => I.firstPin pin o a
  | false => RelayNetwork.pins I.tag o a

theorem initial_eval (i : Fin (k+1)) (pin : Fin p → Bool) (o a : PortData r offsets low slots) :
    (I.initialNetwork (r:=r) (decide (i=0)) i).eval (I.initialInputs pin o a (decide (i=0))) =
      portTensor P.mask (P.localTensor pin) i lane o a := by
  generalize atZero : decide (i=0) = first
  cases first with
  | true =>
    have hi : i=0 := of_decide_eq_true atZero
    subst i
    change ((BitNetwork.Ordered.pair (RelayNetwork.network (r:=r) I.tag P.mask 0) I.network).restrictPins _).eval
      (I.firstPin pin o a) = _
    rw [BitNetwork.restrictPins_eval]
    rw [show (fun i => (((some ∘ I.initialSource (r:=r)) i).map (I.firstPin pin o a)).getD false) = _ from I.first_read pin o a,
        BitNetwork.Ordered.pair_eval,RelayNetwork.eval,I.eval]
    by_cases ok : PortChecks P.mask (0:Fin (k+1)) o a <;> simp [portTensor,ok]
  | false =>
    have hi : i≠0 := of_decide_eq_false atZero
    change (RelayNetwork.network (r:=r) I.tag P.mask i).eval (RelayNetwork.pins I.tag o a) = _
    rw [RelayNetwork.eval]
    simp only [portTensor,ite_eq_right hi]

end ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

end OAI
