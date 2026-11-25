import OAI.ThreeFlat.Diagonal.TraceBucketJoin
import OAI.ThreeFlat.Diagonal.LaneInitialNetwork
import OAI.ThreeFlat.RAM.HistoryCompiledRows

namespace OAI
/-! # The native four-word initial bucket uses row-major local hidden slots -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

open RAM.BitLayout
open scoped BigOperators Classical
variable {F : Type*} [CommSemiring F] {p k low o c r H : ℕ} {N : BitNetwork F p}
    {P : RowLayout N (k+1) low o c} {lane : Lane (k+1)} (I : BucketIndex P lane)

abbrev bank (r t : ℕ) := ((r+1)*2)*t
abbrev ports (r t : ℕ) := bank r t+bank r t

/-- Translate the compact local pins into the actual initial site. -/
def attach (u : Fin I.arity) : Fin (I.x+ports r I.t) :=
  I.initialSource (r:=r) (Fin.natAdd (ports r I.t) u)

noncomputable def firstNetwork (A : BitNetwork.Rectangular.Address I.h H) (i : Fin (k+1)) :
    BitNetwork F (I.x+ports r I.t) :=
  TraceBucketJoin.network (RelayNetwork.network (r:=r) I.tag P.mask i) rfl I.network A
    (Fin.natAdd I.x) I.attach

theorem firstNetwork_eval (A : BitNetwork.Rectangular.Address I.h H) (i : Fin (k+1))
    (x : Fin (I.x+ports r I.t) → Bool) : (I.firstNetwork A i).eval x =
      (I.initialNetwork (r:=r) true i).eval x := by
  refine (TraceBucketJoin.eval (RelayNetwork.network (r:=r) I.tag P.mask i) rfl
    I.network A (Fin.natAdd I.x) (I.attach (r:=r)) x).trans ?_
  change _ = ((BitNetwork.Ordered.pair (RelayNetwork.network (r:=r) I.tag P.mask i) I.network).restrictPins
    (some ∘ I.initialSource (r:=r))).eval x
  rw [BitNetwork.restrictPins_eval]
  have args :
      (fun e => ((some (I.initialSource (r:=r) e)).map x).getD false) =
        Fin.append (x ∘ Fin.natAdd I.x) (x ∘ I.attach) := by
    funext e
    refine Fin.addCases (fun z => ?_) (fun z => ?_) e
    · simp [initialSource,Function.comp_def]
      exact congrArg x (Fin.append_left _ _ z)
    · simp [attach,Function.comp_def]
  rw [show (fun e => (((some ∘ I.initialSource (r:=r)) e).map x).getD false)=_ from args,
    BitNetwork.Ordered.pair_eval]

/-- The original-cell row reads its literal directly or the selected
incoming bit. The coefficient tag comes from the original ternary cell. -/
noncomputable def original (tag : ((Fin 3→Bool)→F)→ℕ) (i : Fin I.c) (leg : Fin 4) : ℕ :=
  if h : leg.val<3 then
    let source := N.source (I.cell i).val ⟨leg.val,h⟩
    if live : wired source then
      let t := I.tag.symm (P.tag ⟨((I.cell i).val,⟨leg.val,h⟩),live⟩)
      let arc := selected (r:=r) P.mask (I.tag t).1 (Fin.last k)
      2+I.x+bank r I.t+(arc.val*I.t+t.val)
    else sourceAddress source
  else tag (N.table (I.cell i).val)

/-- Local source addresses after widening hidden bits to their full
rectangular bank. External pins precede both relay banks. -/
def translateWord (A : BitNetwork.Rectangular.Address I.h H) : BitSource N.internal p → ℕ
  | .constant b => b.toNat
  | .pin j => if h : (splitRow _ _ (P.pinRow j)).1=lane then 2+(I.ext.symm ⟨j,h⟩).val else 0
  | .hidden j => if h : (splitRow _ _ (P.hiddenRow j)).1=lane then
      2+(I.x+ports r I.t)+(A.put (I.hidden.symm ⟨j,h⟩)).val else 0

def emissionWord (A : BitNetwork.Rectangular.Address I.h H) (t : Fin I.t) : ℕ :=
  match I.probe (I.tag t) with
  | none => 0
  | some e => I.translateWord (r:=r) A (N.source e.val.1 e.val.2)

def compareRow (A : BitNetwork.Rectangular.Address I.h H) (tag : ((Fin 3→Bool)→F)→ℕ)
    (t : Fin I.t) (leg : Fin 4) : ℕ :=
  if leg.val=0 then 2+I.x+(selected (r:=r) P.mask (I.tag t).1 (0:Fin (k+1))).val*I.t+t.val
  else if leg.val=1 then I.emissionWord (r:=r) A t
  else if leg.val=2 then 0
  else tag (fun z => if z 0=z 1 then 1 else 0)

def holeRow (A : BitNetwork.Rectangular.Address I.h H) (tag : ((Fin 3→Bool)→F)→ℕ)
    (q : Fin H) (leg : Fin 4) : ℕ :=
  if leg.val<3 then 2+(I.x+ports r I.t)+q.val
  else tag (fun z => if (A.get q).isNone=true ∧ z 0=true then 0 else 1)

end ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

end OAI
