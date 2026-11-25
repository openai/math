import OAI.ThreeFlat.Diagonal.LaneCursorTrace

namespace OAI
/-! # Initial trivalent factors for a lane bucket

An original cell reads its three received or literal arguments. Each
reserved outgoing address contributes one equality test, including a
zero-test when the address is unused. Only bits owned by this lane are
guessed. External bits owned by the lane are given once as a separate
contiguous pin interval.
-/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout

open scoped BigOperators Classical

variable {F : Type*} [CommSemiring F] {p k low offsets slots : ℕ} {N : BitNetwork F p}
variable (P : RowLayout N (k+1) low offsets slots) (lane : Lane (k+1))

abbrev Tags (offsets low slots : ℕ) := Fin offsets × PayloadAddress low slots

structure BucketIndex where
  h : ℕ
  x : ℕ
  c : ℕ
  t : ℕ
  hidden : Fin h ≃ {i // (splitRow _ _ (P.hiddenRow i)).1 = lane}
  ext : Fin x ≃ {j // (splitRow _ _ (P.pinRow j)).1 = lane}
  cell : Fin c ≃ {a // P.cellLane a = lane}
  tag : Fin t ≃ Tags offsets low slots
  probe : Tags offsets low slots → Option (Occurrence N)
  probe_some : ∀ u a, probe u = some a ↔ P.key a = (lane,u)

namespace BucketIndex

variable {P lane} (I : BucketIndex P lane)

def arity := I.x+(I.t+I.t)

def inputs (pin : Fin p → Bool) (send receive : Tags offsets low slots → Bool) : Fin I.arity → Bool :=
  Fin.append (fun a => pin (I.ext a).val) (Fin.append (send ∘ I.tag) (receive ∘ I.tag))

def unpackHidden (g : Fin I.h → Bool) : P.LocalHidden lane := fun i => g (I.hidden.symm i)

private def ownedPin (pin : Fin p → Bool) (j : Fin p) :=
  if (splitRow _ _ (P.pinRow j)).1 = lane then pin j else false

def translate (s : BitSource N.internal p) : BitSource I.h I.arity :=
  match s with
  | .constant b => .constant b
  | .hidden a => if ha : (splitRow _ _ (P.hiddenRow a)).1 = lane then .hidden (I.hidden.symm ⟨a,ha⟩) else .constant false
  | .pin j => if hj : (splitRow _ _ (P.pinRow j)).1 = lane then .pin ((I.ext.symm ⟨j,hj⟩).castAdd _) else .constant false

omit [CommSemiring F] in
private theorem translate_at (s : BitSource N.internal p) (g : Fin I.h → Bool) (pin : Fin p → Bool)
    (send recv : Tags offsets low slots → Bool) :
    (I.translate s).read g (I.inputs pin send recv) =
      s.read (P.padHidden lane (I.unpackHidden g)) (ownedPin (P:=P) (lane:=lane) pin) := by
  cases s with
  | constant => rfl
  | hidden a => by_cases h : (splitRow _ _ (P.hiddenRow a)).1 = lane <;>
      simp [translate,h,BitSource.read,padHidden,unpackHidden]
  | pin j => by_cases h : (splitRow _ _ (P.pinRow j)).1 = lane <;>
      simp [translate,h,BitSource.read,inputs,ownedPin]

def emission (u : Tags offsets low slots) : BitSource I.h I.arity :=
  match I.probe u with
  | none => .constant false
  | some a => I.translate (N.source a.val.1 a.val.2)

omit [CommSemiring F] in
private theorem emission_at (u : Tags offsets low slots) (g : Fin I.h → Bool) (pin : Fin p → Bool)
    (send recv : Tags offsets low slots → Bool) :
    (I.emission u).read g (I.inputs pin send recv) = P.emitted pin (P.padHidden lane (I.unpackHidden g)) lane u := by
  have same := P.emitted_local (ownedPin (P:=P) (lane:=lane) pin) pin
    (P.padHidden lane (I.unpackHidden g)) (P.padHidden lane (I.unpackHidden g)) lane
    (fun j hj => by simp [ownedPin,hj]) (fun _ _ => rfl)
  rw [←congrFun same u]
  cases hu : I.probe u with
  | none =>
    have missing : ¬∃ a, P.key a = (lane,u) := by rintro ⟨a,ha⟩; simpa [hu] using (I.probe_some u a).2 ha
    rw [P.emitted_unused _ _ _ _ missing]
    simp [emission,hu,BitSource.read]
  | some a =>
    have ha := (I.probe_some u a).1 hu
    have h1 : P.ownerLane a = lane := congrArg Prod.fst ha
    have h2 : P.tag a = u := congrArg Prod.snd ha
    have atSource := P.emitted_wire (ownedPin (P:=P) (lane:=lane) pin) (P.padHidden lane (I.unpackHidden g)) a
    rw [h1,h2] at atSource
    rw [atSource]
    simp only [emission,hu,I.translate_at]

noncomputable def argumentSource (c : Fin I.c) (j : Fin 3) : BitSource I.h I.arity :=
  let a := (I.cell c).val
  if hj : wired (N.source a j) then
    .pin (Fin.natAdd I.x (Fin.natAdd I.t (I.tag.symm (P.tag ⟨(a,j),hj⟩))))
  else .constant ((N.source a j).read (fun _ => false) (fun _ => false))

omit [CommSemiring F] in
private theorem argument_at (c : Fin I.c) (j : Fin 3) (g : Fin I.h → Bool) (pin : Fin p → Bool)
    (send recv : Tags offsets low slots → Bool) :
    (I.argumentSource c j).read g (I.inputs pin send recv) = P.argument recv (I.cell c).val j := by
  by_cases hj : wired (N.source (I.cell c).val j) <;>
    simp only [argumentSource,argument,hj,↓reduceDIte,BitSource.read,inputs,Fin.append_right,
      Function.comp_apply,Equiv.apply_symm_apply]

def testSource (i : Fin I.t) : Fin 3 → BitSource I.h I.arity :=
  ![.pin (Fin.natAdd I.x (i.castAdd I.t)),I.emission (I.tag i),.constant false]

noncomputable def network : BitNetwork F I.arity where
  internal := I.h
  cells := I.c+I.t
  source := Fin.append I.argumentSource I.testSource
  table := Fin.append (fun a => N.table (I.cell a).val) (fun _ z => if z 0 = z 1 then 1 else 0)

private theorem factor_gate (c : Fin I.c) (pin : Fin p → Bool) (g : Fin I.h → Bool)
    (send recv : Tags offsets low slots → Bool) :
    I.network.factor (I.inputs pin send recv) g (c.castAdd I.t) = N.table (I.cell c).val (P.argument recv (I.cell c).val) := by
  simp only [network,BitNetwork.factor,Fin.append_left,I.argument_at]

private theorem factor_test (a : Fin I.t) (pin : Fin p → Bool) (g : Fin I.h → Bool)
    (send recv : Tags offsets low slots → Bool) :
    I.network.factor (I.inputs pin send recv) g (Fin.natAdd I.c a) = if send (I.tag a) =
      P.emitted pin (P.padHidden lane (I.unpackHidden g)) lane (I.tag a) then 1 else 0 := by
  simp only [network,BitNetwork.factor,Fin.append_right,testSource,Matrix.cons_val_zero,Matrix.cons_val_one]
  let equal (x y : Bool) : F := if x=y then 1 else 0
  refine congrArg₂ equal ?_ (I.emission_at (I.tag a) g pin send recv)
  simp only [BitSource.read,inputs,Fin.append_right,Fin.append_left,Function.comp_apply]

theorem eval (pin : Fin p → Bool) (send recv : Tags offsets low slots → Bool) :
    I.network.eval (I.inputs pin send recv) = P.localTensor pin lane send recv := by
  let E : (Fin I.h → Bool) ≃ P.LocalHidden lane := Equiv.arrowCongr I.hidden (Equiv.refl _)
  unfold localTensor
  change (∑ g : Fin I.h → Bool, I.network.weight (I.inputs pin send recv) g) = _
  apply Fintype.sum_equiv E
  intro g
  change _ = P.bucket pin (P.padHidden lane (I.unpackHidden g)) lane send recv
  unfold BitNetwork.weight bucket
  refine (Fin.prod_univ_add (fun i : Fin (I.c+I.t) => I.network.factor (I.inputs pin send recv) g i)).trans ?_
  simp only [factor_gate,factor_test]
  have coeff := I.cell.prod_comp (fun a => N.table a.val (P.argument recv a.val))
  by_cases ok : send = P.emitted pin (P.padHidden lane (I.unpackHidden g)) lane
  · rw [ite_eq_left ok,coeff]
    simp [ok]
  · obtain ⟨u,hu⟩ := Function.ne_iff.mp ok
    have miss : send (I.tag (I.tag.symm u)) ≠ P.emitted pin (P.padHidden lane (I.unpackHidden g)) lane (I.tag (I.tag.symm u)) := by simpa using hu
    rw [ite_eq_right ok,Finset.prod_eq_zero (Finset.mem_univ (I.tag.symm u)) (ite_eq_right miss),mul_zero]

end BucketIndex
end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
