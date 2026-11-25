import OAI.Hierarchy.DescentPackedMatchSourceChart
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Physical packed selector seats, including the final chunk's unused lanes -/

namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentStageEdgeReceipt DescentHostDirectory DescentSIMDLookup
open ThreeFlat.Routing
open scoped Classical
noncomputable section
variable {Q J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {H G k M : ℕ}

def seatOf (k : ℕ) (address : Q↪(J×V)×(ℕ×ℕ)) (legal : ∀q,thickKey (address q)∈keys k 1)
    (groupName : J↪Fin G) (vertexName : V↪Fin H) (hm : 0<M) : Q↪Fin (2^(k+1)*(H*chunks G M))×Fin M := by
  let law (q : Q) : (address q).2∈codes k := (Finset.mem_product.mp (Finset.mem_product.mp (legal q)).2).1
  let key (q : Q) : Fin (2^(k+1)) := ⟨heap (address q).2,heap_fits (law q)⟩
  let word (q : Q) := row H G M (position (vertexName (address q).1.2) (groupName (address q).1.1) hm)
  exact ⟨fun q=>(finProdFinEquiv (key q,word q),lane (groupName (address q).1.1) hm),by
    intro x y same
    have ord := finProdFinEquiv.injective (congrArg Prod.fst same)
    have location := (row H G M).injective (congrArg Prod.snd ord)
    have block := congrArg (fun p : Row H G M=>p.2.val) location
    have residue := congrArg (fun t : Fin M=>t.val) (congrArg Prod.snd same)
    have full : (groupName (address x).1.1).val=(groupName (address y).1.1).val := by
      let a := (groupName (address x).1.1).val
      let b := (groupName (address y).1.1).val
      change a/M=b/M at block
      change a%M=b%M at residue
      exact (Nat.div_add_mod' a M).symm.trans (by rw [block,residue,Nat.div_add_mod'])
    exact address.injective (Prod.ext (Prod.ext (groupName.injective (Fin.ext full))
      (vertexName.injective (congrArg Prod.fst location))) (heap_inj (law x) (law y) (congrArg Fin.val (congrArg Prod.fst ord))))⟩

omit [DecidableEq J] [DecidableEq V] in
theorem seatOf_word (k : ℕ) (address : Q↪(J×V)×(ℕ×ℕ)) (legal : ∀q,thickKey (address q)∈keys k 1)
    (groupName : J↪Fin G) (vertexName : V↪Fin H) (hm : 0<M) (q : Q) :
    ((seatOf k address legal groupName vertexName hm q).1).val=heap (address q).2*(H*chunks G M)+
      (row H G M (position (vertexName (address q).1.2) (groupName (address q).1.1) hm)).val := by
  change _+H*chunks G M*heap (address q).2=_
  ring

omit [DecidableEq J] [DecidableEq V] in
theorem seatOf_val (k : ℕ) (address : Q↪(J×V)×(ℕ×ℕ)) (legal : ∀q,thickKey (address q)∈keys k 1)
    (groupName : J↪Fin G) (vertexName : V↪Fin H) (hm : 0<M) (q : Q) :
    let pos:=seatOf k address legal groupName vertexName hm q
    pos.1.val*M+pos.2.val=(heap (address q).2*H+(vertexName (address q).1.2).val)*(chunks G M*M)+(groupName (address q).1.1).val := by
  let g := (groupName (address q).1.1).val
  dsimp only
  rw [seatOf_word]
  change (heap (address q).2*(H*chunks G M)+(g/M+(chunks G M)*(vertexName (address q).1.2).val))*M+g%M=_
  have split := Nat.div_add_mod' g M
  nlinarith only [split]

private theorem lexRadix (b u v x y : ℕ) (hx : x<b) (hy : y<b) :
    u*b+x<v*b+y ↔ u<v ∨ u=v ∧ x<y := by
  have strict {i j a z : ℕ} (h : i<j) (small : a<b) : i*b+a<j*b+z := by
    have s := Nat.mul_le_mul_right b h
    rw [Nat.succ_mul] at s
    omega
  constructor
  · intro lt
    rcases lt_trichotomy u v with h|h|h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      subst v
      exact Nat.lt_of_add_lt_add_left lt
    · exact False.elim ((not_lt_of_ge lt.le) (strict h hy))
  · rintro (h|⟨rfl,h⟩)
    · exact strict h hx
    · omega

omit [DecidableEq J] [DecidableEq V] in
theorem seatOf_order (k : ℕ) (address : Q↪(J×V)×(ℕ×ℕ)) (legal : ∀q,thickKey (address q)∈keys k 1)
    (groupName : J↪Fin G) (vertexName : V↪Fin H) (hm : 0<M) (x y : Q) :
    let p:=seatOf k address legal groupName vertexName hm
    let c:=chartOf k address legal groupName vertexName
    (p x).1.val*M+(p x).2.val<(p y).1.val*M+(p y).2.val ↔ c x<c y := by
  dsimp only
  have cap : G≤chunks G M*M := by
    simpa only [chunks,Nat.mul_comm M] using CallPool.count_le_batches_mul G M hm
  change _ ↔ (chartOf k address legal groupName vertexName x).val<(chartOf k address legal groupName vertexName y).val
  rw [seatOf_val,seatOf_val,chartOf_val,chartOf_val,lexRadix _ _ _ _ _ ((groupName _).isLt.trans_le cap) ((groupName _).isLt.trans_le cap),
    lexRadix _ _ _ _ _ (groupName _).isLt (groupName _).isLt]

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {Gadget : PoweredGadget F} {price ε : ℝ}

def sourceSeat (he : 0≤ε) (A : GroupStage W Gadget price ε J V k) (groupName : J↪Fin G) (vertexName : V↪Fin H) (hm : 0<M) :
    ScanColonies he A.stage ↪ Fin (2^(k+1)*(H*chunks G M))×Fin M :=
  seatOf k (nativeAddress he A.stage) (nativeAddress_legal he A.stage) groupName vertexName hm

end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
