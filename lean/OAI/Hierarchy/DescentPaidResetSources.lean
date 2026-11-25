import OAI.Hierarchy.DescentPaidResidentCensus
import OAI.Hierarchy.DescentPaidResetWindow
import OAI.Hierarchy.DescentRecipeGroupStage
import OAI.Hierarchy.DescentResetIssuedFallback

namespace OAI
/-! # Primary and relay populations from the previous funded chip and signed grain cells -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentColonies DescentSharedCableNames DescentSharedCableNames.Stage
open DescentHostDirectory DescentResetTrunks DescentSIMDLookup
open DescentSixParty.PackedCensus DescentSixParty.StarKeys
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m b H R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (native : W.graph.Edge↪ℕ) (names : Host J V k↪ℕ) (host : V↪Fin H) (groups : J≃Fin R)
local notation "Q" => (A.z*G.b)
set_option quotPrecheck false in
local notation "cost" => fun u : W.graph.Site=>(A.records u).length
local notation "fundedCount" => DescentPacking.PackedMatch.Local.Stage.Census.count A groups host b

include ready in
/-- The funded output at the previous group and block is exactly the old
weight used by the reset placement, in its flattened block coordinate. -/
theorem previous_paid (precision : A.wire*Q*A.cap<2^b) (digits : Block m≃J×Block k) (v : V) (x : Block m) :
    (fundedCount (host v) (groups (digits x).1) (digits x).2).val=
      ∑u : W.graph.Site,if (A.pos u).2=v ∧ filled W.graph A.pos A.block digits u=x then cost u else 0 := by
  have loc : ∃u,host u=host v:=⟨v,rfl⟩
  have same:=host.injective loc.choose_spec
  let t:=((digits x).1,v)
  let len:=histories W A.pos A.block A.records t (digits x).2
  have unit:=units W A.pos A.block A.grainCount (fun z=>A.hub z.2) A.records A.wire 256 A.hist Q
    (A.grainCount_fit S ready) t (digits x).2
  have costBound := unit.symm.le.trans (A.small t (digits x).2)
  have enough : len≤A.wire*Q*A.cap:=calc
    _ = 1*len := (Nat.one_mul _).symm
    _ ≤ A.hist*len := Nat.mul_le_mul_right _ ready.atom
    _ ≤ _ := (Nat.le_add_left _ _).trans costBound
  simp only [DescentPacking.PackedMatch.Local.Stage.Census.count,dite_eq_left loc,same,Equiv.symm_apply_apply]
  change ((len : Cell b).val) = _
  rw [Fin.val_cast_of_lt (enough.trans_lt precision)]
  exact (filled_mass W.graph A.pos A.block digits cost v x).symm

def arrivals (D cap : ℕ) (chip : Fin (2*cap)→Cell (DescentSignedCableCodec.width D cap)) : ℕ :=
  ∑j,((DescentSignedCableCodec.decode D cap (chip j)).any Stage.Live.target).toNat

theorem arrivals_true (p : Host J V k) (raw : Fin (2*A.cap)→Cell (DescentSignedCableCodec.width A.degree A.cap))
    (reads : ∀j,raw j=DescentSignedCableCodec.encode (Stage.signedPanel A native S ready names p j)) :
    arrivals A.degree A.cap raw=
      ∑e : W.graph.Edge,if A.pos (W.graph.dst e)=p.1 ∧ A.block (W.graph.dst e)=p.2 then A.grainCount e else 0 := by
  let place:=Stage.signed A native S ready p.1 p.2
  let get (j : Fin (2*A.cap)):=((DescentSignedCableCodec.decode A.degree A.cap (raw j)).any Stage.Live.target).toNat
  let paid : A.CellPorts p.1.1 p.1.2 p.2→ℕ:=Sum.elim (fun _=>0) (fun _=>1)
  let flag (j : Fin (2*A.cap)):=∃u,place u=j
  have hit (u : A.CellPorts p.1.1 p.1.2 p.2) : get (place u)=paid u := by
    simp only [get,reads,DescentSignedCableCodec.decode_encode,place,Stage.signed_read]
    cases u <;> rfl
  have supported (j) : get j=(if flag j then get j else 0) := by
    split
    · rfl
    · rename_i none
      have empty : ∀u,place u≠j:=fun u eqn=>none ⟨u,eqn⟩
      simp [get,reads,Stage.signed_empty A native S ready names p j empty]
  change (∑j,get j)=_
  calc
    _ = ∑j,if flag j then get j else 0 := Finset.sum_congr rfl (fun j _=>supported j)
    _ = ∑u,paid u := sum_image place paid flag get (fun _=>Iff.rfl) hit
    _ = Fintype.card (Ends W A.pos A.block A.grainCount W.graph.dst p.1 p.2) := by
      change (∑u : _ ⊕ _, Sum.elim (fun _=>0) (fun _=>(1:ℕ)) u)=_
      simp [Fintype.sum_sum_type]
    _ = _ := ends_eq W A.pos A.block A.grainCount W.graph.dst p.1 p.2

/-- A signed loop contributes once to the true incoming incidence, even though
its source row and its receiving row occur in the same physical group. -/
theorem previous_relay (digits : Block m≃J×Block k) (v : V) (x : Block m)
    (raw : Fin (2*A.cap)→Cell (DescentSignedCableCodec.width A.degree A.cap))
    (reads : ∀j,raw j=DescentSignedCableCodec.encode (Stage.signedPanel A native S ready names (( (digits x).1,v),(digits x).2) j)) :
    arrivals A.degree A.cap raw=∑e : W.graph.Edge,if (A.pos (W.graph.dst e)).2=v ∧
        filled W.graph A.pos A.block digits (W.graph.dst e)=x then A.grainCount e else 0 := by
  rw [arrivals_true A S ready native names _ raw reads]
  apply Finset.sum_congr rfl
  intro e _
  have where_ : ((A.pos (W.graph.dst e))=((digits x).1,v) ∧ A.block (W.graph.dst e)=(digits x).2) ↔
      (A.pos (W.graph.dst e)).2=v ∧ filled W.graph A.pos A.block digits (W.graph.dst e)=x := by
    constructor
    · rintro ⟨h,k⟩
      refine ⟨congrArg Prod.snd h,?_⟩
      apply digits.injective
      simpa only [filled,Equiv.apply_symm_apply] using (show ((A.pos (W.graph.dst e)).1,A.block (W.graph.dst e))=digits x from Prod.ext (congrArg (fun z : J×V=>z.1) h) k)
    · rintro ⟨h,k⟩
      have coords := congrArg digits k
      simp only [filled,Equiv.apply_symm_apply] at coords
      exact ⟨Prod.ext (congrArg (fun z : J×Block _=>z.1) coords) h,congrArg (fun z : J×Block _=>z.2) coords⟩
  simp only [where_]

def fiberGrains {E T : Type} (count : E→ℕ) (loc : E→T) (t : T) :
    {e : Σe : E,Fin (count e) //loc e.1=t} ≃ (Σe : {e : E //loc e=t}, Fin (count e.val)) where
  toFun x:=⟨⟨x.val.1,x.property⟩,x.val.2⟩
  invFun x:=⟨⟨x.1.val,x.2⟩,x.1.property⟩
  left_inv:=by rintro ⟨⟨_,_⟩,_⟩;rfl
  right_inv:=by rintro ⟨⟨_,_⟩,_⟩;rfl

theorem grain_total {E V : Type} [Fintype E] (count : E→ℕ) (loc : E→V) (v : V) :
    Fintype.card {e : Σe : E,Fin (count e) //loc e.1=v}=∑e : {e : E //loc e=v},count e.val := by
  rw [Fintype.card_congr (fiberGrains count loc v),Fintype.card_sigma];simp

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
