import OAI.Hierarchy.DescentHostRosterOrder
import OAI.Hierarchy.DescentDatedVenueSources
import OAI.Hierarchy.DescentPackedMatchLiveAmount

namespace OAI
/-! # Read matching neighbors from the very roster that named the signed old cable -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentHostDirectory DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSharedCableNames DescentSIMDLookup
open scoped Classical
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (rank : (J×V)↪ℕ)

def neighbors (h : J×V) := groupedNear A.near h
theorem nb_room (h : J×V) : (neighbors A h).card≤A.degree := (grouped_degree A.near h).le.trans (A.degreeBound h.2)

def ordinal (h : J×V) := Ends.neighborOrder (neighbors A) rank (nb_room A) h

def rotor (h : J×V) (j : Fin A.degree) : Option (J×V) :=
  if live : ∃v,ordinal A rank h v=j then some live.choose.val else none

theorem rotor_at (h : J×V) (v : ↥(neighbors A h)) : rotor A rank h (ordinal A rank h v)=some v.val := by
  let embed := ordinal A rank h
  have hit : ∃ w, embed w = embed v := ⟨v, rfl⟩
  unfold rotor
  rw [dite_eq_left hit, embed.injective hit.choose_spec]

theorem rotor_sorted : RosterSorted A (rotor A rank) rank := by
  intro h j t l z pj pl
  unfold rotor at pj pl
  split at pj <;> try contradiction
  rename_i one
  split at pl <;> try contradiction
  rename_i two
  have hj := one.choose_spec;have hl := two.choose_spec
  cases pj;cases pl
  have ordered (u v : ↥(neighbors A h)) :
      ((ordinal A rank h) u).val < ((ordinal A rank h) v).val ↔ rank u.val < rank v.val := by
    let roster := (neighbors A h).map rank
    let index := (roster.orderIsoOfFin rfl).symm
    let tag (b : ↥(neighbors A h)) : ↥roster := ⟨rank b.val, Finset.mem_map.mpr ⟨b.val,b.property,rfl⟩⟩
    change index (tag u) < index (tag v) ↔ tag u < tag v
    exact index.lt_iff_lt
  have same := congrArg₂ (fun (x y : Fin A.degree) => x.val < y.val) hj.symm hl.symm
  have pair := ordered one.choose two.choose
  exact ⟨fun lt => pair.mp (same.mp lt), fun lt => same.mpr (pair.mpr lt)⟩

theorem paired (h : J×V) (x : Fin (2^k)) (v : ↥(neighbors A h)) :
    Ends.neighborOrder (DescentSharedCableNames.Stage.near A) (cableNames k rank) (DescentSharedCableNames.Stage.near_room A)
      (h,x) ⟨(v.val,x),Finset.mem_map.mpr ⟨v.val,v.property,rfl⟩⟩=ordinal A rank h v := by
  apply Fin.ext
  rw [nb_val,ordinal,nb_val]
  let put := DescentSharedCableNames.Stage.putAt (J:=J) (V:=V) x
  have equal : ((DescentSharedCableNames.Stage.near A (h,x)).filter (fun t=>cableNames k rank t<cableNames k rank (v.val,x)))=
      (((neighbors A h).filter (fun t=>rank t<rank v.val)).map put) := by
    ext t
    simp only [DescentSharedCableNames.Stage.near,Finset.mem_filter,Finset.mem_map,neighbors]
    constructor
    · rintro ⟨⟨z,mem,rfl⟩,less⟩
      refine ⟨z,⟨mem,?_⟩,rfl⟩
      change rank z*2^k+x.val<rank v.val*2^k+x.val at less
      exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_add_lt_add_right less)
    · rintro ⟨z,⟨mem,less⟩,rfl⟩
      exact ⟨⟨z,mem,rfl⟩,Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right less (Nat.two_pow_pos k)) _⟩
  rw [equal,Finset.card_map]

theorem rotor_routes : Routes A native S ready (cableNames k rank) (rotor A rank) := by
  intro h x e
  let z := A.pos (W.graph.dst e.val)
  have wz : z∈neighbors A h := by rw [←e.property.1.1];exact (A.peers e.val).1
  let p := PackedCensus.portOfOut W A.pos A.block A.grainCount A.quantum_positive h x e
  let j := DescentSharedCableNames.Stage.ofPort A native (h,x) p
  let B := DescentSharedCableNames.Stage.source A native
  have incidence : B.peer (h,x) j.val = (z,x) := by
    let grain : DescentSharedCableNames.Stage.Grain A :=
      ⟨e.val, ⟨0, A.quantum_positive e.val e.property.2⟩⟩
    have wire : j.val = DescentSharedCableNames.Stage.stream A native grain := rfl
    have original : ((DescentSharedCableNames.Stage.stream A native).symm j.val).1 = e.val := by
      rw [wire, Equiv.symm_apply_apply]
    have src : B.src j.val = (h,x) := by
      change DescentSharedCableNames.Stage.home A
        (W.graph.src ((DescentSharedCableNames.Stage.stream A native).symm j.val).1) = (h,x)
      rw [original]
      exact Prod.ext e.property.1.1 e.property.1.2
    have dst : B.dst j.val = (z,x) := by
      change DescentSharedCableNames.Stage.home A
        (W.graph.dst ((DescentSharedCableNames.Stage.stream A native).symm j.val).1) = (z,x)
      rw [original]
      exact Prod.ext rfl ((A.same e.val).symm.trans e.property.1.2)
    exact (ite_eq_left src).trans dst
  have slot : target A native S ready (cableNames k rank) (h,x) e=ordinal A rank h ⟨z,wz⟩ := by
    change Ends.neighborOrder (DescentSharedCableNames.Stage.near A) (cableNames k rank) _ (h,x) ⟨B.peer (h,x) j.val,_⟩=_
    convert paired A rank h x ⟨z,wz⟩ using 2
    exact Subtype.ext incidence
  rw [slot,rotor_at]

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
