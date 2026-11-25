import OAI.Hierarchy.DescentPackedCensusFromSigned

namespace OAI
/-! # Exact natural-number load from the previous signed ports and funded count -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census
open DescentSixParty DescentSIMDLookup DescentColonies DescentSharedCableNames
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k age R H a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S age) (groups : J≃Fin R) (hosts : V↪Fin H)

private theorem occupied_count {n : ℕ} (line : Fin n→Cell 2) :
    (∑j,if line j=0 then 0 else 1)=PackedCensus.numLive line := by
  rw [PackedCensus.numLive,Finset.card_filter]
  exact Finset.sum_congr rfl (fun j _=>by by_cases h : line j=0 <;> simp [h])

theorem canvas_value (precision : A.wire*(A.z*G.b)*A.cap < 2^a)
    (h : Fin H) (g : Fin R) (x : Block k) :
    A.censusValue hosts groups false h g x =
      A.hist*(count A groups hosts a h g x).val +
      (A.wire*(A.z*G.b))*(if (hub A hosts h).val=0 then 1 else 256)*
        (∑j,if DescentSignedCableCodec.census (DescentSignedCableCodec.encode
          (Prepare.signed A native S ready groups.toEmbedding hosts x j h g))=0 then 0 else 1) := by
  classical
  by_cases real : ∃u,hosts u=h
  · let loc : J×V := (groups.symm g,real.choose)
    let addr := Stage.signed A native S ready loc x
    let pick := PackedCensus.portOfOut W A.pos A.block A.grainCount A.quantum_positive loc x
    let line := PackedCensus.tags (Finset.univ.map addr) (Finset.univ.map (pick.trans addr))
    have sub : Finset.univ.map (pick.trans addr) ⊆ Finset.univ.map addr := by
      rintro j hj
      obtain ⟨p,_,rfl⟩:=Finset.mem_map.mp hj
      exact Finset.mem_map.mpr ⟨pick p,Finset.mem_univ _,rfl⟩
    have ports : (∑j,if line j=0 then 0 else 1)=Fintype.card (A.CellPorts loc.1 loc.2 x) := by
      rw [occupied_count]
      simp only [line,PackedCensus.numLive_tags _ _ sub,Finset.card_map,Finset.card_univ]
    have observed (j : Fin (2*A.cap)) : DescentSignedCableCodec.census (DescentSignedCableCodec.encode
        (Prepare.signed A native S ready groups.toEmbedding hosts x j h g))=line j := by
      simp only [Prepare.signed,spread_index groups hosts,dite_eq_left real,DescentSignedCableCodec.census_at,
        Stage.census_tags]
      rfl
    let records := PackedCensus.histories W A.pos A.block A.records loc x
    have orig := PackedCensus.units W A.pos A.block A.grainCount (fun t=>A.hub t.2) A.records
      A.wire 256 A.hist (A.z*G.b) (A.grainCount_fit S ready) loc x
    have bound := orig.symm.trans_lt ((A.small loc x).trans_lt precision)
    have exactRecords : A.hist*(records:Cell a).val=A.hist*records := by
      by_cases free : A.hist=0
      · simp [free]
      · have le : records≤A.hist*records := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero free)
        have small : records < 2^a := le.trans_lt ((Nat.le_add_left _ _).trans_lt bound)
        rw [Fin.val_cast_of_lt small]
    simp only [GroupStage.censusValue,dite_eq_left real,Bool.false_eq_true,ite_false,hub,count,observed,ports]
    change _=A.hist*(records:Cell a).val+_
    rw [exactRecords]
    refine orig.trans ?_
    conv_lhs => rw [Nat.add_comm]
    apply congrArg (fun n : ℕ => A.hist*records+n)
    cases flag : A.hub real.choose <;> simp [loc]
  · simp [GroupStage.censusValue,count,hub,real,Prepare.signed,spread_index groups hosts,
      DescentSignedCableCodec.census_at,Stage.censusTag]

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census

end OAI
