import OAI.Hierarchy.DescentUniqueAperture
import OAI.Hierarchy.DescentFineTerminals

namespace OAI
/-! # The true selected fallback leaf as a bounded list of public candidate tests -/

namespace Hierarchy.DescentFallbackLeafScan
open DescentContacts DescentFineTerminals
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {Y k D g f Δ cap : ℕ}
variable (near : V→Finset V) (hub : V→Bool)
def localShape (k D g f : ℕ) (source : Endpoint Y) (peerHub : Bool) : Finset (Endpoint Y) :=
  if source.2.isSome then fromNonhub Y source.1.1 source.1.2 D (k-g) peerHub
  else terminals Y (possible (k-g) source.1.2 D (g-f))

omit [Fintype V] in
theorem local_mem (source : V×Endpoint Y) (v : V) (p : Endpoint Y) :
    (v,p)∈window (k:=k) (D:=D) (g:=g) (f:=f) near hub source ↔
      v∈near source.1 ∧ p∈localShape k D g f source.2 (hub v) := by
  unfold window localShape
  split <;> simp [names]

/-- This enumeration involves only a fixed public old-block shape and a single
hub bit. Both possibilities are integer constants in the compiled table. -/
def localSlot (shapes : Finset (Endpoint Y)) (q : Fin cap) : Option (Endpoint Y) :=
  if valid : q.val<Fintype.card ↥shapes then some (((Fintype.equivFin ↥shapes).symm ⟨q.val,valid⟩).val) else none

theorem localSlot_some {shapes : Finset (Endpoint Y)} {q : Fin cap} {x : Endpoint Y} :
    localSlot shapes q=some x ↔ ∃allowed : x∈shapes,(Fintype.equivFin ↥shapes ⟨x,allowed⟩).val=q.val := by
  unfold localSlot
  split
  · rename_i valid
    constructor
    · intro h
      let a:=(Fintype.equivFin ↥shapes).symm ⟨q.val,valid⟩
      obtain eq:=Option.some.inj h
      subst x
      exact ⟨a.property,congrArg Fin.val ((Fintype.equivFin ↥shapes).apply_symm_apply _)⟩
    · rintro ⟨allowed,num⟩
      have index : (⟨q.val,valid⟩ : Fin (Fintype.card ↥shapes))=Fintype.equivFin ↥shapes ⟨x,allowed⟩ :=
        Fin.ext num.symm
      have same := (Fintype.equivFin ↥shapes).symm_apply_eq.mpr index
      exact congrArg some (congrArg Subtype.val same)
  · rename_i off
    simp only [reduceCtorEq,false_iff]
    rintro ⟨allowed,h⟩
    exact off (h ▸ (Fintype.equivFin ↥shapes ⟨x,allowed⟩).isLt)

variable (peer : V→Fin Δ→Option V)
def candidate (source : V×Endpoint Y) (j : Fin Δ×Fin cap) : Option (V×Endpoint Y) := do
  let v←first peer source.1 j.1
  let x←localSlot (localShape k D g f source.2 (hub v)) j.2
  return (v,x)

local notation "cand" => candidate (k:=k) (D:=D) (g:=g) (f:=f) (cap:=cap) hub peer
local notation "seen" => window (k:=k) (D:=D) (g:=g) (f:=f) near hub

omit [Fintype V] in
theorem candidate_some {source : V×Endpoint Y} {j : Fin Δ×Fin cap} {v : V} {p : Endpoint Y} :
    cand source j=some (v,p) ↔ first peer source.1 j.1=some v ∧
      localSlot (localShape k D g f source.2 (hub v)) j.2=some p := by
  unfold candidate
  cases h : first peer source.1 j.1 with
  | none=>simp
  | some u=>
    cases q : localSlot (localShape k D g f source.2 (hub u)) j.2 with
    | none=>by_cases eqn : u=v <;> simp_all
    | some y=>by_cases eqn : u=v <;> simp_all

variable (real : ∀v x,x∈near v ↔ ∃j,peer v j=some x)

include real in
omit [Fintype V] in
theorem candidate_covers {source : V×Endpoint Y} (room : (seen source).card≤cap) (v : V) (p : Endpoint Y) :
    (∃j : Fin Δ×Fin cap,cand source j=some (v,p)) ↔ (v,p)∈seen source := by
  rw [local_mem near hub]
  constructor
  · rintro ⟨j,h⟩
    obtain ⟨one,two⟩:=(candidate_some hub peer).mp h
    exact ⟨(real ..).mpr ⟨j.1,first_real peer one⟩,((localSlot_some).mp two).choose⟩
  · rintro ⟨good,shape⟩
    obtain ⟨i,one⟩:=first_one peer _ _ ((real ..).mp good)
    let a:=localShape k D g f source.2 (hub v)
    let ix:=Fintype.equivFin ↥a ⟨p,shape⟩
    have small : a.card≤(seen source).card :=
      Finset.card_le_card_of_injOn (fun p=>(v,p))
        (fun p hp=>(local_mem near hub source v p).mpr ⟨good,hp⟩) (fun _ _ _ _ h=>congrArg Prod.snd h)
    have fit : ix.val<cap := ix.isLt.trans_le (by rw [Fintype.card_coe];exact small.trans room)
    exact ⟨(i,⟨ix.val,fit⟩),(candidate_some hub peer).mpr ⟨one,localSlot_some.mpr ⟨shape,rfl⟩⟩⟩

omit [Fintype V] in
theorem candidate_once {source : V×Endpoint Y} {i j : Fin Δ×Fin cap} {v : V} {p : Endpoint Y}
    (hi : cand source i=some (v,p)) (hj : cand source j=some (v,p)) : i=j := by
  obtain ⟨a,b⟩:=(candidate_some hub peer).mp hi
  obtain ⟨c,d⟩:=(candidate_some hub peer).mp hj
  obtain ⟨hb,ib⟩:=localSlot_some.mp b
  obtain ⟨hd,jb⟩:=localSlot_some.mp d
  exact Prod.ext (first_unique peer a c) (Fin.ext (ib.symm.trans jb))

include real in
omit [Fintype V] in
theorem scan_card (source : V×Endpoint Y) (room : (seen source).card≤cap) (test : V×Endpoint Y→Bool) :
    (Finset.univ.filter (fun j : Fin Δ×Fin cap=>(cand source j).any test)).card=
      (Finset.univ.filter (fun p : ↥(seen source)=>test p.val)).card := by
  let good (j : Fin Δ×Fin cap) := (cand source j).any test
  let get (j : Fin Δ×Fin cap) (passed : good j=true) : V×Endpoint Y :=
    (cand source j).get (by cases eqn : cand source j <;> simp_all [good])
  have read (j) (ok : good j=true) : cand source j=some (get j ok) := (Option.some_get _).symm
  have keep (j) (ok : good j=true) : get j ok∈seen source :=
    (candidate_covers near hub peer real room _ _).mp ⟨j,read j ok⟩
  apply Finset.card_bij (fun j h=>⟨get j (Finset.mem_filter.mp h).2,keep j (Finset.mem_filter.mp h).2⟩)
  · intro j h
    have ok:=(Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by change (cand source j).any test=true at ok; rwa [read j ok] at ok⟩
  · intro i hi j hj same
    have left : good i=true := (Finset.mem_filter.mp hi).2
    have right : good j=true := (Finset.mem_filter.mp hj).2
    have eqn : get i left=get j right := congrArg Subtype.val same
    exact candidate_once hub peer (v:=(get j right).1) (p:=(get j right).2)
      ((read i left).trans (congrArg some eqn)) (read j right)
  · intro t ht
    obtain ⟨j,hj⟩:=(candidate_covers near hub peer real room t.val.1 t.val.2).mpr t.property
    have hit : good j=true := by simpa [good,hj] using (Finset.mem_filter.mp ht).2
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩,Subtype.ext ?_⟩
    exact Option.some.inj ((read j hit).symm.trans hj)

end
end Hierarchy.DescentFallbackLeafScan

end OAI
