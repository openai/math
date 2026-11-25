import OAI.Hierarchy.DescentOrdinaryGrainPorts
import OAI.Hierarchy.DescentNextSignedRAM

namespace OAI
/-! # Physical coverage of both end roles, normalized child offsets, and padding -/
namespace Hierarchy.DescentNextSignedWindow
open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase
open scoped Classical
noncomputable section
variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] [Fintype E]
  {d k i c : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : DescentSharedCableNames.Stage.Host J V k↪ℕ)
local notation "B" => DescentSharedCableNames.Stage.source A native
variable (C : Blocks (DescentSharedCableNames.Stage.source A native) E) (h : DescentSharedCableNames.Stage.Host J V k)
local notation "ports" => A.CellPorts (Prod.fst (Prod.fst h)) (Prod.snd (Prod.fst h)) (Prod.snd h)
local notation "address" => DescentSharedCableNames.Stage.signed A native S ready (Prod.fst h) (Prod.snd h)
local notation "live" => DescentSharedCableNames.Stage.live A native S ready names h
local notation "panel" => DescentSharedCableNames.Stage.signedPanel A native S ready names h
variable (row : Fin c→Option (Record A.degree A.cap))

/-- Every occupied row contributes exactly its literal count of normalized
children. Its storage ordinal and its relative child index are separate. -/
abbrev Occupied := {a : Fin c×ℕ // ∃r,row a.1=some r ∧ a.2<r.count}

def data (z:Occupied A row) : Record A.degree A.cap:=z.property.choose

theorem stored (z:Occupied A row) : row z.val.1=some (data A row z) ∧ z.val.2<(data A row z).count:=z.property.choose_spec

omit [Fintype E] in
/-- Convert the two locally supplied numeric addresses and the literal
six fields to the two selection clauses of the signed SRAM publisher. -/
theorem complete (physical : GrainPorts.Unit A native C h≃Occupied A row)
    (index : ∀ t,let z:=physical t; (address (GrainPorts.port A native C h t)).val =
      number A.cap (data A row z).side (data A row z).position + z.val.2)
    (metadata : ∀t,let z:=physical t;render (data A row z) z.val.2=some (live (GrainPorts.port A native C h t))) (j:Fin (2*A.cap)):
    (panel j=none→∀a,(row a).bind (fun r=>read r j)=none) ∧
    (∀q,panel j=some q→∃a,(row a).bind (fun r=>read r j)=some q ∧ ∀b,b≠a→(row b).bind (fun r=>read r j)=none):=by
  let make:=GrainPorts.equiv A native C h
  have truth (z:Occupied A row) :
      (address (make (physical.symm z))).val=number A.cap (data A row z).side (data A row z).position+z.val.2 ∧
      render (data A row z) z.val.2=some (live (make (physical.symm z))):=by
    constructor
    · change (address (GrainPorts.port A native C h (physical.symm z))).val = _
      simpa only [Equiv.apply_symm_apply] using index (physical.symm z)
    · change _ = some (live (GrainPorts.port A native C h (physical.symm z)))
      simpa only [Equiv.apply_symm_apply] using metadata (physical.symm z)
  have miss (a:Fin c) (away:∀z:Occupied A row,z.val.1=a→ address (make (physical.symm z))≠j):
      (row a).bind (fun r=>read r j)=none:=by
    cases value:row a with
    | none=>rfl
    | some r=>
      apply outside;intro off eqn
      let z : Occupied A row:=⟨(a,off.val),r,value,off.isLt⟩
      have table : data A row z=r:=Option.some.inj ((stored A row z).1.symm.trans value)
      exact away z rfl (Fin.ext (by rw [(truth z).1,table];exact eqn.symm))
  constructor
  · intro empty a;apply miss a;intro z _ eqn
    have test:=DescentSharedCableNames.Stage.signed_read A native S ready names h (make (physical.symm z))
    rw [eqn,empty] at test;contradiction
  · intro q hit
    obtain ⟨p,at_⟩ : ∃p:ports,address p=j:=by
      by_contra! absent
      rw [DescentSharedCableNames.Stage.signed_empty A native S ready names h j absent] at hit;contradiction
    let z:=physical (make.symm p)
    have original:make (physical.symm z)=p:=by simp [z]
    have eqn:live p=q:=Option.some.inj ((DescentSharedCableNames.Stage.signed_read A native S ready names h p).symm.trans (by simpa only [at_] using hit))
    refine ⟨z.val.1,?_,?_⟩
    · rw [(stored A row z).1];change read (data A row z) j=some q
      rw [indexed _ ⟨z.val.2,(stored A row z).2⟩ _ (by rw [←(truth z).1,original,at_])]
      simpa only [original,eqn] using (truth z).2
    · intro b diff;apply miss b;intro y yslot yj
      have same:=(address).injective (yj.trans at_.symm)
      have sy : y=z:=physical.symm.injective (make.injective (same.trans original.symm))
      exact diff (yslot ▸ congrArg (fun u : Occupied A row=>u.val.1) sy)

end
end Hierarchy.DescentNextSignedWindow

end OAI
