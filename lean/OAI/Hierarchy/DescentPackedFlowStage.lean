import OAI.Hierarchy.DescentPackedFlowPair
import OAI.Hierarchy.DescentPackedFlowRoster

namespace OAI
/-! # Old measured group traffic at the reset Walsh input -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentGL DescentColonies DescentSIMDLookup DescentStageEdgeReceipt
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m H R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J≃Fin R) (hosts : V≃Fin H)
local notation "rs" => groups.toEmbedding.trans Fin.valEmbedding
local notation "vs" => hosts.toEmbedding.trans Fin.valEmbedding
local notation "Q" => A.wire*(A.z*G.b)
local notation "place" => socket A vs

def next (v : Fin H) (j : Fin A.degree) : Option (Fin H) :=
  let h:=hosts.symm v
  if hit : ∃b,place h b=j then some (hosts hit.choose.val) else none

theorem next_at (v : V) (u : ↥(A.near v)) :
    next A hosts (hosts v) (place v u)=some (hosts u.val) := by
  have atHost (h : Fin H) (z : V) (same : hosts.symm h=z) (a : ↥(A.near z)) :
      next A hosts h (place z a)=some (hosts a.val) := by
    subst z
    have exists_ : ∃b,place (hosts.symm h) b=place (hosts.symm h) a := ⟨a,rfl⟩
    simp only [next,dite_eq_left exists_,(place (hosts.symm h)).injective exists_.choose_spec]
  exact atHost (hosts v) v (hosts.symm_apply_apply v) u

theorem next_unique {u v : V} (a b : Fin A.degree)
    (first : next A hosts (hosts v) a=some (hosts u)) (second : next A hosts (hosts v) b=some (hosts u)) : a=b := by
  simp only [next] at first second
  split at first <;> try contradiction
  rename_i ha
  split at second <;> try contradiction
  rename_i hb
  have same : ha.choose=hb.choose:=Subtype.ext (hosts.injective ((Option.some.inj first).trans (Option.some.inj second).symm))
  exact ha.choose_spec.symm.trans ((congrArg _ same).trans hb.choose_spec)

def weights (short : ℕ) (v : Fin H) (g : Fin R) (j : Fin A.degree) (x : Block k) :=
  Q*DescentPackedFlowRAM.counts (chips A native S ready rs vs short (groups.symm g) (hosts.symm v)) j.val x

theorem measured (short : ℕ) (ok : A.degree<2^short) (digits : Block m≃J×Block k)
    (v u : V) (peer : u∈A.near v) (x : Block m) :
    DescentPackedFlowPair.paid (next A hosts) (weights A native S ready groups hosts short)
      (hosts v) (groups (digits x).1) (place v ⟨u,peer⟩) (digits x).2 =
    pairLoad (W.countWorld A.grainCount) (fun t=>(A.pos t).2) (StarKeys.filled W.graph A.pos A.block digits)
      Q v u x := by
  have reverse : v∈A.near u:=(A.symmetric v u).mp peer
  let a : ↥(A.near v):=⟨u,peer⟩
  let b : ↥(A.near u):=⟨v,reverse⟩
  rw [DescentPackedFlowPair.paid_at _ _ _ _ _ _ (place u b) _ (next_at A hosts v a)
    (next_at A hosts u b) (fun j read=>next_unique A hosts j _ read (next_at A hosts u b)),
    pair_issued A digits v u x]
  simp only [weights,Equiv.symm_apply_apply]
  rw [chip_count A native S ready rs vs short ok _ v a,chip_count A native S ready rs vs short ok _ u b]

theorem absent (short : ℕ) (ok : A.degree<2^short) (v : V) (g : J) (j : Fin A.degree)
    (empty : next A hosts (hosts v) j=none) (x : Block k) :
    DescentPackedFlowPair.paid (next A hosts) (weights A native S ready groups hosts short)
      (hosts v) (groups g) j x=0 := by
  have unusedSocket (a : ↥(A.near v)) : place v a≠j := by
    intro eqn
    have live:=next_at A hosts v a
    rw [eqn,empty] at live
    contradiction
  simp [DescentPackedFlowPair.paid,DescentPackedFlowReturn.back,empty,weights,
    unused A native S ready rs vs short ok g v j unusedSocket x]

def raw (digits : Block m≃J×Block k) (j : Fin A.degree) (v : Fin H) (x : Block m) :=
  (next A hosts v j).elim 0 (fun u=>pairLoad (W.countWorld A.grainCount)
    (fun t=>(A.pos t).2) (StarKeys.filled W.graph A.pos A.block digits) Q (hosts.symm v) (hosts.symm u) x)

theorem raw_at (short : ℕ) (ok : A.degree<2^short) (digits : Block m≃J×Block k)
    (j : Fin A.degree) (v : Fin H) (x : Block m) :
    DescentPackedFlowPair.paid (next A hosts) (weights A native S ready groups hosts short)
      v (groups (digits x).1) j (digits x).2=raw A hosts digits j v x := by
  let u:=hosts.symm v
  have same : hosts u=v:=hosts.apply_symm_apply v
  by_cases hit : ∃a : ↥(A.near u),place u a=j
  · let a:=hit.choose
    have socketEq : place u a=j:=hit.choose_spec
    have points:=next_at A hosts u a
    rw [socketEq,same] at points
    simpa [raw,points,socketEq,same,u] using measured A native S ready groups hosts short ok digits u a.val a.property x
  · have miss : next A hosts v j=none:=by simp [next,u,hit]
    rw [raw,miss]
    simpa [same] using absent A native S ready groups hosts short ok u (digits x).1 j (same.symm ▸ miss) (digits x).2

end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
