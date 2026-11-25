import OAI.Hierarchy.DescentPackedFlowPadding
import OAI.Hierarchy.DescentIssuedReset

namespace OAI
/-! # Old signed token and amount words at the public host and degree caps -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentColonies DescentGL DescentSIMDLookup DescentStageEdgeReceipt DescentPackedColony
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i h l m H N R D short b : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J≃Fin R) (hosts : V≃Fin H)
local notation "rs" => groups.toEmbedding.trans Fin.valEmbedding
local notation "vs" => hosts.toEmbedding.trans Fin.valEmbedding
local notation "Q" => A.wire*(A.z*G.b)
open DescentPackedFlowPair.Padded

def tokens (short : ℕ) (v : Fin N) (g : Fin R) (s : DescentPackedFlowRAM.Slot (2^k) (2*A.cap)) : Cell short :=
  (project H v).elim 0 (fun u=>chips A native S ready rs vs short (groups.symm g) (hosts.symm u) s)

theorem token_limit (short : ℕ) (u : V) (g : J) (s : DescentPackedFlowRAM.Slot (2^k) (2*A.cap)) :
    (chips A native S ready rs vs short g u s).val≤A.degree := by
  unfold chips
  generalize DescentSharedCableNames.Stage.signedPanel A native S ready
    (DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank rs vs))
    ((g,u),s.1) s.2 = entry
  cases entry with
  | none=>exact Nat.zero_le _
  | some p=>
    simp only [DescentPacking.PackedMatch.Local.Stage.marked]
    split
    · change (p.neighbor.val+1)%2^short ≤ A.degree
      exact (Nat.mod_le _ _).trans (Nat.succ_le_of_lt p.neighbor.isLt)
    · exact Nat.zero_le _

def flow (digits : Block m≃J×Block k) (j : Fin D) (v : Fin N) (x : Block m) :=
  (project H v).elim 0 (fun u=>(project A.degree j).elim 0 (fun i=>raw A hosts digits i u x))

def load (digits : Block m≃J×Block k) (v : Fin N) (x : Block m) :=
  (project H v).elim 0 (fun u=>A.resetLoad digits (hosts.symm u) x)

def roster (ph : H≤N) : Fin N→Fin D→Option (Fin N) :=
  DescentPackedFlowPair.Padded.next ph (PackedFlow.next A hosts)

theorem measured_cell (_ph : H≤N) (pd : A.degree≤D) (v : Fin N) (g : Fin R) (j : Fin D) (x : Block k) :
    Q*DescentPackedFlowRAM.counts (tokens A native S ready groups hosts short v g) j.val x=
      cells (weights A native S ready groups hosts short) v g j x := by
  unfold tokens cells
  cases host : project H v with
  | none=>
    simp only [Option.elim_none]
    have void : IsEmpty {s : Fin (2*A.cap) // ((0:Cell short).val)=j.val+1} :=
      ⟨fun z=>by have hz:=z.property;change 0=j.val+1 at hz;omega⟩
    let:=void
    simp [DescentPackedFlowRAM.counts]
  | some u=>
    simp only [Option.elim_some]
    cases slot : project A.degree j with
    | some t=>
      have bind:=project_some slot pd
      subst j
      rfl
    | none=>
      have far : A.degree≤j.val:=by by_contra! small;simp [project,small] at slot
      let tag:=chips A native S ready rs vs short (groups.symm g) (hosts.symm u)
      have void : IsEmpty {s : Fin (2*A.cap) // (tag (x,s)).val=j.val+1} :=
        ⟨fun z=>by have top:=token_limit A native S ready groups hosts short (hosts.symm u) (groups.symm g) (x,z.val)
                   have same:=z.property
                   change (tag (x,z.val)).val≤A.degree at top
                   omega⟩
      let:=void
      change Q*Fintype.card {s : Fin (2*A.cap) // (tag (x,s)).val=j.val+1}=0
      simp

theorem measured_amount (ph : H≤N) (pd : A.degree≤D) (ok : A.degree<2^short) (digits : Block m≃J×Block k)
    (v : Fin N) (j : Fin D) (x : Block m) :
    DescentPackedFlowPair.paid (roster A hosts ph) (fun u g t z=>
      Q*DescentPackedFlowRAM.counts (tokens A native S ready groups hosts short u g) t.val z)
      v (groups (digits x).1) j (digits x).2=flow A hosts digits j v x := by
  simp_rw [measured_cell A native S ready groups hosts ph pd]
  change DescentPackedFlowPair.paid (DescentPackedFlowPair.Padded.next ph (PackedFlow.next A hosts))
    (cells (weights A native S ready groups hosts short)) v (groups (digits x).1) j (digits x).2=
    flow A hosts digits j v x
  cases hs:project H v with
  | none=>rw [DescentPackedFlowPair.Padded.paid_at_ghost ph pd _ _ _ _ _ _ (.inl hs)];simp [flow,hs]
  | some u=>
    cases js:project A.degree j with
    | none=>rw [DescentPackedFlowPair.Padded.paid_at_ghost ph pd _ _ _ _ _ _ (.inr js)];simp [flow,hs,js]
    | some t=>
      have a:=project_some hs ph
      have b:=project_some js pd
      subst v j
      rw [DescentPackedFlowPair.Padded.paid_live ph pd]
      simpa only [flow,project_cast,Option.elim_some] using raw_at A native S ready groups hosts short ok digits t u x

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
