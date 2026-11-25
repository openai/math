import OAI.Computability.BorderVNP.CubeTeamRawArenaRoles
import OAI.Computability.BorderVNP.CubeTeamOwnedReturn
import OAI.Computability.BorderVNP.CubeTeamRawDeclaration

/-! # Recovering distributed selector scans from the actual returned team programs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.CubeArena Physical Physical.Owned Scatter TeamRowSources TeamRowPrepare VPVNP.BurstRAM

variable {a : CubeArena.Layout} {teams w : ℕ} {decl : LengthDeclaration a.n a.header.d} {copies : 1 ≤ a.K}
variable {owner : Fin a.header.d → Fin teams} {frame : Fin teams → ℕ}
variable {pub : Fin teams → Arg → Word w} {mac : Fin teams → TeamOpcode.Macros w 8}
variable {original : Fin teams → Memory w} {raw : Symbols a.header.d → List Bool}

/-- The native group returns, physical frame words and the raw delivered prefixes give
the complete distributed scan. Every preservation assertion in the row induction is
obtained from the genuine scatter and checker of the reached branch. -/
theorem RawScans.of_physical
    (input : ∀ team : Fin teams, a.RawInputs (frame team) team.val decl copies (fun g => (owner g).val) (pub team) (original team))
    (views : ∀ team : Fin teams, a.RawPrefixes (frame team) team.val decl (fun g => (owner g).val) raw (original team))
    (returns : ∀ team, ∃ r es t mt, Runs (pub team) (mac team) (ownedGroups a.n a.b a.h a.K a.s) r (original team) es t mt) :
    Nonempty (RawScans owner pub mac decl raw a.header.blocks a.b a.h a.K a.s) := by
  let l (team : Fin teams) := a.scanner (frame team) team.val decl.1.val a.rowSelectorBits
  let num := fun g : Fin a.header.d => (owner g).val
  let old (team : Fin teams) (m : Memory w) := ∀ x ∈ source (l team) a.powerBase a.n, m x = original team x
  let J (team : Fin teams) (q : ℕ) (v : Word w) (m : Memory w) :=
    old team m ∧ v.val = a.vertexBase+3*vertexPrefix (l team) (wordOwner num) a.n a.header.blocks q
  have inventory (team : Fin teams) (m : Memory w) (same : old team m) :
      (l team).Fields (readings m) ∧ readings m ((l team).frame+78) = a.vertexBase ∧
        ∀ g < (l team).d, readings m ((l team).ownerBase+g) = wordOwner num g :=
    source_inventory (l := l team) (input team).fields (input team).directory (input team).owners same
  have visit (team : Fin teams) (q : ℕ) (hq : q < (l team).d*(l team).d)
      (owned : wordOwner num (q/(l team).d) = (l team).teamID) (r : Bank w) (m : Memory w) (same : old team m)
      (cursor : readings r 7 = a.vertexBase+3*vertexPrefix (l team) (wordOwner num) a.n a.header.blocks q)
      (prep : ReadyRow (l team) (readings m) q (.ofWords r m)) (es t mt)
      (run : Runs (pub team) (mac team)
        (if q/(l team).d = q%(l team).d then diagonalRole a.n a.b a.h a.K a.s else strictRole a.n a.b a.h a.K a.s) r m es t mt) :
      old team mt ∧ readings t 7 = readings r 7+(if q/(l team).d = q%(l team).d then 0 else 3*strictVertices a.n (l team).d a.header.blocks) ∧
        readings t 22 = q ∧ readings t 23 = (l team).d*(l team).d := by
    have obs := (input team).visit (views team) ⟨q,hq⟩ owned same cursor prep run
    exact ⟨fun x hx => (obs.1 x hx).trans (same x hx),obs.2⟩
  have advance (team : Fin teams) {q r m es t mt} (hq : q < (l team).d*(l team).d) (start : J team q (r 7) m)
      (prep : ReadyRow (l team) (readings m) q (.ofWords r m))
      (run : Visit (pub team) (mac team) (l team) (strictRole a.n a.b a.h a.K a.s)
        (diagonalRole a.n a.b a.h a.K a.s) q r m es t mt) : J team (q+1) (t 7) mt := by
    have bounded : q/(l team).d < (l team).d := (pairAt (l team).d ⟨q,hq⟩).1.isLt
    have word := (inventory team m start.1).2.2 _ bounded
    cases run with
    | skip miss =>
      have foreign : wordOwner num (q/(l team).d) ≠ (l team).teamID := fun h => miss (word.trans h)
      exact ⟨start.1,by simpa only [vertexPrefix,Finset.sum_range_succ,foreign,false_and,ite_false,Nat.add_zero] using start.2⟩
    | offDiagonal mine diff run =>
      have own := word.symm.trans mine
      have ret := visit team q hq own r m start.1 start.2 prep _ _ _ (by simpa only [ite_eq_right diff] using run)
      refine ⟨ret.1,?_⟩
      have v := ret.2.1
      change readings _ 7 = _
      rw [v,ite_eq_right diff,show readings r 7 = _ from start.2]
      simp only [vertexPrefix,Finset.sum_range_succ,own,diff,true_and,ne_eq,not_false_eq_true,ite_true,Nat.mul_add,Nat.add_assoc]
    | onDiagonal mine eq run =>
      have own := word.symm.trans mine
      have ret := visit team q hq own r m start.1 start.2 prep _ _ _ (by simpa only [ite_eq_left eq] using run)
      refine ⟨ret.1,?_⟩
      change readings _ 7 = _
      rw [ret.2.1,ite_eq_left eq,Nat.add_zero,show readings r 7 = _ from start.2]
      simp only [vertexPrefix,Finset.sum_range_succ,eq,ne_self_iff_false,and_false,ite_false,Nat.add_zero]
  have history (team : Fin teams) : ∃ z m rows gs u mu, J team 0 (z 7) m ∧ ReturnedRows (pub team) (mac team) (l team)
      (strictRole a.n a.b a.h a.K a.s) (diagonalRole a.n a.b a.h a.K a.s) 0 z m rows gs u mu := by
    obtain ⟨r,es,t,mt,run⟩ := returns team
    obtain ⟨H,zero,_⟩ := ownedGroups_return_induction a.n a.header.blocks a.b a.h a.K a.s
      (l team) (wordOwner num) (fun _ => old team) a.vertexBase (input team).fits (input team).seed.frame
      (fun _ _ => rfl) (fun _ => inventory team) (fun _ _ _ _ same => same) (visit team) run
    exact ⟨H.scanStart,original team,H.rows,H.rowEvents,H.afterScan,H.pre,⟨fun _ _ => rfl,by simpa [vertexPrefix,readings] using zero⟩,H.history⟩
  refine ⟨{
    scanLayout := l
    dimension := fun _ => rfl
    resident := J
    history := history
    advance := advance
    owns := ?_
    strict := ?_
    diagonal := ?_ }⟩
  · intro x y v m hs
    simpa only [wordOwner,dite_eq_left x.isLt,num,l,CubeArena.Layout.scanner] using (inventory (owner x) m hs.1).2.2 x.val x.isLt
  · intro p r m gs u mu start prep side
    let team := owner p.val.1
    have owned : num (oriented p false).1 = team.val := rfl
    obtain ⟨len,read⟩ := views team p false owned
    obtain ⟨word,_,_,_,_,S,eqn,stored⟩ := (input team).strictSide p false (raw p) owned start.1 start.2 prep
      len (read.congr start.1) side
    exact ⟨a.checkAddresses,word,S,eqn,stored⟩
  · intro g r m gs u mu start prep side
    exact ⟨a.checkAddresses,(input (owner g)).diagonalSide g start.1 prep side⟩

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
