import OAI.Hierarchy.DescentDatedOperandPages
import OAI.Hierarchy.DescentDatedOverlapAperture
import OAI.Hierarchy.DescentOrdinaryHeadRetileLayout
import OAI.Hierarchy.DescentOperandReadShape
import Mathlib.Data.Nat.Log

namespace OAI
/-! Address exponents of the old operand census, physical head repack and five selectors. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSIMDLookup Filter
variable {ι : ℕ→Type*} {α β : ∀h,ι h→ℕ}
def Linear (x : ∀h,ι h→ℕ) := ∃k:ℕ,∀ᶠ h in atTop,∀i,x h i≤k*h
theorem Linear.smaller (large : Linear α) (bound : ∀h i,β h i≤α h i) : Linear β :=by
  obtain ⟨k,high⟩:=large
  exact ⟨k,high.mono fun h ready i=>(bound h i).trans (ready i)⟩
theorem Linear.table (width : Linear α) : Bounded (fun h i=>2^(α h i)) :=by
  obtain ⟨k,wide⟩:=width
  exact Bounded.pow_of_linear (K:=k) wide
theorem Bounded.chunks (groups : Bounded α) (pitch : Bounded β) : Bounded (fun h i=>chunks (α h i) (β h i)) :=
  (groups.add pitch).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
end Hierarchy.DescentDatedAddressBook

namespace Hierarchy.DescentDatedOperandPages
open DescentDatedAddressBook DescentSIMDLookup DescentRawCablePanel.DepotRAM ProtocolRAM
variable {ι : ℕ→Type*} (f : ∀h,ι h→Shape) (l : ∀h,ι h→Layout)
theorem extent_rate (hosts : Bounded (fun h i=>(l h i).hosts)) (groups : Bounded (fun h i=>(l h i).groups))
    (old : Bounded (fun h i=>(l h i).old)) (next : Bounded (fun h i=>(l h i).newLanes))
    (cols : Bounded (fun h i=>count (f h i)))
    (sourceKey : Linear (fun h i=>totalBits (f h i)*(l h i).old))
    (resultKey : Linear (fun h i=>(l h i).bits*(l h i).old)) :
    Bounded (fun h i=>lastAddress (f h i) (l h i) 0) :=by
  have rows:=hosts.mul (groups.chunks old)
  have start:=((Bounded.const 0).add (cols.mul (sourceKey.table.add rows.padded))).add
    (((cols.mul rows).add (Bounded.const 1)).padded)
  have last:=Overlap.address_rate (cols.mul hosts) groups old next resultKey
  apply ((start.add last).add (hosts.mul (groups.chunks next)).padded).of_le
  intro h i
  rw [lastAddress,dataEnd]
  change Overlap.endAddress (scratch (f h i) (l h i) 0) _ _ _ _ _+_≤_
  rw [Overlap.address_affine]
  exact le_rfl
end Hierarchy.DescentDatedOperandPages

namespace Hierarchy.DescentOrdinaryHeadRetile.Shape
open DescentDatedAddressBook DescentSIMDLookup
variable {ι : ℕ→Type*} (s : ∀h,ι h→Shape)
theorem address_rate (fields : Bounded (fun h i=>(s h i).n)) (hosts : Bounded (fun h i=>(s h i).hosts))
    (groups : Bounded (fun h i=>(s h i).groups)) (old : Bounded (fun h i=>(s h i).before))
    (nxt : Bounded (fun h i=>(s h i).after)) (key : Linear (fun h i=>(s h i).bits*(s h i).before)) :
    Bounded (fun h i=>(s h i).endAddress 0) :=by
  have rows:=hosts.mul (groups.chunks old)
  have newRows:=hosts.mul (groups.chunks nxt)
  have start:=((Bounded.const 0).add (fields.mul rows)).add ((rows.add (Bounded.const 1)).padded)
  have tiles:=Overlap.address_rate hosts groups old nxt key
  apply (((start.add tiles).add (fields.mul newRows)).add (newRows.add (Bounded.const 1)).padded).of_le
  intro h i
  let S:=s h i
  have bound : Overlap.dest (S.roleStart 0) S.hosts S.groups S.before S.after S.bits ≤
      S.roleStart 0+Overlap.endAddress 0 S.hosts S.groups S.before S.after S.bits :=by
    rw [←Overlap.address_affine]
    exact Nat.le_add_right ..
  exact Nat.add_le_add_right (Nat.add_le_add_right bound _) _
end Hierarchy.DescentOrdinaryHeadRetile.Shape

namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedAddressBook DescentSIMDLookup
variable {ι : ℕ→Type*} (g : ∀h,ι h→Geometry)

private theorem priceBits (g : Geometry) (q : Fin 5) :
    max (Nat.clog 2 (candidateCount g q+1)+g.digitBits) (g.digitBits+g.digitBits) ≤ purchase g :=by
  have count : candidateCount g q≤candidateLimit g:=
    Finset.le_sup (f:=candidateCount g) (Finset.mem_univ q)
  have index:=Nat.clog_mono_right 2 (Nat.add_le_add_right count 1)
  exact (max_le_max (Nat.add_le_add_right index _) le_rfl).trans (le_max_right ..)

theorem pipeline_rate (hosts : Bounded (fun h i=>(g h i).hosts)) (groups : Bounded (fun h i=>(g h i).groups))
    (lanes : Bounded (fun h i=>(g h i).lanes)) (jobs : Bounded (fun h i=>(g h i).jobs))
    (options : ∀q,Bounded (fun h i=>candidateCount (g h i) q))
    (key : Linear (fun h i=>purchase (g h i)*(g h i).lanes)) :
    Bounded (fun h i=>(g h i).pipelineWords) :=by
  have s (q : Fin 5) (n fields : ℕ) (enough : n≤17) :
      Bounded (fun h i=>(g h i).stageWords n fields (candidateCount (g h i) q)) :=by
    have left:=key.smaller (β:=fun h i=>((g h i).digitBits*n+(g h i).digitBits)*(g h i).lanes) (by
      intro h i
      apply Nat.mul_le_mul_right
      exact (show (g h i).digitBits*n+(g h i).digitBits≤18*(g h i).digitBits by
        nlinarith only [Nat.mul_le_mul_left (g h i).digitBits enough]).trans (le_max_left ..))
    have right:=key.smaller (fun h i=>Nat.mul_le_mul_right (g h i).lanes (priceBits (g h i) q))
    exact (((Bounded.const (n+1)).mul ((Bounded.const 2).mul left.table)).add
      (((options q).add (Bounded.const 1)).mul ((Bounded.const 2).mul right.table))).add
      ((jobs.mul (Bounded.const fields)).mul (hosts.mul (groups.chunks lanes)).padded)
  have last:=key.smaller (β:=fun h i=>((g h i).digitBits*17+(g h i).digitBits)*(g h i).lanes) (by
    intro h i
    apply Nat.mul_le_mul_right
    exact (show (g h i).digitBits*17+(g h i).digitBits=18*(g h i).digitBits by ring).le.trans (le_max_left ..))
  exact (((((s 0 6 4 (by decide)).add (s 1 5 1 (by decide))).add (s 2 9 5 (by decide))).add
    (s 3 5 8 (by decide))).add (s 4 3 1 (by decide))).add ((Bounded.const (17+8)).mul ((Bounded.const 2).mul last.table))
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
