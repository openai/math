import OAI.Computability.BorderVNP.DiagonalExternalSewFourSlot

/-! # The live four-slot addresses are exactly the occupied exterior intervals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.FourSlot

open Finset

variable {R r literal stride link g V : ℕ}

/-- Every positive row decoded at a padded four-slot address is the genuine
ordered interval between its two actual team blocks, and encodes back to
the same address. -/
theorem exists_index_of_live (hg : 0 < g) (small : g ≤ link) (fit : literal+R*link ≤ stride)
    (room : r*stride ≤ V*g) (team : Fin (R+1)) (site : Fin V) (right next : Bool)
    (live : (row R r literal stride link g team.val site.val right next).live = true) :
    ∃ c : Pieces (fieldStart (R := R) (r := r) literal stride link) g link,
      index V hg fit room c = (team,site,right,next) := by
  let base := site.val*g
  let x := base + if right then g-1 else 0
  let p := x/stride
  let col := x%stride
  let k := (col-literal)/link
  let A := p*stride+literal+k*link
  let B := p*stride+literal+team.val*link
  let firstRemote := (B+(base-A))/g
  let m := firstRemote+next.toNat
  let cut := bounds A B g link site.val m
  change decide (p<r ∧ literal≤col ∧ k<R ∧ team.val≤k ∧
    (right=false ∨ ¬(A≤base ∧ base<A+link)) ∧ cut.1<cut.2) = true at live
  obtain ⟨hp,hl,hk,ht,hdup,hcut⟩ := of_decide_eq_true live
  let high : Fin (R+1) := ⟨k+1,by omega⟩
  let b : Routing.Block (R+1) := ⟨(team,high),show team.val < k+1 by omega⟩
  let f : Routing.Block (R+1) × Fin r := (b,⟨p,hp⟩)
  have loRank : (fieldRank b false).val = k := by
    change (if high.val < team.val then high.val else high.val-1) = k
    dsimp [high]
    rw [ite_eq_right (by omega)]
  have hiRank : (fieldRank b true).val = team.val := by
    change (if team.val < high.val then team.val else team.val-1) = team.val
    rw [ite_eq_left (show team.val < high.val from b.property)]
  let st := fieldStart (R := R) (r := r) literal stride link
  have hA : st f false = A := by
    change p*stride+literal+(fieldRank b false).val*link = _
    rw [loRank]
  have hB : st f true = B := by
    change p*stride+literal+(fieldRank b true).val*link = _
    rw [hiRank]
  have bitLt : cut.1 < link := hcut.trans_le (Nat.min_le_left _ _)
  let bit : Fin link := ⟨cut.1,bitLt⟩
  have hpair : blockPair st g f bit = (site.val,m) := by
    have h := (mem_bounds_iff (A := A) (B := B) (s := site.val) (t := m) hg bitLt).mp ⟨le_rfl,hcut⟩
    simpa only [blockPair,hA,hB,bit] using Prod.ext h.1 h.2
  let c : Pieces st g link := ⟨f,⟨(site.val,m),mem_image.mpr ⟨bit,mem_univ _,hpair⟩⟩⟩
  have hraw : A ≤ x ∧ x < A+link := mem_decoded (hg.trans_le small) hl
  have hright : rightProbe c = right := by
    change decide (¬(st f false ≤ base ∧ base < st f false+link)) = right
    rw [hA]
    cases right
    · have hx : x = base := by simp [x]
      rw [hx] at hraw
      simp [hraw]
    · have hn : ¬(A≤base ∧ base<A+link) := hdup.resolve_left (by decide)
      simp [hn]
  have hbase : remoteBase c = firstRemote := by
    change (st f true+(site.val*g-st f false))/g = _
    rw [hA,hB]
  have hnext : nextBlock c = next := by
    change decide (m ≠ remoteBase c) = next
    rw [hbase]
    cases next <;> simp [m]
  refine ⟨c,?_⟩
  change (team,site,rightProbe c,nextBlock c) = _
  rw [hright,hnext]

/-- The four-slot reader's live flag recognizes exactly the image of the injective
address map of occupied intervals. -/
theorem row_live_iff (hg : 0 < g) (small : g ≤ link) (fit : literal+R*link ≤ stride)
    (room : r*stride ≤ V*g) (x : Fin (R+1) × Fin V × (Bool × Bool)) :
    (row R r literal stride link g x.1.val x.2.1.val x.2.2.1 x.2.2.2).live = true ↔
      ∃ c : Pieces (fieldStart (R := R) (r := r) literal stride link) g link, index V hg fit room c = x := by
  constructor
  · exact exists_index_of_live hg small fit room x.1 x.2.1 x.2.2.1 x.2.2.2
  · rintro ⟨c,rfl⟩
    exact congrArg Row.live (row_index c hg small fit)

end Diagonal.ExternalSew.FourSlot

end BorderVNP
end Computability
end OAI
