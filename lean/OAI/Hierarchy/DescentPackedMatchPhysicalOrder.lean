import OAI.Hierarchy.DescentPackedProfileCursor
import OAI.Hierarchy.DescentPackedProfileWindow
import OAI.Hierarchy.DescentMatchedRosterCount

namespace OAI
/-! # Chronological addresses in the measured packed survivor tape -/

noncomputable section
namespace Hierarchy.DescentPacking.PackedMatch.Chronology
open DescentPackedProfileWindow MatchedStageRAM
open scoped Classical BigOperators
variable {C : Type} [Fintype C] {n M U : ℕ}

def rank (seat : C ↪ Fin n × Fin M) : C ↪ ℕ :=
  (seat.trans finProdFinEquiv.toEmbedding).trans Fin.valEmbedding

omit [Fintype C] in
theorem rank_val (seat : C ↪ Fin n × Fin M) (c : C) :
    rank seat c = (seat c).1.val*M+(seat c).2.val := by
  change (seat c).2.val+M*(seat c).1.val=_
  ring

def chunk (cnt : Fin n → Fin M → Fin (U+1)) (r : ℕ) :=
  if h : r<n then ∑i,(cnt ⟨r,h⟩ i).val else 0

/-- All live and empty SIMD lanes are charged in their actual storage order. -/
structure Counts (seat : C ↪ Fin n × Fin M) (amount : C → ℕ)
    (cnt : Fin n → Fin M → Fin (U+1)) : Prop where
  live : ∀ c, (cnt (seat c).1 (seat c).2).val=amount c
  hole : ∀ r i, (∀c,seat c≠(r,i)) → (cnt r i).val=0

theorem within (seat : C ↪ Fin n × Fin M) (amount : C→ℕ)
    (cnt : Fin n→Fin M→Fin (U+1)) (measured : Counts seat amount cnt)
    (r : Fin n) (j : ℕ) (fit : j≤M) :
    countAt (rank seat) amount (r.val*M)+countAt Fin.valEmbedding (fun i=>(cnt r i).val) j =
      countAt (rank seat) amount (r.val*M+j) := by
  induction j with
  | zero => simp only [countAt_start,Nat.add_zero]
  | succ j ih =>
    let i : Fin M:=⟨j,Nat.lt_of_succ_le fit⟩
    have old:=ih (Nat.le_of_succ_le fit)
    rw [countAt_live Fin.valEmbedding (fun i=>(cnt r i).val) i (q := j) rfl,←Nat.add_assoc,old]
    by_cases live : ∃c,seat c=(r,i)
    · obtain ⟨c,hc⟩:=live
      have eqn : rank seat c=r.val*M+j := by rw [rank_val,hc]
      have val:=measured.live c
      rw [hc] at val
      exact (congrArg (_+·) val).trans (countAt_live (rank seat) amount c eqn).symm
    · have hole : ∀c,seat c≠(r,i) := fun c eqn=>live ⟨c,eqn⟩
      have empty : ∀c,rank seat c≠r.val*M+j := by
        intro c eqn
        apply hole c
        apply finProdFinEquiv.injective
        apply Fin.ext
        calc
          (finProdFinEquiv (seat c)).val = r.val*M+j := eqn
          _ = (finProdFinEquiv (r,i)).val := by change _=j+M*r.val;ring
      simpa only [measured.hole r i hole,Nat.add_zero,Nat.add_assoc] using
        (show countAt (rank seat) amount (r.val*M+j)+(cnt r i).val =
            countAt (rank seat) amount ((r.val*M+j)+1) by rw [measured.hole r i hole,Nat.add_zero,countAt_empty _ _ empty])

theorem start (seat : C ↪ Fin n × Fin M) (amount : C→ℕ)
    (cnt : Fin n→Fin M→Fin (U+1)) (measured : Counts seat amount cnt)
    (r : ℕ) (fit : r≤n) :
    PackedProfileCursor.total (chunk cnt) r = countAt (rank seat) amount (r*M) := by
  induction r with
  | zero => simp only [PackedProfileCursor.total,Nat.zero_mul,countAt_start]
  | succ r ih =>
    let i : Fin n:=⟨r,Nat.lt_of_succ_le fit⟩
    have done:=within seat amount cnt measured i M le_rfl
    rw [countAt_end Fin.valEmbedding (fun j=>(cnt i j).val) (fun j=>j.isLt)] at done
    rw [PackedProfileCursor.total,ih (Nat.le_of_succ_le fit),chunk,dite_eq_left i.isLt,Nat.succ_mul]
    exact done

theorem address (seat : C ↪ Fin n × Fin M) (amount : C→ℕ)
    (cnt : Fin n→Fin M→Fin (U+1)) (measured : Counts seat amount cnt) (c : C) :
    PackedProfileCursor.total (chunk cnt) (seat c).1.val +
      localPrefix (cnt (seat c).1) (seat c).2 =
      ProtocolRAMPortRanks.«prefix» amount (rank seat) c := by
  rw [start seat amount cnt measured _ (seat c).1.isLt.le]
  change _+countAt Fin.valEmbedding _ (seat c).2.val=countAt (rank seat) amount (rank seat c)
  rw [rank_val]
  exact within seat amount cnt measured _ _ (seat c).2.isLt.le

end Hierarchy.DescentPacking.PackedMatch.Chronology

end
end OAI
