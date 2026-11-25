import OAI.Hierarchy.DescentDatedSourcePathDirectory
import OAI.Hierarchy.DescentSortedRoster
import OAI.Hierarchy.DescentSharedCableSerial

namespace OAI
/-! # Dense original halo rank on a physical, deduplicated raw endpoint bank -/
namespace Hierarchy.DescentDatedSourcePathDirectory.Dense
open DescentHaloWalkRAM DescentSortedRoster DescentFallbackRankRAM DescentPackedColony DescentSIMDLookup
open DescentSharedCableNames DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {H P w : ℕ}

theorem before_lt (reach : Fin H→Fin P→Option (Fin H)) (v u : Fin H) (p : Fin P)
    (hit : Gather.select reach v p=some u) : before reach v u<P :=by
  rw [←order_count]
  apply lt_of_lt_of_le (b:=((Finset.univ : Finset (Fin P))).card)
  · apply Finset.card_lt_card
    apply (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
    refine ⟨p,Finset.mem_univ _,?_⟩
    have seen : DescentFallbackLeafScan.first reach v p=some u:=hit
    intro counted
    have earlier := (Finset.mem_filter.mp counted).2
    change (DescentFallbackLeafScan.first reach v p).any (· < u) = true at earlier
    simp [seen] at earlier
  · simp

def value (reach : Fin H→Fin P→Option (Fin H)) (v : Fin H) (p : Fin P) : Cell (Packed.bits P) :=
  match h : Gather.select reach v p with
  | none=>0
  | some u=>Packed.token (some ⟨before reach v u,before_lt reach v u p h⟩)

private theorem value_number (reach : Fin H→Fin P→Option (Fin H)) (v : Fin H) (p : Fin P) :
    (value reach v p).val=(Gather.select reach v p).elim 0 (fun u=>before reach v u+1) :=by
  unfold value
  split <;> rename_i hit <;> simp [hit,Packed.token]

theorem at_sorted (reach : Fin H→Fin P→Option (Fin H)) (v u : Fin H) (p s : Fin P)
    (raw : Gather.select reach v p=some u) (old : indexed reach v s=some u) :
    (value reach v p).val=s.val+1 :=by
  have rank:=((indexed_iff reach v s u).1 old).2
  simp [value_number,raw,rank]

def bit (visited : Bank) (p q : Fin P) : Expr :=
  .branch .lt (atHost visited P q.val) (atHost visited P p.val) (.lit 1) (.lit 0)

def amount (visited : Bank) (p : Fin P) : Expr :=
  foldSum ((Finset.univ : Finset (Fin P)).toList.map (bit visited p))

def expr (visited : Bank) (H : ℕ) (p : Fin P) : Expr :=
  .branch .eq (atHost visited P p.val) (.lit H) (.lit 0) (.op .add (amount visited p) (.lit 1))

theorem reads (visited : Bank) {out : ℕ} (fit : visited.Fits w out) (size : H*P≤visited.size)
    (room : H<2^w) (m : Memory w) (reach : Fin H→Fin P→Option (Fin H))
    (issued : ∀v p,m (visited.base+(Ranks.id v p).val)=(number (Gather.select reach v p):Word w))
    (v : Fin H) (p : Fin P) : (expr visited H p).eval m (v.val:Word w)=((value reach v p).val:Word w) :=by
  have cell (q : Fin P):=(at_host fit size m v q).trans (issued v q)
  cases hit : Gather.select reach v p with
  | none=>simp [expr,Expr.eval,DescriptorExpr.Comparison.test,cell,hit,number,value_number]
  | some u=>
    have selected : (atHost visited P p.val).eval m (v.val:Word w)=(u.val:Word w):=by
      simpa only [hit,number,Option.elim_some] using cell p
    have distinct : (u.val:Word w)≠(H:Word w):=by
      intro no
      have eqn:=congrArg Fin.val no
      rw [Fin.val_cast_of_lt (u.isLt.trans room),Fin.val_cast_of_lt room] at eqn
      exact u.isLt.ne eqn
    have each (q : Fin P) : (bit visited p q).eval m (v.val:Word w)=((keep reach v u q).toNat:Word w) :=by
      change _=(((Gather.select reach v q).any (·<u)).toNat:Word w)
      unfold bit
      have comparison (a : ℕ) (fits : a<2^w) :
          ((a:Word w)<(u.val:Word w)) ↔ a<u.val :=by
        change ((a:Word w).val<(u.val:Word w).val) ↔ _
        rw [Fin.val_cast_of_lt fits, Fin.val_cast_of_lt (u.isLt.trans room)]
      cases e : Gather.select reach v q with
      | none=>
        have high : ¬((H:Word w)<(u.val:Word w)):=
          fun h=>Nat.not_lt_of_ge u.isLt.le ((comparison H room).mp h)
        simp [Expr.eval,DescriptorExpr.Comparison.test,selected,cell q,e,number,high]
      | some z=>
        by_cases less : z<u
        · have ltWord := (comparison z.val (z.isLt.trans room)).mpr less
          simp [Expr.eval,DescriptorExpr.Comparison.test,selected,cell q,e,number,ltWord,less]
        · have notWord : ¬((z.val:Word w)<(u.val:Word w)) :=
            fun h=>less ((comparison z.val (z.isLt.trans room)).mp h)
          simp [Expr.eval,DescriptorExpr.Comparison.test,selected,cell q,e,number,notWord,less]
    have count : (amount visited p).eval m (v.val:Word w)=(before reach v u:Word w) :=by
      rw [amount,foldSum_eval,List.map_map]
      simp only [Function.comp_def,each]
      rw [←order_count]
      rw [Finset.sum_map_toList]
      simp [Bool.toNat,Finset.sum_boole]
    simp [expr,Expr.eval,DescriptorExpr.Comparison.test,selected,distinct,count,value_number,hit,
      RowOp.opcode,BinaryOp.eval]

theorem fits (visited : Bank) {out : ℕ} (fit : visited.Fits w out) (p : Fin P) :
    (expr visited H p).Fits w out :=by
  have each (q : Fin P) : (bit visited p q).Fits w out:=⟨place_fits fit ..,place_fits fit ..,trivial,trivial⟩
  have total (xs : List (Fin P)) : (foldSum (xs.map (bit visited p))).Fits w out:=by
    induction xs with
    | nil=>trivial
    | cons q xs ih=>exact ⟨each q,ih⟩
  exact ⟨place_fits fit ..,trivial,trivial,total _,trivial⟩

theorem work (visited : Bank) (p : Fin P) : (expr visited H p).work≤(P+1)*(30+4*P+4*(P*P)) :=by
  have total (xs : List (Fin P)) :
      (foldSum (xs.map (bit visited p))).work≤1+xs.length*(22+8*P) :=by
    induction xs with
    | nil=>simp [foldSum,Expr.work]
    | cons q xs ih=>
      change (bit visited p q).work+(foldSum (xs.map (bit visited p))).work+1≤1+(xs.length+1)*(22+8*P)
      simp only [bit,atHost,Expr.work,times_work,Nat.add_mul,Nat.one_mul] at *
      omega
  have lower:=total (Finset.univ.toList : List (Fin P))
  simp only [Finset.length_toList,Finset.card_univ,Fintype.card_fin] at lower
  change (Expr.branch _ _ _ _ (.op .add (foldSum _) _)).work≤_
  simp only [atHost,Expr.work,times_work,Nat.add_mul,Nat.one_mul] at *
  have enough : 4*P≤4*(P*P) := Nat.mul_le_mul_left _ (by
    have pos:=Nat.zero_lt_of_lt p.isLt
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left P pos)
  nlinarith [Nat.mul_le_mul_left P enough]

end
end Hierarchy.DescentDatedSourcePathDirectory.Dense

end OAI
