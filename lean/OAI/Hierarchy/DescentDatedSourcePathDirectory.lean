import OAI.Hierarchy.DescentHaloPairRanks
import OAI.Hierarchy.DescentHaloPackedGather

namespace OAI
/-! # Locate the old source of an inherited cable from its selected actor

The actor's old home and its one additional rotor step may span five hops.
The previous header contains both eight-hop endpoints and the deduplicated
four-hop roster. A comparison between these two physical banks recovers the
canonical four-hop donor socket whenever the old source belongs to the halo.
The directory is shared by all packed operand lanes at a receiving host. -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentHaloWalkRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H P w : ℕ}

structure Banks where
  visited : Bank
  pairs : Bank

structure Reads (B : Banks) (reach : Fin H → Fin P → Option (Fin H)) (m : Memory w) : Prop where
  visited : ∀v q, m (B.visited.base+(Ranks.id v q).val)=(number (Gather.select reach v q):Word w)
  pairs : ∀v t, m (B.pairs.base+(Ranks.id v t).val)=(number (PairRanks.combined reach v t):Word w)

structure Fits (B : Banks) (H P out w : ℕ) : Prop where
  visited : B.visited.Fits w out
  pairs : B.pairs.Fits w out
  rosterSize : H*P ≤ B.visited.size
  pairSize : H*(P*P) ≤ B.pairs.size
  sentinel : H < 2^w
  room : out+H < 2^w

def atHost (b : Bank) (pitch i : ℕ) : Expr :=
  .lookup b (.op .add (times .row pitch) (.lit i))

def seek (B : Banks) (t : Fin (P*P)) : List (Fin P) → Expr
  | [] => .lit 0
  | q::qs => .branch .eq (atHost B.visited P q.val) (atHost B.pairs (P*P) t.val)
      (.lit (q.val+1)) (seek B t qs)

def body (B : Banks) (H : ℕ) (p d : Fin P) : Expr :=
  let t:=PairRanks.pair p d
  .branch .eq (atHost B.pairs (P*P) t.val) (.lit H) (.lit 0) (seek B t (List.finRange P))

def ordinal (reach : Fin H → Fin P → Option (Fin H)) (v : Fin H) (t : Fin (P*P)) : List (Fin P) → ℕ
  | [] => 0
  | q::qs => if number (Gather.select reach v q)=number (PairRanks.combined reach v t) then q.val+1
      else ordinal reach v t qs

def value (reach : Fin H → Fin P → Option (Fin H)) (v : Fin H) (p d : Fin P) : ℕ :=
  let t:=PairRanks.pair p d
  if number (PairRanks.combined reach v t)=H then 0 else ordinal reach v t (List.finRange P)

theorem value_le (reach : Fin H → Fin P → Option (Fin H)) (v : Fin H) (p d : Fin P) :
    value reach v p d ≤ P := by
  let t:=PairRanks.pair p d
  have count (xs : List (Fin P)) : ordinal reach v t xs ≤ P := by
    induction xs with
    | nil => exact Nat.zero_le _
    | cons q qs ih =>
      simp only [ordinal]
      split
      · exact q.isLt
      · exact ih
  change (if number (PairRanks.combined reach v t)=H then 0 else ordinal reach v t (List.finRange P)) ≤ P
  split
  · exact Nat.zero_le _
  · exact count _

private theorem small (u : Option (Fin H)) : number u ≤ H := by
  cases u with
  | none => exact le_rfl
  | some i => exact i.isLt.le

private theorem cast_eq (u z : ℕ) (x : u < 2^w) (y : z < 2^w) :
    ((u:Word w)=(z:Word w)) ↔ u=z := by
  constructor
  · intro eqn
    simpa only [Fin.val_cast_of_lt x,Fin.val_cast_of_lt y] using congrArg Fin.val eqn
  · exact fun eqn=>congrArg (fun n:ℕ=>(n:Word w)) eqn

theorem at_host {b : Bank} {S out : ℕ} (fit : b.Fits w out) (size : H*S ≤ b.size)
    (m : Memory w) (v : Fin H) (i : Fin S) :
    (atHost b S i.val).eval m (v.val:Word w)=m (b.base+(Ranks.id v i).val) := by
  have ptr : (S:Word w)*(v.val:Word w)+(i.val:Word w)=((Ranks.id v i).val:Word w) := by
    simp [Ranks.id,finProdFinEquiv_apply_val,add_comm]
  have addressed: (Ranks.id v i).val<b.size:=(Ranks.id v i).isLt.trans_le size
  change b.read m ((times .row S).eval m (v.val:Word w)+(i.val:Word w))=_
  rw [times_at]
  change b.read m ((S:Word w)*(v.val:Word w)+(i.val:Word w))=_
  rw [ptr]
  simp [Bank.read,Fin.val_cast_of_lt (addressed.trans fit.2.1),Nat.mod_eq_of_lt addressed]

theorem body_at (B : Banks) {out : ℕ} (fit : Fits B H P out w)
    (reach : Fin H → Fin P → Option (Fin H)) (m : Memory w) (data : Reads B reach m)
    (v : Fin H) (p d : Fin P) :
    (body B H p d).eval m (v.val:Word w)=(value reach v p d:Word w) := by
  let t:=PairRanks.pair p d
  let other:=PairRanks.combined reach v t
  have target : (atHost B.pairs (P*P) t.val).eval m (v.val:Word w)=(number other:Word w):=
    (at_host fit.pairs fit.pairSize m v t).trans (data.pairs v t)
  have read (qs : List (Fin P)) : (seek B t qs).eval m (v.val:Word w)=(ordinal reach v t qs:Word w) := by
    induction qs with
    | nil => rfl
    | cons q qs ih =>
      have cell:=(at_host fit.visited fit.rosterSize m v q).trans (data.visited v q)
      have eqn:=cast_eq _ _ ((small (Gather.select reach v q)).trans_lt fit.sentinel) ((small other).trans_lt fit.sentinel)
      by_cases yes : number (Gather.select reach v q)=number other <;>
        simp [seek,Expr.eval,DescriptorExpr.Comparison.test,cell,target,eqn,ordinal,yes,ih,other] at *
  have lim:=cast_eq _ _ ((small other).trans_lt fit.sentinel) fit.sentinel
  by_cases empty : number other=H <;>
    simp [body,value,Expr.eval,DescriptorExpr.Comparison.test,t,target,read,other] at *
  · simp only [ite_eq_left (lim.mpr empty),ite_eq_left empty]
  · simp only [ite_eq_right (mt lim.mp empty),ite_eq_right empty]

theorem place_fits {b : Bank} {out : ℕ} (fit : b.Fits w out) (n i : ℕ) :
    (atHost b n i).Fits w out := ⟨fit,times_fits (f:=Expr.row) (w:=w) (out:=out) trivial n,trivial⟩

theorem body_fits (B : Banks) {out : ℕ} (fit : Fits B H P out w) (p d : Fin P) :
    (body B H p d).Fits w out := by
  let t:=PairRanks.pair p d
  have recFit (qs : List (Fin P)) : (seek B t qs).Fits w out := by
    induction qs with
    | nil => trivial
    | cons q qs ih => exact ⟨place_fits fit.visited _ _,place_fits fit.pairs _ _,trivial,ih⟩
  exact ⟨place_fits fit.pairs _ _,trivial,trivial,recFit _⟩

theorem body_work (B : Banks) (H : ℕ) (p d : Fin P) :
    (body B H p d).work ≤ (P+1)*(30+4*P+4*(P*P)) := by
  let t:=PairRanks.pair p d
  let cost:=30+4*P+4*(P*P)
  have each (qs : List (Fin P)) : (seek B t qs).work ≤ 1+qs.length*cost := by
    induction qs with
    | nil => simp [seek,Expr.work]
    | cons q qs ih =>
      simp only [seek,atHost,Expr.work,times_work,List.length_cons,Nat.add_mul] at *
      dsimp [cost] at *
      omega
  have count:=each (List.finRange P)
  simp only [List.length_finRange] at count
  change (Expr.branch _ _ _ _ (seek B t (List.finRange P))).work ≤ _
  simp only [atHost,Expr.work,times_work,Nat.add_mul,Nat.one_mul] at *
  dsimp [cost] at *
  omega

theorem run (B : Banks) (out : ℕ) (fit : Fits B H P out w)
    (reach : Fin H → Fin P → Option (Fin H)) (m : Memory w) (data : Reads B reach m) (p d : Fin P) :
    let f:=body B H p d
    let after:=image out H f m
    (scan w out H f).Exec m after (4+H*(2*f.work+4)) ∧
      (∀v:Fin H,after (out+v.val)=(value reach v p d:Word w)) ∧ CheapCode (scan w out H f) := by
  intro f after
  exact ⟨scan_exec _ _ _ _ (body_fits B fit p d) fit.room,
    fun v=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ v).trans (body_at B fit reach m data v p d),by apply scan_cheap⟩

theorem located (reach : Fin H → Fin P → Option (Fin H)) (v actor source : Fin H) (p d q : Fin P)
    (home : reach v p=some actor) (step : reach actor d=some source)
    (selected : Gather.select reach v q=some source) :
    value reach v p d=q.val+1 := by
  let t:=PairRanks.pair p d
  have dest : PairRanks.combined reach v t=some source := by simp [t,PairRanks.joined,home,step]
  have existsHit : ∃a,reach v a=some source := by
    refine ⟨q,?_⟩
    unfold Gather.select at selected
    split at selected
    · contradiction
    · exact selected
  obtain ⟨key,found,uniq⟩:=Gather.once reach v source existsHit
  have same (j : Fin P) : number (Gather.select reach v j)=source.val ↔ j=q := by
    constructor
    · intro eqn
      have match_ : Gather.select reach v j=some source := by
        cases got : Gather.select reach v j with
        | none => exact False.elim (source.isLt.ne (by simpa [number,got] using eqn.symm))
        | some u => exact congrArg some (Fin.ext (by simpa [number,got] using eqn))
      exact (uniq j match_).trans (uniq q selected).symm
    · rintro rfl
      simp [selected,number]
  have good (qs : List (Fin P)) (has : q∈qs) : ordinal reach v t qs=q.val+1 := by
    induction qs with
    | nil => simp at has
    | cons j js ih =>
      by_cases hit : j=q
      · subst j
        simp [ordinal,dest,selected,number]
      · have miss:=mt (same j).mp hit
        rw [ordinal,ite_eq_right (by simpa [dest,number] using miss)]
        exact ih ((List.mem_cons.mp has).resolve_left (Ne.symm hit))
  have live : number (PairRanks.combined reach v t)≠H := by simpa [dest,number] using source.isLt.ne
  exact (ite_eq_right live).trans (good _ (List.mem_finRange q))

end
end Hierarchy.DescentDatedSourcePathDirectory

end OAI
