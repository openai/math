import OAI.Hierarchy.DescentDatedSourcePathDirectory
import OAI.Hierarchy.DescentSortedRoster

namespace OAI
/-! # Translate the dense W donor ordinal to the first physical four-walk -/
namespace Hierarchy.DescentDatedSourcePathDirectory.Sorted
open DescentHaloWalkRAM DescentSIMDLookup DescentPackedColony DescentSortedRoster DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H P w : ℕ}

def firstPath (reach : Fin H→Fin P→Option (Fin H)) (v u : Fin H) : List (Fin P)→ℕ
  | []=>0
  | p::xs=>if Gather.select reach v p=some u then p.val else firstPath reach v u xs

def rawAtOrdinal (reach : Fin H→Fin P→Option (Fin H)) (v : Fin H) (s : Fin P) : ℕ :=
  (indexed reach v s).elim 0 (fun u=>firstPath reach v u (List.finRange P))

/-- A live dense ordinal selects the unique earliest raw walk to that host.
The returned value is zero-based, as required by the origin register. -/
theorem raw_at (reach : Fin H→Fin P→Option (Fin H)) (v u : Fin H) (s : Fin P)
    (read : indexed reach v s=some u) :
    ∃! p : Fin P,Gather.select reach v p=some u ∧ rawAtOrdinal reach v s=p.val :=by
  have member:=((indexed_iff reach v s u).1 read).1
  obtain ⟨p,chosen,unique⟩:=Gather.once reach v u (Finset.mem_filter.mp member).2
  have result (l : List (Fin P)) (inside : p∈l) : firstPath reach v u l=p.val :=by
    induction l with
    | nil=>simp at inside
    | cons q l ih=>
      rw [firstPath]
      split
      · rename_i yes
        exact congrArg Fin.val (unique q yes)
      · rename_i no
        have neq : p≠q:=fun eqn=>no (eqn ▸ chosen)
        exact ih ((List.mem_cons.mp inside).resolve_left neq)
  refine ⟨p,⟨chosen,?_⟩,fun q h=>unique q h.1⟩
  simp only [rawAtOrdinal,read,Option.elim_some]
  exact result _ (List.mem_finRange _)

theorem raw_eq (reach : Fin H→Fin P→Option (Fin H)) (v u : Fin H) (s p : Fin P)
    (ordinal : indexed reach v s=some u) (hit : Gather.select reach v p=some u) :
    rawAtOrdinal reach v s=p.val :=by
  obtain ⟨q,⟨picked,number⟩,_⟩:=raw_at reach v u s ordinal
  have present:=((indexed_iff reach v s u).1 ordinal).1
  have only:=Gather.once reach v u (Finset.mem_filter.mp present).2
  exact number.trans (congrArg Fin.val (only.unique picked hit))

def scan (visited : Bank) (wanted : Expr) : List (Fin P)→Expr
  | []=>.lit 0
  | p::xs=>.branch .eq (atHost visited P p.val) wanted (.lit p.val) (scan visited wanted xs)

/-- Both tables are pre-existing scalar host-by-walk banks. -/
def expr (visited sorted : Bank) (H : ℕ) (s : Fin P) : Expr :=
  let wanted:=atHost sorted P s.val
  .branch .eq wanted (.lit H) (.lit 0) (scan visited wanted (List.finRange P))

private theorem eq_number {x y : Option (Fin H)} (room : H<2^w) :
    ((number x:Word w)=(number y:Word w)) ↔ x=y :=by
  have small (z : Option (Fin H)) : number z≤H:=by cases z with | none=>exact le_rfl | some i=>exact i.isLt.le
  constructor
  · intro h
    have eqn:=congrArg Fin.val h
    rw [Fin.val_cast_of_lt ((small x).trans_lt room),Fin.val_cast_of_lt ((small y).trans_lt room)] at eqn
    cases x with
    | none=> cases y with | none=>rfl | some i=>exact False.elim (i.isLt.ne (Eq.symm eqn))
    | some i=> cases y with | none=>exact False.elim (i.isLt.ne eqn) | some u=>exact congrArg some (Fin.ext eqn)
  · rintro rfl
    rfl

theorem expr_read (visited sorted : Bank) (out : ℕ) (m : Memory w) (reach : Fin H→Fin P→Option (Fin H))
    (vis : visited.Fits w out) (srt : sorted.Fits w out) (nv : H*P≤visited.size) (ns : H*P≤ sorted.size)
    (room : H<2^w) (raw : ∀v p,m (visited.base+(Ranks.id v p).val)=(number (Gather.select reach v p):Word w))
    (old : ∀v s,m (sorted.base+(Ranks.id v s).val)=(number (indexed reach v s):Word w))
    (v : Fin H) (s : Fin P) :
    (expr visited sorted H s).eval m (v.val:Word w)=(rawAtOrdinal reach v s:Word w) :=by
  let wanted:=atHost sorted P s.val
  have hdr : wanted.eval m (v.val:Word w)=(number (indexed reach v s):Word w):=
    (at_host srt ns m v s).trans (old v s)
  have cell (q : Fin P) := (at_host vis nv m v q).trans (raw v q)
  cases hit : indexed reach v s with
  | none=>
    simp only [hit] at hdr
    simp [expr,←show wanted=atHost sorted P s.val from rfl,Expr.eval,DescriptorExpr.Comparison.test,hdr,rawAtOrdinal,hit,number]
  | some u=>
    have hv : wanted.eval m (v.val:Word w)=(u.val:Word w):=by
      simpa only [hit,number,Option.elim_some] using hdr
    have high : (u.val:Word w)≠(H:Word w):=by
      exact fun h=>(show some u≠none by simp) ((eq_number (x:=some u) (y:=none) room).1 h)
    have scan_ (xs : List (Fin P)) : (scan visited wanted xs).eval m (v.val:Word w)=(firstPath reach v u xs:Word w) :=by
      induction xs with
      | nil=>rfl
      | cons q xs ih=>
        have eqn : ((number (Gather.select reach v q):Word w)=(u.val:Word w)) ↔ Gather.select reach v q=some u :=
          eq_number (y:=some u) room
        by_cases same : Gather.select reach v q=some u <;>
          simp [scan,Expr.eval,DescriptorExpr.Comparison.test,cell,hv,eqn,firstPath,same,ih]; simp [number]
    simpa [expr,←show wanted=atHost sorted P s.val from rfl,Expr.eval,DescriptorExpr.Comparison.test,hv,high,
      rawAtOrdinal,hit] using scan_ (List.finRange P)

theorem expr_fits (visited sorted : Bank) {out : ℕ} (vis : visited.Fits w out) (srt : sorted.Fits w out) (s : Fin P) :
    (expr visited sorted H s).Fits w out :=by
  let wanted:=atHost sorted P s.val
  have fit : wanted.Fits w out:=place_fits srt _ _
  have bound (xs : List (Fin P)) : (scan visited wanted xs).Fits w out:=by
    induction xs with
    | nil=>trivial
    | cons q xs ih=>exact ⟨place_fits vis _ _,fit,trivial,ih⟩
  exact ⟨fit,trivial,trivial,bound _⟩

theorem expr_work (visited sorted : Bank) (s : Fin P) :
    (expr visited sorted H s).work≤(P+1)*(30+8*P) :=by
  let wanted:=atHost sorted P s.val
  have each (xs : List (Fin P)) : (scan visited wanted xs).work≤1+xs.length*(30+8*P) :=by
    induction xs with
    | nil=>simp [scan,Expr.work]
    | cons q xs ih=>
      simp only [scan,wanted,atHost,Expr.work,times_work,List.length_cons,Nat.add_mul] at *
      omega
  have cost:=each (List.finRange P)
  simp only [List.length_finRange] at cost
  change (Expr.branch _ _ _ _ (scan visited wanted (List.finRange P))).work≤_
  simp only [wanted,atHost,Expr.work,times_work,Nat.add_mul,Nat.one_mul] at *
  omega

end
end Hierarchy.DescentDatedSourcePathDirectory.Sorted

end OAI
