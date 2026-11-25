import OAI.Hierarchy.TaggedWireEntryCheck
import OAI.Hierarchy.TaggedWireNamedAperture
import OAI.Hierarchy.TaggedWireHistoryRoles

namespace OAI
/-! # Original mixed-radix source and reserve bits of the exposed matching -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.EntryOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WireTelescope TaggedPrune Tagged Catalyst AdaptiveProbe MatchingEntry
open scoped Classical BigOperators
variable {h d k w R : ℕ}

abbrev Bucket (h d k : ℕ) := Row h ⊕ (Columns h d×Fin k)

def bucket : exposedEdges h d k w R→Bucket h d k
  | .inl (i,_)=>.inl i
  | .inr v=>.inr (reserveLocation h d k R v)

def digit : exposedEdges h d k w R→ℕ
  | .inl (_,j)=> j.val
  | .inr v=>((reserveSeats h d k R v).2).val

def base (w R : ℕ) : Bucket h d k→ℕ
  | .inl i=> w*i.val
  | .inr c=>2^h*w+R*((Fintype.equivFin _) c).val

def capacity (w R : ℕ) : Bucket h d k→ℕ := Sum.elim (fun _=> w) (fun _=> R)

def edge (w R : ℕ) (b : Bucket h d k) : Fin (capacity w R b)→exposedEdges h d k w R :=
  match b with
  | .inl i=> fun j=>.inl (i,j)
  | .inr c=> fun j=>.inr ((reserveSeats h d k R).symm (c,j))

theorem digit_lt (e : exposedEdges h d k w R) : digit e< capacity w R (bucket e) := by
  rcases e with ⟨i,j⟩|v
  · exact j.isLt
  · exact ((reserveSeats h d k R v).2).isLt

theorem edge_bucket (b : Bucket h d k) (j : Fin (capacity w R b)) : bucket (edge w R b j)=b := by
  cases b <;> simp [edge,bucket,reserveLocation]

theorem unit_index (e : exposedEdges h d k w R) :
    ((exposedOrder h d k w R).symm e).val=base w R (bucket e)+digit e := by
  rcases e with ⟨i,j⟩|v
  · change j.val+w*i.val=w*i.val+j.val
    omega
  · change 2^h*w+(((reserveSeats h d k R v).2).val+R*((Fintype.equivFin _) (reserveLocation h d k R v)).val)=_
    simp only [base,bucket,digit]
    omega

theorem edge_index (b : Bucket h d k) (j : Fin (capacity w R b)) :
    ((exposedOrder h d k w R).symm (edge w R b j)).val=base w R b+j.val := by
  rw [unit_index,edge_bucket]
  have low : digit (edge w R b j)=j.val := by cases b <;> simp [digit,edge]
  rw [low]

def ends (p : Equiv.Perm (Row h)) : Bucket h d k→Site h d k×Site h d k
  | .inl i=>((.inl (p i),none),(.inr (.inr i),none))
  | .inr (c,j)=>((c,some (j,false)),(c,some (j,true)))

theorem distinct (p : Equiv.Perm (Row h)) (b : Bucket h d k) : (ends p b).1≠(ends p b).2 := by
  rcases b with i|⟨c,j⟩ <;> simp [ends]

def chord (p : Equiv.Perm (Row h)) (b : Bucket h d k) : Chord (siteLast h d k+1) :=
  orderedChord (siteNumber h d k (ends p b).1) (siteNumber h d k (ends p b).2) ((siteNumber h d k).injective.ne (distinct p b))

private theorem oriented_eq {n : ℕ} (a b c d : Fin n) (ab : a≠b) (cd : c≠d)
    (same : orderedChord a b ab=orderedChord c d cd) : (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have eq:=congrArg Subtype.val same
  by_cases l:a< b <;> by_cases r:c< d <;> simp only [orderedChord,l,r,dite_true,dite_false,Prod.mk.injEq] at eq <;> tauto

theorem chord_injective (p : Equiv.Perm (Row h)) : Function.Injective (chord (d:=d) (k:=k) p) := by
  intro a b same
  obtain good|rev:=oriented_eq _ _ _ _ _ _ same
  · have l:=(siteNumber h d k).injective good.1
    have r:=(siteNumber h d k).injective good.2
    rcases a with i|⟨x,j⟩ <;> rcases b with t|⟨y,u⟩ <;> simp [ends] at l r ⊢ <;> tauto
  · have l:=(siteNumber h d k).injective rev.1
    rcases a with i|⟨x,j⟩ <;> rcases b with t|⟨y,u⟩ <;> simp [ends] at l

theorem numbered_chord (p : Equiv.Perm (Row h)) (i : Fin (Fintype.card (exposedEdges h d k w R))) :
    MatchingEntry.ends p (exposedSite h d k w R) (exposedDistinct p) (exposedOrder h d k w R) i=
      chord p (bucket (exposedOrder h d k w R i)) := by
  have raw (e : exposedEdges h d k w R) :
      orderedChord ((matchGraph p (exposedSite h d k w R)).tail e)
        ((matchGraph p (exposedSite h d k w R)).head e) (exposedDistinct p e) =
        chord p (bucket e) := by
    rcases e with ⟨row,j⟩|v <;> rfl
  exact raw ((exposedOrder h d k w R) i)

/-- The lower digit within a real original role is the chronological rank on
that chord, regardless of the matching-selected opposite endpoint. -/
theorem earlier_eq (p : Equiv.Perm (Row h)) (e : exposedEdges h d k w R) :
    let ord:=exposedOrder h d k w R
    let loc:=MatchingEntry.ends p (exposedSite h d k w R) (exposedDistinct p) ord
    TaggedShorterCommonScan.earlier (NamedAperture.key loc) (fun _=>1) (ord.symm e).val (NamedAperture.key loc (ord.symm e))=digit e := by
  intro ord loc
  let b:=bucket e
  let offset:=base w R b
  let key:=NamedAperture.key loc
  have same {i j} (equal : key i=key j) : bucket (ord i)=bucket (ord j) := by
    apply chord_injective p
    rw [←numbered_chord p,←numbered_chord p]
    exact (Fintype.equivFin _).injective equal
  have start : TaggedShorterCommonScan.earlier key (fun _=>1) offset (key (ord.symm e))=0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have early:=Finset.mem_range.mp ht
    split
    · rename_i inRange
      split
      · rename_i eq
        have tag:=same eq
        rw [ord.apply_symm_apply] at tag
        have ix:=unit_index (ord ⟨t,inRange⟩)
        rw [show (exposedOrder h d k w R).symm (ord ⟨t,inRange⟩)=⟨t,inRange⟩ from ord.symm_apply_apply _] at ix
        rw [tag] at ix
        change t=offset+_ at ix
        omega
      · rfl
    · rfl
  have steps (j : ℕ) (bound : j≤ capacity w R b) :
      TaggedShorterCommonScan.earlier key (fun _=>1) (offset+j) (key (ord.symm e))=j := by
    induction j with
    | zero => simpa only [Nat.add_zero] using start
    | succ j ih =>
      let u:=edge w R b ⟨j,by omega⟩
      let i:=ord.symm u
      have num : i.val=offset+j:=edge_index b ⟨j,by omega⟩
      have bucketEq : key i=key (ord.symm e) := by
        apply congrArg (Fintype.equivFin _)
        dsimp only [loc,ord]
        rw [numbered_chord p,numbered_chord p]
        change chord p (bucket (ord (ord.symm u)))=chord p (bucket (ord (ord.symm e)))
        rw [ord.apply_symm_apply,ord.apply_symm_apply]
        exact congrArg (chord p) (edge_bucket b _)
      have fit : offset+j< Fintype.card (exposedEdges h d k w R) := num ▸ i.isLt
      unfold TaggedShorterCommonScan.earlier at *
      rw [←Nat.add_assoc,Finset.sum_range_succ,dite_eq_left fit,show (⟨offset+j,fit⟩:_)=i from Fin.ext num.symm,ite_eq_left bucketEq,ih (by omega)]
  rw [unit_index]
  exact steps (digit e) (digit_lt e).le

end Hierarchy.ProbeStage.CoreBoard.EntryOrder
end

end OAI
