import OAI.Hierarchy.TaggedWideOutputPlane
import OAI.Hierarchy.ProtocolStackContraction
import OAI.Hierarchy.TaggedShorterFields

namespace OAI
/-! # Reading the original row after the shorter stack assignments are identified -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open TaggedShorterFields ProtocolStackContraction
open scoped Classical
variable {R G T : Type} [Fintype G] [Fintype T] {ports lanes : ℕ}
    (width : T→ℕ) (bits : R→ℕ) (kind : R→T) (anchor : R×Bool ↪ G×Fin ports)
    (count : T→G→ℕ)
    (place : ∀t g,Bool→Fin (count t g) ↪ Fin (ports*lanes))
    (row : ∀ t g,Fin (count t g)→R) (part : ∀t g,Fin (count t g)→Fin lanes)

def afterCuts (words : (r:R)→Fin (bits r)→Bool) : OutputData T G ports lanes width→Bool :=
  fun a=>encode (place a.1) (fun _=>false)
    (fun e=>slice (width a.1) (words (row a.1 e.1 e.2)) (part a.1 e.1 e.2).val) a.2.1 a.2.2

variable (classAt : ∀t g u,kind (row t g u)=t)
    (groupAt : ∀t g u side,(anchor (row t g u,side)).1=g)
    (locate : ∀t g u side,place t g side u=fixedSlot le_rfl ((anchor (row t g u,side)).2,part t g u))
    (cover : ∀r side (j : Fin (bits r)),
      let t := kind r
      let g := (anchor (r,side)).1
      ∃ u : Fin (count t g),row t g u=r ∧ (part t g u).val=j.val/width t)

private theorem slice_read {n w : ℕ} (x : Fin n→Bool) (k : ℕ) (b : Fin w) (j : Fin n)
    (index : k*w+b.val=j.val) : slice w x k b=x j := by
  have live : k*w+b.val<n := by rw [index]; exact j.isLt
  rw [slice,dite_eq_left live]
  exact congrArg x (Fin.ext index)

include classAt groupAt locate cover

omit [Fintype G] in
/-- On the actual two-ended placement, the OR shelf returns the true
absolute bit of each live edge. The only inputs concerning a dense common
ID are its literal owning record, type, packed slot, and subslot number. -/
theorem output_slice_bit (words : (r:R)→Fin (bits r)→Bool) (positive : ∀t,0<width t)
    (r : R) (side : Bool) (j : Fin (bits r)) :
    positivePlane width (afterCuts width bits count place row part words) (anchor (r,side)) j.val=words r j := by
  let data := afterCuts width bits count place row part words
  have origin (t : T) (s : Bool) (p : G×Fin ports) (j : ℕ)
      (on : (candidateBit width p j t s).elim false data=true) :
      ∃r,anchor (r,s)=p ∧ kind r=t ∧ ∃d : Fin (bits r),d.val=j ∧ words r d=true := by
    by_cases ok : 0<width t ∧ j/width t<lanes
    · let pos := fixedSlot (D:=ports*lanes) le_rfl (p.2,⟨j/width t,ok.2⟩)
      let b : Fin (width t) := ⟨j%width t,Nat.mod_lt _ ok.1⟩
      let labels := fun e : Edge (count t)=>slice (width t) (words (row t e.1 e.2)) (part t e.1 e.2).val
      have hot : encode (place t) (fun _=>false) labels (some p.1,s,pos) b=true := by
        simpa only [candidateBit,dite_eq_left ok,Option.elim_some,data,afterCuts,pos,b,labels] using on
      have used : pos∈Set.range (place t p.1 s) := by
        by_contra miss
        have blank := (encoded_valid (place t) (fun _=>false) labels).1.2 p.1 s pos miss
        simp [blank] at hot
      obtain ⟨u,slot⟩ := used
      have addresses := (fixedSlot (D:=ports*lanes) le_rfl).injective ((locate t p.1 u s).symm.trans slot)
      let z := row t p.1 u
      have atSite : anchor (z,s)=p := Prod.ext (groupAt t p.1 u s) (congrArg Prod.fst addresses)
      have next : (part t p.1 u).val=j/width t := congrArg (fun e : Fin ports × Fin lanes=>e.2.val) addresses
      have restore : (part t p.1 u).val*width t+b.val=j := by
        rw [next]
        exact (Nat.div_add_mod j (width t)) |> (fun h=>by simpa [b,Nat.mul_comm] using h)
      rw [←slot,encode_active] at hot
      change (if h : (part t p.1 u).val*width t+b.val<bits z then words z ⟨_,h⟩ else false)=true at hot
      split at hot
      next h => exact ⟨z,atSite,classAt t p.1 u,⟨_,h⟩,restore,hot⟩
      next => contradiction
    · simp [candidateBit,ok] at on
  apply output_bit width anchor bits kind words data origin _ r side j
  intro r s j trueBit
  let t := kind r
  let g := (anchor (r,s)).1
  obtain ⟨u,rowAt,subslot⟩ := cover r s j
  change row t g u=r at rowAt
  change (part t g u).val=j.val/width t at subslot
  have room : j.val/width t<lanes := subslot ▸ (part t g u).isLt
  let c : Fin lanes := ⟨j.val/width t,room⟩
  let b : Fin (width t) := ⟨j.val%width t,Nat.mod_lt _ (positive t)⟩
  have same : place t g s u=fixedSlot le_rfl ((anchor (r,s)).2,c) := by
    rw [locate,rowAt,show part t g u=c from Fin.ext subslot]
  have aperture : 0<width (kind r) ∧ j.val/width (kind r)<lanes := ⟨positive _,room⟩
  simp only [candidateBit,dite_eq_left aperture,Option.elim_some]
  change encode (place t) (fun _=>false) _ (some g,s,fixedSlot le_rfl ((anchor (r,s)).2,c)) b=true
  rw [←same,encode_active]
  have recover : (part t g u).val*width t+b.val=j.val := by
    change (part t g u).val*width t+j.val%width t=j.val
    rw [subslot,Nat.mul_comm]
    exact Nat.div_add_mod j.val (width t)
  change slice (width t) (words (row t g u)) (part t g u).val b=true
  exact (congrArg (fun z=>slice (width t) (words z) (part t g u).val b) rowAt).trans
    ((slice_read (words r) (part t g u).val b j recover).trans trueBit)

end Hierarchy.Tagged.WideStack

end
end OAI
