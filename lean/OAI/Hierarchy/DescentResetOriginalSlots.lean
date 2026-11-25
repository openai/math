import OAI.Hierarchy.ProtocolRAMDisjointPassReads
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Publishing an arbitrary family directly in the full rectangular original-word shelf -/
namespace Hierarchy.DescentResetOriginalSlots
open DescentSIMDLookup DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {X J K H G M w b : ℕ}

def stride (R : ℕ) :=2^(Nat.clog 2 R)
def offset (base rows K x j : ℕ) :=base+(x*K+j)*stride rows
def bank (base rows K x j : ℕ) : Bank:=⟨offset base rows K x j,Nat.clog 2 rows⟩
def finish (base rows X K : ℕ) :=base+X*K*stride rows
theorem rows_le (n : ℕ) : n ≤ stride n := Nat.le_pow_clog (by decide : 1<2) n

def cell (shelf : Fin J↪Fin K) (t : Fin (X*J)) : Fin (X*K) :=
  let p:=finProdFinEquiv.symm t
  finProdFinEquiv (p.1,shelf p.2)

theorem cell_inj (shelf : Fin J↪Fin K) : Function.Injective (cell (X:=X) shelf):=by
  intro a b eqn
  have e:=finProdFinEquiv.injective eqn
  apply finProdFinEquiv.symm.injective
  exact Prod.ext (congrArg (fun z : Fin X × Fin K => z.1) e)
    (shelf.injective (congrArg (fun z : Fin X × Fin K => z.2) e))

def passes (shelf : Fin J↪Fin K) (base rows : ℕ) (f : Fin (X*J)→Expr) : List Pass:=
  (List.finRange (X*J)).map (fun t=>⟨base+(cell shelf t).val*stride rows,rows,f t⟩)

theorem intervals (shelf : Fin J↪Fin K) (base n : ℕ) (f : Fin (X*J)→Expr) :
    (passes shelf base n f).Pairwise (fun a b=>a.out+a.rows≤b.out ∨ b.out+b.rows≤a.out):=by
  rw [passes,List.pairwise_map]
  apply (List.nodup_finRange (X*J)).imp
  intro a b different
  have ne : (cell shelf a).val≠(cell shelf b).val:=fun e=>different ((cell_inj shelf) (Fin.ext e))
  have cut (x y : ℕ) (less : x<y) : base+x*stride n+n≤base+y*stride n:=by
    have space:=Nat.mul_le_mul_right (stride n) less
    rw [Nat.succ_mul] at space
    have :=rows_le n
    omega
  exact (lt_or_gt_of_ne ne).imp (cut _ _) (cut _ _)

private theorem frame_list (ps : List Pass) (m : Memory w) (j : ℕ) (apart : ∀p∈ps,j<p.out ∨ p.out+p.rows≤j) :
    result ps m j=m j:=by
  induction ps generalizing m with
  | nil=>rfl
  | cons p tail ih=>
    exact (ih (p.apply m) (fun a hit=>apart a (.tail _ hit))).trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (apart p (.head _)))

theorem frame (shelf : Fin J↪Fin K) (base n : ℕ) (f : Fin (X*J)→Expr) (m : Memory w) (j : ℕ)
    (apart : ∀t : Fin (X*J),j<base+(cell shelf t).val*stride n ∨ base+(cell shelf t).val*stride n+n≤j) :
    result (passes shelf base n f) m j=m j:=by
  apply frame_list; intro p member
  obtain ⟨t,_,rfl⟩:=List.mem_map.mp member
  exact apart t

theorem earlier (shelf : Fin J↪Fin K) (base n : ℕ) (f : Fin (X*J)→Expr) (p : Pass) (seen : p∈passes shelf base n f) :
    base≤p.out ∧ p.out+p.rows≤finish base n X K:=by
  obtain ⟨t,_,rfl⟩:=List.mem_map.mp seen
  have space:=Nat.mul_le_mul_right (stride n) (cell shelf t).isLt
  rw [Nat.succ_mul] at space
  have :=rows_le n
  exact ⟨Nat.le_add_right ..,by change base+(cell shelf t).val*stride n+n≤base+X*K*stride n;omega⟩

theorem safe (shelf : Fin J↪Fin K) (base n : ℕ) (f : Fin (X*J)→Expr)
    (inputs : ∀t,(f t).Fits w base) (room : finish base n X K<2^w) :
    ∀p∈passes shelf base n f,p.Fits w:=by
  intro p hit;obtain ⟨lo,hi⟩:=earlier shelf base n f p hit
  obtain ⟨s,_,rfl⟩:=List.mem_map.mp hit
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ lo (inputs s),hi.trans_lt room⟩

theorem read (shelf : Fin J↪Fin K) (base n : ℕ) (f : Fin (X*J)→Expr) (m : Memory w) (t : Fin (X*J)) (fit : (f t).Fits w base) (r : Fin n) :
    result (passes shelf base n f) m (base+(cell shelf t).val*stride n+r.val)=(f t).eval m (r.val:Word w):=by
  let p : Pass:=⟨base+(cell shelf t).val*stride n,n,f t⟩
  have member : p∈passes shelf base n f:=List.mem_map.mpr ⟨t,List.mem_finRange _,rfl⟩
  exact ProtocolRAM.Calendar.FeedLayout.scheduled_read _ m p member r base fit
    (fun q h=>(earlier shelf base n f q h).1) (intervals shelf base n f)

theorem slot_read (shelf : Fin J↪Fin K) (base : ℕ) (f : Fin (X*J)→Expr) (m : Memory w)
    (x : Fin X) (j : Fin J) (v : Fin H→Fin G→Cell b) (fit : (f (finProdFinEquiv (x,j))).Fits w base)
    (seen : Source (f (finProdFinEquiv (x,j))) v M m) (p : Row H G M) :
    result (passes shelf base (H*chunks G M) f) m
        (offset base (H*chunks G M) K x.val (shelf j).val+(row H G M p).val)=((data v p).val:Word w):=by
  have h:=read shelf base (H*chunks G M) f m (finProdFinEquiv (x,j)) fit (row H G M p)
  simpa only [cell,Equiv.symm_apply_apply,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm,offset] using h.trans (seen p)

theorem frame_slot (shelf : Fin J↪Fin K) (base n : ℕ) (f : Fin (X*J)→Expr) (m : Memory w) (x : Fin X) (j : Fin K)
    (missing : ∀a,shelf a≠j) (r : Fin n) :
    result (passes shelf base n f) m (offset base n K x.val j.val+r.val)=m (offset base n K x.val j.val+r.val):=by
  apply frame;intro t
  let c : Fin (X*K):=finProdFinEquiv (x,j)
  have ne : (cell shelf t).val≠c.val:=by
    intro e
    exact missing (finProdFinEquiv.symm t).2 (congrArg Prod.snd (finProdFinEquiv.injective (Fin.ext e : cell shelf t=c)))
  have pos:=r.isLt
  have bound:=rows_le n
  have loc : offset base n K x.val j.val=base+c.val*stride n:=by simp [offset,c,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  rw [loc]
  rcases lt_or_gt_of_ne ne with lt|gt
  · right
    have step:=Nat.mul_le_mul_right (stride n) lt
    rw [Nat.succ_mul] at step;omega
  · left
    have step:=Nat.mul_le_mul_right (stride n) gt
    rw [Nat.succ_mul] at step;omega

end
end Hierarchy.DescentResetOriginalSlots

end OAI
