import OAI.Hierarchy.TraceReceiverCommandHeader
import OAI.Hierarchy.TraceReceiverDecodedTask
import OAI.Hierarchy.TraceReceiverGatherRoom
import OAI.Hierarchy.TraceReceiverGatherPrepared

namespace OAI
/-! # The real terminal task and saved wires issue an executable S9 command -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat RAM HistoryJoinScan HistoryCommandTable HistoryCompiledRows
open Diagonal Diagonal.HistoryContraction Computability.VPVNP.BurstRAM PrivateRAM BitNetwork.Ordered
open scoped Fin.CommRing Classical BigOperators

variable {F : Type*} {w u n p : ℕ} {arity : Fin n→ℕ}
variable (nets : ∀ i,BitNetwork F (arity i)) (wires : ∀ i,Fin (arity i)→Fin p)
variable (tag : ((Fin 3→Bool)→F)→ℕ)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "D" => GridReceiverBanks.tasks w
local notation "ctrl" => GridReceiverBanks.cursor w
local notation "cmd" => GridReceiverBanks.commands w
local notation "base" => TickWorkspace.base u 9
local notation "rows" => (fun i=>(nets i).cells)
local notation "bits" => (fun i=>(nets i).internal)
local notation "B" => GridReceiverBanks.base w
local notation "G" => GridReceiverBanks.gap w

/-- Physically returned S12 data, S13 headers and per-root saved maps
suffice for all command and anti-alias observations in the actual cursor image. -/
theorem issued_terminal (large : 7≤w) (age : u^10≤5*w) (count : ℕ) (mapped : Memory W)
    (i : Fin n) (node stream : ℕ)
    (jobs : 5*n≤G) (size : 4*(∑ j,rows j)≤TickWorkspace.stride u)
    (pinSum : (∑ j,arity j)≤G) (hidden : (nets i).internal≤G) (tables : ∀ t,tag t<2^W)
    (sourceLo : TickWorkspace.base u 12≤ stream)
    (sourceHi : stream+4*(nets i).cells≤TickWorkspace.base u 14)
    (rangedTask : let r:=TraceReceiverTasks.rangeImage (D).current count cmd 0 7 mapped
      readTask r (((D).tasks+5*i.val:ℕ):Word W)=⟨(node:Word W),(D).parent,
        (((D).maps+Tree.before arity i:ℕ):Word W),(Tree.before rows i:Word W),(Tree.before bits i:Word W)⟩)
    (rangedNode : let r:=TraceReceiverTasks.rangeImage (D).current count cmd 0 7 mapped
      readNode r (node:Word W)=⟨(stream:Word W),arity i,(nets i).cells,(nets i).internal⟩)
    (rangedParent : let r:=TraceReceiverTasks.rangeImage (D).current count cmd 0 7 mapped
      readNode r ((D).parent:Word W)=⟨(base:Word W),p,0,0⟩)
    (rec : Records tag (nets i) stream mapped)
    (saved : ∀ j : Fin (arity i),
      mapped ((D).maps+Tree.before arity i+j.val)=((2+(wires i j).val:ℕ):Word W)) :
    let ranged:=TraceReceiverTasks.rangeImage (D).current count cmd 0 7 mapped
    let out:=Issued.image ctrl cmd (D).tasks n ranged
    ∃ h mapPin,IssuedRoot nets wires tag (ctrl:Word W) base cmd out i h mapPin ∧
      out (cmd+7*i.val+6)=((h.dest+4*(nets i).cells:ℕ):Word W) := by
  intro ranged out
  let h : Header ℕ:=⟨stream,base+4*Tree.before rows i,(D).maps+Tree.before arity i,arity i,p,Tree.before bits i⟩
  let mapPin (j : ℕ):=if hj : j<arity i then 2+(wires i ⟨j,hj⟩).val else 0
  obtain ⟨bank,roof,space⟩:=grid_window large age
  have cp : ctrl=B+32:=rfl
  have hi : cmd=B+9*G:=rfl
  have mp : (D).maps=B+2*G:=rfl
  have hd : (D).current=B:=rfl
  have earlier:=TickWorkspace.apart (u:=u) (by decide : 9<12)
  have archive:=TickWorkspace.apart (u:=u) (by decide : 14<45)
  have low:=TickWorkspace.apart (u:=u) (by decide : 12<14)
  have trail : 4*(Tree.before rows i+(nets i).cells)≤TickWorkspace.stride u :=
    (Nat.mul_le_mul_left 4 (Tree.prefix_next_le rows i)).trans size
  have lastPin:=(Tree.prefix_next_le arity i).trans pinSum
  have s9 : h.dest+4*(nets i).cells≤TickWorkspace.base u 12:=by
    change base+4*Tree.before rows i+4*(nets i).cells≤_
    omega
  obtain ⟨limit,quietRow,quietPin,quietCmd⟩:=gather_untouched rows large age i (by omega) size
  have room:=gather_room nets tag large age i h sourceHi rfl rfl pinSum hidden tables
  have ptr:=Issued.terminal_command ctrl cmd (D).tasks n ranged i node (D).parent stream (arity i)
    (nets i).cells (nets i).internal base p ((D).maps+Tree.before arity i) (Tree.before rows i)
    (Tree.before bits i) (by rw [cp,hi];omega) limit rangedTask rangedNode rangedParent
  have same {a : ℕ} (band : a<B ∨ B+2*G≤a ∧ a<B+3*G) : out a=mapped a := by
    exact (Issued.frame ctrl cmd (D).tasks n a ranged (by rw [cp];omega) (by rw [hi];omega)).trans
      (Issued.header_frame (D).current count cmd mapped (by rw [hd];omega))
  refine ⟨h,mapPin,⟨rfl,ptr.1,⟨rfl,rfl,by simp [h,Tree.before]⟩,?_,room.1,room.2.1,
    room.2.2.1,room.2.2.2,?_,?_,quietCmd,?_,?_,?_,Or.inr (s9.trans sourceLo),?_⟩,ptr.2⟩
  · intro j
    simp [mapPin,j.isLt,resolve,BitLayout.sourceAddress]
  · intro r c
    have rt:=r.isLt
    have ct:=c.isLt
    exact (same (Or.inl (by change stream+(4*r.val+c.val)<B;omega))).trans (rec r c)
  · intro j hj
    change j<arity i at hj
    have ok : B+2*G≤(D).maps+Tree.before arity i+j ∧ (D).maps+Tree.before arity i+j<B+3*G:=by rw [mp];omega
    exact (same (Or.inr ok)).trans (by simpa [mapPin,hj] using saved ⟨j,hj⟩)
  · intro r c
    have rt:=r.isLt
    have ct:=c.isLt
    exact quietRow _ (by change _≤ stream+(4*r.val+c.val);omega) (by change stream+(4*r.val+c.val)<_;omega)
  · intro j hj
    change j<arity i at hj
    apply quietPin
    · change B+2*G≤(D).maps+Tree.before arity i+j;rw [mp];omega
    · change (D).maps+Tree.before arity i+j<B+3*G;rw [mp];omega
  · intro c
    have ci:=c.isLt
    have ii:=i.isLt
    apply Or.inr
    change _≤(((cmd+7*i.val:ℕ):Word W)+(c.val:Word W)).val
    rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    omega
  · apply Or.inr
    change h.dest+4*(nets i).cells≤(D).maps+Tree.before arity i
    rw [mp];omega

end Hierarchy.TraceFactorReceiver.Gather
end

end OAI
