import OAI.Hierarchy.DescentDatedSourcePathPages
import OAI.Hierarchy.DescentSharedLeafImage

namespace OAI
/-! # A single physical broadcast header serves every old-source path -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentPackedZip DescentSIMDLookup DescentSharedCableNames DescentHaloWalkRAM
open DescentSixParty.Chronology DescentPackedColony DescentSharedLeafLookup
open DescentDatedAddressBook Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D H G M K w : ℕ}
local notation "P" => breadth D
local notation "b" => Packed.bits P

def stop (base H G M D : ℕ) := Public.stop (hostEnd base H D) H G M (Packed.bits (breadth D))
def chart (base H G M : ℕ) (p : Fin P) (d : Fin (D+1)) :=
  Public.header (hostEnd base H D) H G M b (hostBank base H p d)
def broadcast (base H G M D w : ℕ) : NativePhase w :=
  let I:=Public.literals (hostEnd base H D) 1 H G M (Packed.bits (breadth D)) w
  ⟨I.program,4+10*I.length,I.output,I.hardware.1⟩
def allPages (B : Banks) (base H G M D w : ℕ) : NativePhase w :=
  ((hostJob B H D).atBase base w).seq (broadcast base H G M D w)

theorem end_le (base H G M D : ℕ) : hostEnd base H D≤ stop base H G M D := by
  exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)

theorem geometry (base : ℕ) (p : Fin P) (d : Fin (D+1)) (space : stop base H G M D<2^w) :
    Readable (chart base H G M p d) 1 H G M b w (stop base H G M D) := by
  let lo:=hostEnd base H D
  let pad:=Public.stride H G M
  let rep:=2^Nat.clog 2 (Public.words b M)
  have high : stop base H G M D=lo+2*pad+rep :=rfl
  have index:=Nat.mul_le_mul_right (stride H) (pairIndex p d).isLt
  rw [Nat.succ_mul] at index
  have rankEnd:(hostBank base H p d).base+(hostBank base H p d).size≤lo:=by
    change base+(pairIndex p d).val*stride H+stride H≤base+_*stride H
    omega
  have bankfit (B : Bank) (h : B.base+B.size≤ stop base H G M D) : B.Fits w (stop base H G M D) :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (h.trans_lt space),h⟩
  refine ⟨?_,?_,Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _⟩
  · intro B h
    simp only [chart,Public.header,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact bankfit _ (rankEnd.trans (end_le ..))
    · apply bankfit
      change lo+pad ≤ stop base H G M D
      rw [high]
      exact (Nat.add_le_add_left (by omega : pad≤2*pad) lo).trans (Nat.le_add_right ..)
    · apply bankfit
      change lo+pad+pad ≤ stop base H G M D
      rw [high, two_mul, ← Nat.add_assoc]
      exact Nat.le_add_right ..
    · exact bankfit _ (by change lo+2*pad+rep≤_;omega)
  · change H*1≤2^Nat.clog 2 H
    simpa only [Nat.mul_one] using (Nat.le_pow_clog (by decide : 1<2) H)

theorem all_issued (B : Banks) (base : ℕ) (fit : Fits B H P base w) (space : stop base H G M D<2^w)
    (R : Fin H → Fin D → Option (Fin H)) (m : Memory w) (data : Reads B (Gather.reaching R) m) :
    let phase:=allPages B base H G M D w
    phase.Runs m ∧ (∀i,i<base ∨ stop base H G M D≤ i → phase.image m i=m i) ∧
      ∀(p : Fin P) (d : Fin (D+1)),
        Fixed (chart base H G M p d) 1 H G M b (phase.image m) ∧
          ∀v:Fin H,phase.image m ((hostBank base H p d).base+v.val)=
            (value (Gather.reaching R) v p (shortPath d):Word w) := by
  intro phase
  let hot:=(hostJob B H D).atBase base w
  let mid:=hot.image m
  let lo:=hostEnd base H D
  let I:=Public.literals lo 1 H G M b w
  have low:lo≤ stop base H G M D:=end_le ..
  have earlier:=host_issued B base fit (low.trans_lt space) R m data
  have room:I.low+I.length<2^w:=by
    change lo+(stop base H G M D-lo)<2^w
    rwa [Nat.add_sub_of_le low]
  have installed:=I.issue mid room
  have run:(broadcast base H G M D w).Runs mid:=installed.1
  refine ⟨NativePhase.seq_runs hot _ m earlier.1 run,?_,?_⟩
  · intro i side
    rcases side with pre|post
    · exact (installed.2.2 i (.inl (pre.trans_le (Nat.le_add_right ..)))).trans (earlier.2.2 i (.inl pre))
    · exact (installed.2.2 i (.inr post)).trans (earlier.2.2 i (.inr (low.trans post)))
  · intro p d
    refine ⟨Public.mounted lo 1 H G M b _ _ installed.2.1,?_⟩
    intro v
    have index:=Nat.mul_le_mul_right (stride H) (pairIndex p d).isLt
    rw [Nat.succ_mul] at index
    have inside:v.val<stride H:=v.isLt.trans_le (Nat.le_pow_clog (by decide) _)
    have prior:(hostBank base H p d).base+v.val<lo:=by
      change base+(pairIndex p d).val*stride H+v.val<base+_*stride H
      omega
    exact (installed.2.2 _ (.inl prior)).trans (earlier.2.1 p d v)

theorem all_cost (B : Banks) (base H G M D w : ℕ) :
    let work:=(breadth D+1)*(30+4*breadth D+4*(breadth D*breadth D))
    let job:=hostJob B H D
    let pages:=stop base H G M D-hostEnd base H D
    (allPages B base H G M D w).ticks≤job.clocks work+(4+10*pages) ∧
      DescentStaticWordColumn.names (allPages B base H G M D w).program≤job.textSize work+15*(pages+1) := by
  intro work job pages
  have head:=host_cost B H D base w
  let I:=Public.literals (hostEnd base H D) 1 H G M (Packed.bits (breadth D)) w
  refine ⟨Nat.add_le_add_right head.1 _,?_⟩
  change DescentStaticWordColumn.names ((job.atBase base w).program.seq I.program)≤_
  rw [DescentStaticWordColumn.names_seq]
  exact Nat.add_le_add head.2 I.hardware.2.le

end
end Hierarchy.DescentDatedSourcePathDirectory

end OAI
