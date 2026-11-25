import OAI.Hierarchy.ProtocolRAMSiteCounts
import OAI.Hierarchy.ProtocolRAMEndpointPrefix
import OAI.Hierarchy.ProtocolRAMEndpointScatter

namespace OAI
/-! # Linear-time stable native sorting of endpoint ordinals -/

namespace Hierarchy.ProtocolRAMEndpointSort

open Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
open Computability.BorderVNP.FragmentBucket
open scoped Fin.CommRing

variable {w n sites : ℕ}

structure Layout where
  src : ℕ
  counts : ℕ
  starts : ℕ
  sorted : ℕ

structure Layout.Fits (L : Layout) (w n sites : ℕ) : Prop where
  src_safe : L.src+n ≤ L.counts
  count_safe : L.counts+sites ≤ L.starts
  prefix_safe : L.starts+sites+1 ≤ L.sorted
  room : L.sorted+n<2^w

def program (L : Layout) (w n sites : ℕ) : Procedure w :=
  ((ProtocolRAMSiteCounts.program w L.src L.counts n sites).seq
    (ProtocolRAMEndpointPrefix.exclusive w L.counts L.starts sites)).seq
    (ProtocolRAMEndpointScatter.scatter w L.src L.starts L.sorted n)

def image (L : Layout) (site : Fin n→Fin sites) (m : Memory w) : Memory w :=
  ProtocolRAMEndpointScatter.image site L.starts L.sorted
    (ProtocolRAMEndpointPrefix.image L.starts (start site)
      (ProtocolRAMSiteCounts.image L.counts site m) sites) n

def cost (n sites : ℕ) := ((4+6*sites)+(3+11*n))+(10+(3+12*sites))+(3+14*n)

theorem cost_eq (n sites : ℕ) : cost n sites = 23+25*n+18*sites := by unfold cost; omega

/-- The entire machine sees the endpoint column in original order. It clears its bins,
counts the rows at each site, builds exclusive starts, and scatters original row numbers. -/
theorem run (L : Layout) (fits : L.Fits w n sites) (site : Fin n→Fin sites) (m : Memory w)
    (input : ∀ i : Fin n, m (L.src+i.val)=((site i).val:Word w)) :
    (program L w n sites).Exec m (image L site m) (cost n sites) := by
  have h₁ := fits.src_safe
  have h₂ := fits.count_safe
  have h₃ := fits.prefix_safe
  have h₄ := fits.room
  let a := ProtocolRAMSiteCounts.image L.counts site m
  let b := ProtocolRAMEndpointPrefix.image L.starts (start site) a sites
  have hist : (ProtocolRAMSiteCounts.program w L.src L.counts n sites).Exec m a ((4+6*sites)+(3+11*n)) := ProtocolRAMSiteCounts.run L.src L.counts site m h₁ (by omega) input
  have pre : (ProtocolRAMEndpointPrefix.exclusive w L.counts L.starts sites).Exec a b (10+(3+12*sites)) := ProtocolRAMEndpointPrefix.run L.counts L.starts sites (start site) a h₂
    (by omega) (start_zero site) (by
      intro t ht
      let s : Fin sites := ⟨t,ht⟩
      have num := start_step site s
      have read : a (L.counts+t)=(count site s:Word w) := ProtocolRAMSiteCounts.bin L.counts site m s
      change start site (t+1)=start site t+count site s at num
      rw [read,num,Nat.cast_add])
  apply Procedure.Exec.then (Procedure.Exec.then hist pre)
  apply Procedure.Spec.exec (ProtocolRAMEndpointScatter.run site L.src L.starts L.sorted (by omega) (by omega) h₄) b
  constructor
  · intro i
    have below : L.src+i.val < L.counts := by have := i.isLt; omega
    exact ((ProtocolRAMEndpointPrefix.frame L.starts (start site) a sites _ (.inl (by omega))).trans
      (ProtocolRAMSiteCounts.frame L.counts site m _ (.inl below))).trans (input i)
  · intro s
    exact ProtocolRAMEndpointPrefix.read L.starts (start site) a sites s.val s.isLt.le

theorem read (L : Layout) (fits : L.Fits w n sites) (site : Fin n→Fin sites) (m : Memory w)
    (j : Fin n) : image L site m (L.sorted+j.val)=(((dest site).symm j).val:Word w) := by
  have sep := fits.prefix_safe
  simpa only [image,Equiv.apply_symm_apply] using
    ProtocolRAMEndpointScatter.sorted site L.starts L.sorted
      (ProtocolRAMEndpointPrefix.image L.starts (start site)
        (ProtocolRAMSiteCounts.image L.counts site m) sites)
      (by omega) n le_rfl ((dest site).symm j) ((dest site).symm j).isLt

theorem frame (L : Layout) (_fits : L.Fits w n sites) (site : Fin n→Fin sites) (m : Memory w)
    (a : ℕ) (hc : a < L.counts ∨ L.counts+sites ≤ a)
    (hs : a < L.starts ∨ L.starts+sites+1 ≤ a) (ho : a < L.sorted ∨ L.sorted+n ≤ a) :
    image L site m a=m a :=
  ((ProtocolRAMEndpointScatter.frame site L.starts L.sorted _ n a (by omega) ho).trans
    (ProtocolRAMEndpointPrefix.frame L.starts (start site) _ sites a (by omega))).trans
    (ProtocolRAMSiteCounts.frame L.counts site m a hc)


end Hierarchy.ProtocolRAMEndpointSort

end OAI
