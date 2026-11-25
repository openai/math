import OAI.Hierarchy.DescentResetStencilAddressBook
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Linear logarithmic address width for the literal reset split, cutoff and stencil -/
namespace Hierarchy.DescentPlainTerminal.Suffix.StencilBook
open DescentDatedAddressBook DescentSIMDLookup DescentPacking.PackedMatch.Local DescentPackedColony Filter
noncomputable section
variable {ι : ℕ→Type*}
structure ScalarRoom (S : ∀h,ι h→StencilBook) where
  hosts : Bounded (fun h i=>(S h i).hosts)
  groups : Bounded (fun h i=>2^(S h i).c)
  lanes : Bounded (fun h i=>(S h i).M)
  blocks : Bounded (fun h i=>2^(S h i).r)
  axes : Bounded (fun h i=>(S h i).m)
  degree : Bounded (fun h i=>(S h i).degree)
  widths : ∃K : ℕ,∀ᶠ h:ℕ in atTop,∀i,let s:=S h i;let n:=s.n*Stencil.count s.r (s.degree+s.degree);
    DescentPackedColony.unit s.r s.b*s.M≤K*h ∧ s.levels+s.total≤K*h ∧
    Stencil.ReaderTables.largest s.r s.m s.n s.b s.M≤K*h ∧
    (2^s.r*s.m+2^s.r)*s.M≤K*h ∧ (n+s.n)*s.M≤K*h

theorem extent_rate (S : ∀h,ι h→StencilBook) (b : ScalarRoom S) :
    Bounded (fun h i=>(S h i).endAddress 0) := by
  obtain ⟨K,fit⟩:=b.widths
  have cuts:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).2.1)
  have rowKey:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).1)
  have dir:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).2.2.1)
  have met:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).2.2.2.1)
  have gather:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).2.2.2.2)
  have lev : Bounded (fun h i=>2^(S h i).levels) :=
    cuts.of_le fun _ _=>Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)
  have narrow : Bounded (fun h i=>2^((S h i).b*2^(S h i).r*(S h i).M)) := by
    apply dir.of_le
    intro h i
    unfold Stencil.ReaderTables.largest
    exact Nat.pow_le_pow_right (by decide) ((Nat.le_max_left ..).trans (Nat.le_max_right ..))
  have mask : Bounded (fun h i=>2^((S h i).n*Stencil.count (S h i).r ((S h i).degree+(S h i).degree)*(S h i).M)) :=
    gather.of_le fun _ _=>Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
  have batch : Bounded (fun h i=>chunks (2^(S h i).c) (S h i).M) :=
    (b.groups.add b.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows : Bounded (fun h i=>(S h i).rows) := b.hosts.mul batch
  have rowPage:=rows.padded
  have hp:=b.hosts.padded
  have depth : Bounded (fun h i=>(S h i).r) :=b.blocks.of_le fun _ _=>Nat.lt_two_pow_self.le
  have page : Bounded (fun h i=>2^(S h i).splitBits) := by
    have head:=(b.hosts.max' rows).logPage
    apply (head.max' rowKey).of_le
    intro h i
    simp only [splitBits,Frame.pageBits,StencilBook.rows]
    rcases le_total (max (S h i).hosts ((S h i).hosts*chunks (2^(S h i).c) (S h i).M)).log2.succ
      (DescentPackedColony.unit (S h i).r (S h i).b*(S h i).M) with hl|hl
    · rw [max_eq_right hl];exact Nat.le_max_right ..
    · rw [max_eq_left hl];exact Nat.le_max_left ..
  have count_ : Bounded (fun h i=>Stencil.count (S h i).r ((S h i).degree+(S h i).degree)) := by
    simp_rw [Stencil.count_eq]
    have blocks:=b.blocks;have degree:=b.degree
    repeat' first | assumption | apply Bounded.add | apply Bounded.mul | apply Bounded.const
  have keys : Bounded (fun h i=>Fintype.card (Stencil.ReaderTables.Key (S h i).r)) := by
    have blocks:=b.blocks
    have nodes:=((Bounded.const 1).add (blocks.add (depth.mul blocks))).add (blocks.pow 2)
    apply nodes.of_le
    intro h i
    rw [(S h i).socket_count]
  have host:=b.hosts;have degree:=b.degree;have axis:=b.axes
  simp_rw [extent]
  repeat' first | assumption | apply Bounded.add | apply Bounded.mul | apply Bounded.const

end
end Hierarchy.DescentPlainTerminal.Suffix.StencilBook

end OAI
