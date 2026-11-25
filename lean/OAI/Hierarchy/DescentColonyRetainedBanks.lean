import OAI.Hierarchy.DescentColonyAllSeedsRAM

namespace OAI
/-! # The full seed sweep preserves every actual permuted load and split flag -/

noncomputable section
namespace Hierarchy.DescentColonies
open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM NativeBatch
open DescentGL (Bits Nonzero)
open scoped Fin.CommRing

variable {G H k w : ℕ}

namespace SiteRAM

/-- The initial load column and its chronological split layers share one index. -/
def retainedBank (k base : ℕ) (layer : Option (Fin k)) (v : Fin H) := match layer with
  | none => bank k base v.val
  | some d => LayerRAM.address k (bank k base H) d.val v

def retainedValue (incoming : Fin H→List (Fin H)) (load : Fin H→Block k→ℕ) (D cap : ℕ) :
    Option (Fin k) → Fin H → Block k → ℕ
  | none,v,x => load v x
  | some d,v,x => (Scan.lookup (Scan.build incoming load D cap k) d.val v x).toNat

theorem retained_end (base : ℕ) (layer : Option (Fin k)) (v : Fin H) :
    retainedBank k base layer v+2^k≤ scoreAt H k base := by
  cases layer with
  | none => exact (transfer_bound _ _ v).trans (score_ge ..)
  | some d => exact PhysicalCensus.bank_before _ _ d.isLt v

theorem retained_read (base : ℕ) (incoming : Fin H→List (Fin H)) (p : Fin H→ℕ) (D cap : ℕ)
    (a μ : Bits k) (m : Memory w) (weight : Fin H→Block k→ℕ) (old : ∀i,p i+2^k≤base)
    (room : scoreAt H k base+1<2^w) (cf : cap<2^w)
    (loads : ∀i (x : Block k),m (p i+x.val)=(weight i x:Word w))
    («partial» : ∀d<k,∀v x,(Scan.readWeights (multiplierLoad weight a μ) d v x).sum<2^w)
    (layer : Option (Fin k)) (v : Fin H) (x : Block k) :
    (groupCode w k base incoming p D cap a μ).after m (retainedBank k base layer v+x.val)=
      (retainedValue incoming (multiplierLoad weight a μ) D cap layer v x:Word w) := by
  have earlier := (Nat.add_lt_add_left x.isLt _).trans_le (retained_end base layer v)
  apply (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl earlier)).trans
  have pulls := rearrange_read base p a μ m weight old ((score_ge _ _ _).trans_lt (by omega)) loads
  cases layer with
  | none =>
    exact (LayerRAM.below _ ((Nat.add_lt_add_left x.isLt _).trans_le (transfer_bound _ _ v))).trans (pulls v x)
  | some d =>
    exact LayerRAM.published _ _ (fun u=>transfer_bound k base u) (by change scoreAt H k base<2^w;omega) cf
      pulls «partial» d.val d.isLt v x

end SiteRAM

namespace CandidateRAM

def permBank (base : ℕ) (g : Fin G) (v : Fin H) (k : ℕ) := SiteRAM.bank k (output g.val H k base) v.val

def retainedBank (base : ℕ) (g : Fin G) (v : Fin H) (layer : Option (Fin k)) :=
  SiteRAM.retainedBank k (output g.val H k base) layer v

theorem retained_end (base : ℕ) (g : Fin G) (v : Fin H) (layer : Option (Fin k)) :
    retainedBank base g v layer+2^k≤output G H k base := by
  have one := SiteRAM.retained_end (output g.val H k base) layer v
  have nextSlot : SiteRAM.scoreAt H k (output g.val H k base)<output G H k base :=
    (next g.val H k base).le.trans (mono _ _ _ g.isLt)
  exact one.trans nextSlot.le

theorem retained_read (base : ℕ) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) (m : Memory w) (weight : Fin G→Fin H→Block k→ℕ)
    (old : ∀g i,ptr g i+2^k≤base) (room : output G H k base+1<2^w) (cf : cap<2^w)
    (loads : ∀g i (x : Block k),m (ptr g i+x.val)=(weight g i x:Word w))
    («partial» : ∀g d,d<k→∀v x,(Scan.readWeights (multiplierLoad (weight g) a μ.val) d v x).sum<2^w)
    (g : Fin G) (v : Fin H) (layer : Option (Fin k)) (x : Block k) :
    after base incoming ptr D cap a μ m (retainedBank base g v layer+x.val)=
      (SiteRAM.retainedValue incoming (multiplierLoad (weight g) a μ.val) D cap layer v x:Word w) := by
  let step := steps w base incoming ptr D cap a μ
  let Init := fun M : Memory w=>∀j i (y : Block k),M (ptr j i+y.val)=(weight j i y:Word w)
  let Claim := fun i : Fin G=>fun M : Memory w=>M (retainedBank base i v layer+x.val)=
      (SiteRAM.retainedValue incoming (multiplierLoad (weight i) a μ.val) D cap layer v x:Word w)
  have stable (j : Fin G) (M : Memory w) (h : Init M) : Init ((step j).after M) := by
    intro i u y
    exact (SiteRAM.below _ _ _ _ _ _ _ _ _ (((Nat.add_lt_add_left y.isLt _).trans_le (old i u)).trans_le
      (start j.val H k base))).trans (h i u y)
  have now (j : Fin G) (M : Memory w) (h : Init M) : Claim j ((step j).after M) := by
    have siteRoom : SiteRAM.scoreAt H k (output j.val H k base)+1<2^w := by
      rw [next]
      exact (mono H k base j.isLt).trans_lt (by omega)
    exact SiteRAM.retained_read (output j.val H k base) incoming (ptr j) D cap a μ.val M (weight j)
      (fun i=>(old j i).trans (start j.val H k base)) siteRoom cf (h j) («partial» j) layer v x
  have keep (i j : Fin G) (h : i<j) (M : Memory w) (ok : Claim i M) : Claim i ((step j).after M) := by
    apply (SiteRAM.below _ _ _ _ _ _ _ _ _ ?_).trans ok
    have edge := SiteRAM.retained_end (output i.val H k base) layer v
    have hi : SiteRAM.scoreAt H k (output i.val H k base)<output j.val H k base :=
      (next i.val H k base).le.trans (mono _ _ _ h)
    exact ((Nat.add_lt_add_left x.isLt _).trans_le edge).trans hi
  apply (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl ((Nat.add_lt_add_left x.isLt _).trans_le
    (retained_end base g v layer)))).trans
  exact (Code.read_seq step Init stable Claim now keep m loads G le_rfl).2 g g.isLt

end CandidateRAM

namespace AllSeedsRAM

def retainedBank (base : ℕ) (i : Fin (2^k-1)) (g : Fin G) (v : Fin H) (layer : Option (Fin k)) :=
  CandidateRAM.retainedBank (slot G H k base i.val) g v layer

theorem retained_end (base : ℕ) (i : Fin (2^k-1)) (g : Fin G) (v : Fin H) (layer : Option (Fin k)) :
    retainedBank base i g v layer+2^k≤last G H k base i.val :=
  CandidateRAM.retained_end _ g v layer

theorem retained_read (base D cap : ℕ) (a : Bits k) (incoming : Fin H→List (Fin H))
    (ptr : Fin G→Fin H→ℕ) (m : Memory w) (weights : Fin G→Fin H→Block k→ℕ)
    (old : ∀g i,ptr g i+2^k≤base) (room : slot G H k base (2^k-1)<2^w) (cf : cap<2^w)
    (loads : ∀g i (x : Block k),m (ptr g i+x.val)=(weights g i x:Word w))
    («partial» : ∀(μ : Nonzero k) g d,d<k→∀v x,(Scan.readWeights (multiplierLoad (weights g) a μ.val) d v x).sum<2^w)
    (i : Fin (2^k-1)) (g : Fin G) (v : Fin H) (layer : Option (Fin k)) (x : Block k) :
    (stage w base D cap a incoming ptr).after m (retainedBank base i g v layer+x.val)=
      (SiteRAM.retainedValue incoming (multiplierLoad (weights g) a (seedAt k i).val) D cap layer v x:Word w) := by
  let step := steps w base D cap a incoming ptr
  let Init := fun M : Memory w=>∀j u (y : Block k),M (ptr j u+y.val)=(weights j u y:Word w)
  let Claim := fun j : Fin (2^k-1)=>fun M : Memory w=>M (retainedBank base j g v layer+x.val)=
    (SiteRAM.retainedValue incoming (multiplierLoad (weights g) a (seedAt k j).val) D cap layer v x:Word w)
  have stable (j : Fin (2^k-1)) (M : Memory w) (h : Init M) : Init ((step j).after M) := by
    intro l u y
    exact (CandidateRAM.below _ _ _ _ _ _ _ _ _ (((Nat.add_lt_add_left y.isLt _).trans_le (old l u)).trans_le
      (Nat.le_add_right ..))).trans (h l u y)
  have now (j : Fin (2^k-1)) (M : Memory w) (h : Init M) : Claim j ((step j).after M) := by
    have candidateRoom : last G H k base j.val+1<2^w := by
      rw [next]
      exact (mono G H k base j.isLt).trans_lt room
    exact CandidateRAM.retained_read (slot G H k base j.val) incoming ptr D cap a (seedAt k j) M weights
      (fun l u=>(old l u).trans (Nat.le_add_right ..)) candidateRoom cf h («partial» (seedAt k j)) g v layer x
  have keep (l j : Fin (2^k-1)) (h : l<j) (M : Memory w) (ok : Claim l M) : Claim l ((step j).after M) := by
    apply (CandidateRAM.below _ _ _ _ _ _ _ _ _ ?_).trans ok
    have prior : last G H k base l.val<slot G H k base j.val :=
      (next G H k base l.val).le.trans (mono G H k base h)
    exact ((Nat.add_lt_add_left x.isLt _).trans_le (retained_end base l g v layer)).trans prior
  exact (Code.read_seq step Init stable Claim now keep m loads _ le_rfl).2 i i.isLt

end AllSeedsRAM
end Hierarchy.DescentColonies

end
end OAI
