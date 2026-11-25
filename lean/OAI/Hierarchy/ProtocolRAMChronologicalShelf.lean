import OAI.Hierarchy.ProtocolRAMTurnShelfProgram
import OAI.Hierarchy.ProtocolRAMTurnInstalled
import OAI.Hierarchy.ProtocolRAMTurnCursor
import OAI.Hierarchy.ProtocolRAMTurnCost

namespace OAI
/-! # One measured CPU execution from the old role/paid words to every physical gate seat -/

noncomputable section
namespace Hierarchy.ProtocolRAMChronologicalShelf
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMTurnItinerary ProtocolRAMTurnChart
open scoped Fin.CommRing
variable {W N sites slots history occ edges : ℕ}

theorem run (header bits initial src sb rom rb base scratch sink : ℕ)
    (d : Data) (heads : Bank) (b : Banks) (v : Values) (u : Fin N → Geometry)
    (w : Words) (sitesAt : Fin N → ℕ) (head : ℕ → ℕ) (m : Memory W)
    («public» : Loaded header bits u m) (old : d.Before w m u) (safe : ProtocolRAMTurnCursor.Safe d W initial)
    (romSafe : ∀ f,(get header bits f).Fits W initial)
    (siteBase : d.site.base=initial+1+2*N) (siteRoom : N ≤ d.site.size)
    (within : ∀i,(u i).raw ≤ (u i).length) (lenFit : ∀i,(u i).length < 2^W) (one : 1 < 2^W)
    (geo : ProtocolRAMVisitColumns.Geography (walk header bits d b.edge b.tailSite heads) m
      (fun i=>(u i).raw) (fun i=>(u i).origin) (fun i=>(u i).item) sitesAt v.edge w.rawSource v.tailSite head)
    (input : ∀e∈ProtocolRAMVisitColumns.terms initial (initial+1+2*N) (walk header bits d b.edge b.tailSite heads),
      e.Fits W initial) (space : initial+1+3*N < 2^W)
    (bankReads : b.Reads v history occ edges m)
    (banksLow : ∀ a ∈ [b.oldSource,b.oldTarget,b.edge,b.tailSite,b.tailRole,b.headRole,b.starts],a.Fits W initial)
    (fit : ∀i,(record u w sitesAt i).Fits v W history occ edges)
    (fields : ∀ f,(field (chart header bits d) b f).Fits W src) (fieldRoom : src+7*N < 2^W)
    (put : ProtocolRAMTurnShelf.Live (ProtocolRAMTurnInstalled.columns (record u w sitesAt) v) ↪ ProtocolRAMTurnShelf.Seats sites slots)
    (loc : ∀ z,(put z).1.val=(record u w sitesAt z.val).site ∧ (put z).2.val=(record u w sitesAt z.val).seat)
    (romLow : rom+4*2^rb ≤ initial) (after : initial ≤ src)
    (directory : ∀ (j : Fin 4) (t : ℕ),t<2^rb →
      (ProtocolRAMTurnDirectory.bank rom rb j).read m (t:Word W)=
        ProtocolRAMTurnDirectory.words N sites slots base j t)
    (romRows : N*5 ≤ 2^rb) (romSites : sites ≤ 2^rb) (cap : 5*N ≤ 2^sb)
    (Wroom : 2^sb ≤ 2^W) (widthFit : ∀i,(record u w sitesAt i).width < 2^W)
    (before : base+5*(sites*slots) ≤ scratch) (scratchFit : scratch+(N*5)+(N*5) < 2^W)
    (sinkLow : sink < base)
    (af : (ProtocolRAMTurnShelf.addressExpr (ProtocolRAMTurnShelf.tables rom rb src sb N) sink).Fits W base)
    (vf : (ProtocolRAMTurnShelf.valueExpr (ProtocolRAMTurnShelf.tables rom rb src sb N)).Fits W base) :
    ∃ out,(program W N sites slots header bits initial src sb rom rb base scratch sink d heads b).Exec m out
        (72+6096*N+30*(sites*slots)) ∧
      (∀ (f : Fin 5) (s : ProtocolRAMTurnShelf.Seats sites slots),
        out (base+f.val*(sites*slots)+s.1.val*slots+s.2.val)=
          ProtocolRAMTurnShelf.entry (ProtocolRAMTurnInstalled.columns (record u w sitesAt) v) put f s) ∧
      ∀ a,(a < initial ∨ initial+1+3*N ≤ a) → (a < src ∨ src+7*N ≤ a) →
        (a < base ∨ base+5*(sites*slots) ≤ a) → (a < scratch ∨ scratch+10*N ≤ a) →
        a ≠ sink → out a=m a := by
  obtain ⟨mid,first,coords,frame⟩ := ProtocolRAMTurnCursor.run header bits initial d u w b.edge b.tailSite heads
    sitesAt v.edge v.tailSite head m «public» old safe romSafe siteBase siteRoom within lenFit one geo input space
  have keep (a : Bank) (ha : a.Fits W initial) (i : Word W) : a.read mid i=a.read m i :=
    frame _ (.inl ((Nat.add_lt_add_left (Nat.mod_lt i.val ha.1) _).trans_le ha.2.2))
  have earlier : b.Reads v history occ edges mid :=
    ⟨fun i hi=>(keep _ (banksLow _ (by simp)) _).trans (bankReads.oldSource i hi),
     fun i hi=>(keep _ (banksLow _ (by simp)) _).trans (bankReads.oldTarget i hi),
     fun i hi=>(keep _ (banksLow _ (by simp)) _).trans (bankReads.edge i hi),
     fun i hi=>(keep _ (banksLow _ (by simp)) _).trans (bankReads.tailSite i hi),
     fun i hi=>(keep _ (banksLow _ (by simp)) _).trans (bankReads.tailRole i hi),
     fun i hi=>(keep _ (banksLow _ (by simp)) _).trans (bankReads.headRole i hi),
     fun i hi=>(keep _ (banksLow _ (by simp)) _).trans (bankReads.starts i hi)⟩
  have mounted (f : Fin 4) (i : ℕ) (hi : i < 2^rb) :
      (ProtocolRAMTurnDirectory.bank rom rb f).read mid (i:Word W)=
        ProtocolRAMTurnDirectory.words N sites slots base f i := by
    refine Eq.trans ?_ (directory f i hi)
    apply frame
    left
    change rom+f.val*2^rb+(i:Word W).val%(2^rb) < initial
    have h := Nat.mod_lt (i:Word W).val (Nat.two_pow_pos rb)
    have l := Nat.mul_le_mul_right (2^rb) f.isLt
    rw [Nat.succ_mul] at l
    omega
  obtain ⟨out,last,read,preserve⟩ := ProtocolRAMTurnInstalled.run src sb rom rb base scratch sink (chart header bits d)
    b (record u w sitesAt) v mid coords earlier fit one fields fieldRoom put loc (romLow.trans after)
    mounted romRows romSites cap Wroom widthFit before scratchFit sinkLow af vf
  refine ⟨out,?_,read,?_⟩
  · rw [←ProtocolRAMTurnCost.full_ticks header bits initial src N sites slots d b.edge b.tailSite heads b]
    exact first.then last
  · intro a uno two three four notSink
    exact (preserve a two three (by omega) notSink).trans (frame a uno)

end Hierarchy.ProtocolRAMChronologicalShelf

end
end OAI
