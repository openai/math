import OAI.Hierarchy.ProtocolRAMChronologicalShelf
import OAI.Hierarchy.ProtocolRAMTurnCaptured
import OAI.Hierarchy.ProtocolRAMVisitLive

namespace OAI
/-! # Terminal CPU walk, gather, and five-field publication with genuinely live-only ports -/

namespace Hierarchy.ProtocolRAMChronologicalShelf
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMTurnItinerary ProtocolRAMTurnChart
open scoped Fin.CommRing
variable {W N sites slots history occ edges : ℕ}

theorem run_live (header bits initial src sb rom rb base scratch sink : ℕ)
    (d : Data) (heads : Bank) (b : Banks) (v : Values) (u : Fin N → Geometry)
    (w : Words) (sitesAt : Fin N → ℕ) (m : Memory W)
    («public» : Loaded header bits u m) (old : ∀i,0<w.width (u i).item → d.At w m (u i))
    (weights : ∀i,d.oldWidth.read m ((u i).item:Word W)=(w.width (u i).item:Word W)) (safe : ProtocolRAMTurnCursor.Safe d W initial)
    (romSafe : ∀ f,(get header bits f).Fits W initial)
    (siteBase : d.site.base=initial+1+2*N) (siteRoom : N ≤ d.site.size)
    (within : ∀i,(u i).raw ≤ (u i).length) (lenFit : ∀i,(u i).length < 2^W) (one : 1 < 2^W)
    (posPrev : ∀ i : Fin N,0<(u i).raw → 0 < i.val)
    (closed : ∀ i : Fin N,0<(u i).raw → 0<w.width (u i).item →
      0<w.width (u ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩).item)
    (endpoint : ∀i,0<w.width (u i).item →
      (ProtocolRAMVisitColumns.total (walk header bits d b.edge b.tailSite heads)).eval m (i.val:Word W)=
        (sitesAt i:Word W)+ProtocolRAMTurnWalk.carried (fun j=>(sitesAt j:Word W)) i
          (ProtocolRAMVisitColumns.previous? (fun j=>(u j).raw) posPrev i))
    (input : ∀e∈ProtocolRAMVisitColumns.terms initial (initial+1+2*N) (walk header bits d b.edge b.tailSite heads),
      e.Fits W initial) (space : initial+1+3*N < 2^W)
    (bankReads : v=ProtocolRAMTurnSnapshot.values b m)
    (banksLow : ∀ a ∈ [b.oldSource,b.oldTarget,b.edge,b.tailSite,b.tailRole,b.headRole,b.starts],a.Fits W initial)
    (siteFits : ∀i,0<w.width (u i).item → sitesAt i<2^W)
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
  obtain ⟨mid,first,visits,frame⟩ := ProtocolRAMVisitLive.run initial (walk header bits d b.edge b.tailSite heads)
    m (fun i=>(u i).raw) posPrev (fun i=>0<w.width (u i).item) sitesAt («public» 3)
    (fun i=>(within i).trans_lt (lenFit i)) closed endpoint input space
  have keep (a : Bank) (ha : a.Fits W initial) (i : Word W) : a.read mid i=a.read m i :=
    frame _ (.inl ((Nat.add_lt_add_left (Nat.mod_lt i.val ha.1) _).trans_le ha.2.2))
  have hdr : Loaded header bits u mid := fun f i=>
    (eval_below (get header bits f) (i.val:Word W) m mid (romSafe f) (fun a ha=>frame a (.inl ha))).trans («public» f i)
  have oldAt (i : Fin N) (on : 0<w.width (u i).item) : d.At w mid (u i) := by
    have src := old i on
    exact ⟨(keep _ safe.rawSource _).trans src.rawSource,(keep _ safe.rawTarget _).trans src.rawTarget,
      (keep _ safe.oldWidth _).trans src.width,(keep _ safe.sourceRole _).trans src.sourceRole,
      (keep _ safe.targetRole _).trans src.targetRole,(keep _ safe.half _).trans src.halfSource,
      (keep _ safe.half _).trans src.halfTarget,src.srcRoom,src.dstRoom⟩
  have weightAt (i : Fin N) := (keep _ safe.oldWidth _).trans (weights i)
  have siteAt (i : Fin N) (on : 0<w.width (u i).item) : d.site.read mid (i.val:Word W)=(sitesAt i:Word W) := by
    change mid (d.site.base+(i.val:Word W).val%d.site.size)=_
    rw [Fin.val_cast_of_lt (by have := i.isLt;omega),Nat.mod_eq_of_lt (i.isLt.trans_le siteRoom),siteBase]
    exact visits i on
  have saved : ProtocolRAMTurnSnapshot.values b mid=v := by
    rw [bankReads]
    unfold ProtocolRAMTurnSnapshot.values
    congr 1 <;> funext i <;> exact congrArg Fin.val (keep _ (banksLow _ (by simp)) _)
  have genuine := ProtocolRAMTurnChart.observed_live header bits src d u w sitesAt b mid hdr within lenFit
    weightAt (fun i on=>⟨oldAt i on,siteAt i on,siteFits i on⟩) one fields fieldRoom
  dsimp only at genuine
  rw [saved] at genuine
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
  have shape (i : Fin N) : (record u w sitesAt i).position≤(record u w sitesAt i).length := by
    change (if rev w (u i).item then _ else _) ≤ _
    split
    · exact Nat.sub_le ..
    · exact within i
  have capBits (i : Fin N) : (ProtocolRAMTurnInstalled.columns (record u w sitesAt) v i 4)<2^W := by
    change (if (record u w sitesAt i).length < (record u w sitesAt i).position then 0 else _) < _
    simpa only [ite_eq_right (not_lt_of_ge (shape i))] using widthFit i
  obtain ⟨out,last,read,preserve⟩ := ProtocolRAMTurnInstalled.run_from src sb rom rb base scratch sink
    (ProtocolRAMTurnItinerary.program W src N (chart header bits d) b) (ProtocolRAMTurnItinerary.ticks src N (chart header bits d) b)
    (ProtocolRAMTurnInstalled.columns (record u w sitesAt) v) mid genuine put loc (romLow.trans after)
    mounted romRows romSites cap Wroom capBits before scratchFit sinkLow af vf
  refine ⟨out,?_,read,?_⟩
  · rw [←ProtocolRAMTurnCost.full_ticks header bits initial src N sites slots d b.edge b.tailSite heads b]
    intro P R K mach pc reg pub exit installed vals cfg original entry same
    exact Procedure.Exec.then first last mach pc reg pub exit installed vals cfg original entry same
  · intro a uno two three four notSink
    exact (preserve a two three (by omega) notSink).trans (frame a uno)

end Hierarchy.ProtocolRAMChronologicalShelf

end OAI
