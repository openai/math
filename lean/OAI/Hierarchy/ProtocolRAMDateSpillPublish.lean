import OAI.Hierarchy.ProtocolRAMDateSpillTurns
import OAI.Hierarchy.ProtocolRAMChronologicalLive

namespace OAI
/-! # Execution and five-field readback for the dated chronological publisher -/
namespace Hierarchy.ProtocolRAM.DateSpill.Turns
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMTurnItinerary ProtocolRAMTurnChart
open scoped Classical Fin.CommRing
variable {W N sites slots : ℕ}

theorem publish (header bits initial src sb rom rb base scratch sink : ℕ)
    (d : Data) (heads : Bank) (b : Banks) (v : Values) (u : Fin N → Geometry)
    (off : Offsets) (oldBase newBase : ℕ→ℕ) (w : Words) (sitesAt : Fin N → ℕ) (m : Memory W)
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
    (offLow : off.old.Fits W initial ∧ off.new.Fits W initial)
    (oldOffset : ∀i,0<w.width (u i).item→∀s,(record u w sitesAt i).boundary s→
      off.old.read m ((u i).item:Word W)=(oldBase (u i).item:Word W))
    (newOffset : ∀i,0<w.width (u i).item→∀s,¬(record u w sitesAt i).boundary s→
      off.new.read m (v.edge ((record u w sitesAt i).occurrence s):Word W)=
        (newBase (v.edge ((record u w sitesAt i).occurrence s)):Word W))
    (fieldFits : ∀ f,(fields (chart header bits d) b off f).Fits W src) (fieldRoom : src+7*N < 2^W)
    (put : ProtocolRAMTurnShelf.Live (fun i=>fieldWords (record u w sitesAt i) v oldBase newBase) ↪ ProtocolRAMTurnShelf.Seats sites slots)
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
    let ps:=Columns.passes src N (fields (chart header bits d) b off)
    ∃ out,((ProtocolRAMVisitColumns.program W N initial (walk header bits d b.edge b.tailSite heads)).seq
      ((ProtocolRAM.program W ps).seq (ProtocolRAMTurnShelf.program W N sites slots base scratch sink
        (ProtocolRAMTurnShelf.tables rom rb src sb N)))).Exec m out
        ((25+206*N)+(clock ps+(15+30*(sites*slots)+740*N))) ∧
      (∀ (f : Fin 5) (s : ProtocolRAMTurnShelf.Seats sites slots),
        out (base+f.val*(sites*slots)+s.1.val*slots+s.2.val)=
          ProtocolRAMTurnShelf.entry (fun i=>fieldWords (record u w sitesAt i) v oldBase newBase) put f s) ∧
      ∀ a,(a < initial ∨ initial+1+3*N ≤ a) → (a < src ∨ src+7*N ≤ a) →
        (a < base ∨ base+5*(sites*slots) ≤ a) → (a < scratch ∨ scratch+10*N ≤ a) →
        a ≠ sink → out a=m a := by
  intro ps
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
  have within' (i : Fin N) : (record u w sitesAt i).position≤(record u w sitesAt i).length := by
    change (if rev w (u i).item then _ else _)≤_
    split
    · exact Nat.sub_le ..
    · exact within i
  have width' (i : Fin N) : (live (chart header bits d)).eval mid (i.val:Word W)=
      ((record u w sitesAt i).width:Word W) := by
    have item : (get header bits 0).eval mid (i.val:Word W)=((u i).item:Word W) := hdr 0 i
    exact width_at _ mid _ _ ((congrArg (d.oldWidth.read mid) item).trans (weightAt i))
      (not_lt_of_ge (ProtocolRAMTurnSnapshot.position_within header bits d mid u i hdr (within i) (lenFit i)))
  have genuine := observed src (chart header bits d) b off (record u w sitesAt) v oldBase newBase mid one
    fieldFits fieldRoom within' width' (fun i on=>⟨row_at header bits d u w sitesAt mid i hdr (oldAt i on)
      (siteAt i on) (within i) (lenFit i) one, (by rw [←saved];exact ProtocolRAMTurnSnapshot.adjacent b mid _),
      lenFit i,siteFits i on⟩)
    (fun i on s endAt=>(keep _ offLow.1 _).trans (oldOffset i on s endAt))
    (fun i on s interior=>(keep _ offLow.2 _).trans (newOffset i on s interior))
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
  have capBits (i : Fin N) : (fieldWords (record u w sitesAt i) v oldBase newBase 4)<2^W := by
    change (if (record u w sitesAt i).length < (record u w sitesAt i).position then 0 else _) < _
    simpa only [ite_eq_right (not_lt_of_ge (shape i))] using widthFit i
  obtain ⟨out,last,read,preserve⟩ := ProtocolRAMTurnInstalled.run_from src sb rom rb base scratch sink
    (ProtocolRAM.program W ps) (clock ps)
    (fun i=>fieldWords (record u w sitesAt i) v oldBase newBase) mid genuine put loc (romLow.trans after)
    mounted romRows romSites cap Wroom capBits before scratchFit sinkLow af vf
  refine ⟨out,?_,read,?_⟩
  · rw [←ProtocolRAMTurnCost.site_ticks header bits initial N d b.edge b.tailSite heads]
    intro P R K mach pc reg pub exit installed vals cfg original entry same
    exact Procedure.Exec.then first last mach pc reg pub exit installed vals cfg original entry same
  · intro a uno two three four notSink
    exact (preserve a two three (by omega) notSink).trans (frame a uno)

end Hierarchy.ProtocolRAM.DateSpill.Turns

end OAI
