import OAI.Hierarchy.ProtocolRAMDateSpillTurnPrepared

namespace OAI
/-! # Native execution of a dated five-word shelf from chronological archive reads -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.DateSpill.TurnPage
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMTurnChart ProtocolRAMTurnItinerary Calendar
open scoped Classical Fin.CommRing

variable {W roles : ℕ} (P : TurnPage roles)
local notation "T" => P.terminal
local notation "L" => P.window
local notation "d" => P.data
local notation "b" => P.banks
local notation "oldBanks" => [(b).oldSource,(b).oldTarget,(b).edge,(b).tailSite,(b).tailRole,(b).headRole,(b).starts]
local notation "valueAt" m => ProtocolRAMTurnSnapshot.values P.banks m

private theorem raised {q : Bank} {a c : ℕ} (h : q.Fits W a) (u : a≤c) : q.Fits W c :=
  ⟨h.1,h.2.1,h.2.2.trans u⟩

set_option maxRecDepth 8192 in
private theorem fields_fit (room : P.stop≤2^W)
    (header : ∀f,(get (T).header (T).headerBits f).Fits W (L).zero) (safe : ProtocolRAMTurnCursor.Safe (d) W (L).zero)
    (low : ∀a∈oldBanks,a.Fits W (L).zero) (offs : P.added.old.Fits W (L).zero ∧ P.added.new.Fits W (L).zero)
    (f : Fin 7) : (Turns.fields P.chart (b) P.added f).Fits W (L).src := by
  have bounds:=(L).bounds
  have order : (L).zero≤(L).src := by omega
  have head (j : Fin 6) := ProtocolRAMGeneratedWrite.fits_mono _ order (header j)
  have s:=raised safe.rawSource order
  have t:=raised safe.rawTarget order
  have width:=raised safe.oldWidth order
  have a:=raised safe.sourceRole order
  have z:=raised safe.targetRole order
  have half:=raised safe.half order
  have si : (d).site.Fits W (L).src := (L).site_fit room
  have oldL:=raised (low (b).oldSource (by simp)) order
  have oldR:=raised (low (b).oldTarget (by simp)) order
  have edge:=raised (low (b).edge (by simp)) order
  have tail:=raised (low (b).tailSite (by simp)) order
  have left:=raised (low (b).tailRole (by simp)) order
  have right:=raised (low (b).headRole (by simp)) order
  have rank:=raised (low (b).starts (by simp)) order
  have old:=raised offs.1 order
  have new:=raised offs.2 order
  fin_cases f <;> simp [Turns.fields,Turns.absolute,Turns.extra,role,start,live,onEnd,occurrence,four,plus,minus,
    TurnPage.chart,ProtocolRAMTurnChart.chart,direction,seat,Expr.Fits,head,s,t,width,a,z,half,si,oldL,oldR,edge,tail,left,right,rank,old,new]

/-- The public boundary order, original source roles, hop IDs and both absolute offsets
are read from the incoming tape. Only positive dated rows require genuine endpoint words. -/
theorem run_from (cut : ℕ) (u : Fin (T).turns→Geometry) (w : Words) (sitesAt : Fin (T).turns→ℕ)
    (oldBase newBase : ℕ→ℕ) (m state : Memory W) (common : ∀a<cut,state a=m a) (below : cut≤P.first)
    (leftSafe : P.left.prefix.Fits W cut) (rightSafe : P.right.prefix.Fits W cut)
    (original : ∀f (i : ℕ),i<2^(T).romBits→(ProtocolRAMTurnDirectory.bank (T).rom (T).romBits f).read m (i:Word W)=
      ProtocolRAMTurnDirectory.words (T).turns (T).sites (T).seats (T).base f i)
    (romLow : (T).rom+4*2^(T).romBits≤cut) (oldBaseLow : (T).base≤P.base)
    (bits : (T).romBits=(L).romBits) (room : P.stop≤2^W)
    (headerLow : (T).header+6*2^(T).headerBits≤cut) («public» : Loaded (T).header (T).headerBits u m)
    (safe : ProtocolRAMTurnCursor.Safe (d) W cut)
    (bank : ∀a∈(T).heads::oldBanks,a.Fits W cut)
    (old : ∀i,0<w.width (u i).item→(d).At w m (u i))
    (weights : ∀i,(d).oldWidth.read m ((u i).item:Word W)=(w.width (u i).item:Word W))
    (within : ∀i,(u i).raw≤(u i).length) (lengthFit : ∀i,(u i).length<2^W)
    (posPrev : ∀i:Fin (T).turns,0<(u i).raw→0 < i.val)
    (closed : ∀i:Fin (T).turns,0<(u i).raw→0<w.width (u i).item→
      0<w.width (u ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩).item)
    (endpoint : ∀i,0<w.width (u i).item→(ProtocolRAMVisitColumns.total P.walk).eval m (i.val:Word W)=
      (sitesAt i:Word W)+ProtocolRAMTurnWalk.carried (fun j=>(sitesAt j:Word W)) i
        (ProtocolRAMVisitColumns.previous? (fun j=>(u j).raw) posPrev i))
    (siteFits : ∀i,0<w.width (u i).item→sitesAt i<2^W)
    (left : ∀i,0<w.width (u i).item→∀s,(record u w sitesAt i).boundary s→
      (u i).item<P.ranks.old ∧ P.left.prefix.eval m ((u i).item:Word W)=(oldBase (u i).item:Word W))
    (right : ∀i,0<w.width (u i).item→∀s,¬(record u w sitesAt i).boundary s→
      let eid:=(valueAt m).edge ((record u w sitesAt i).occurrence s)
      eid<P.ranks.edges ∧ P.right.prefix.eval m (eid:Word W)=(newBase eid:Word W))
    (put : ProtocolRAMTurnShelf.Live (fun i=>Turns.fieldWords (record u w sitesAt i) (valueAt m) oldBase newBase) ↪
      ProtocolRAMTurnShelf.Seats (T).sites (T).seats)
    (loc : ∀z,(put z).1.val=(record u w sitesAt z.val).site ∧ (put z).2.val=(record u w sitesAt z.val).seat)
    (widthFit : ∀i,(record u w sitesAt i).width<2^W) :
    ∃out,(P.program W).Exec state out P.ticks ∧
      (∀(f : Fin 5) (s : ProtocolRAMTurnShelf.Seats (T).sites (T).seats),
        out (P.base+f.val*((T).sites*(T).seats)+s.1.val*(T).seats+s.2.val)=
          ProtocolRAMTurnShelf.entry (fun i=>Turns.fieldWords (record u w sitesAt i) (valueAt m) oldBase newBase) put f s) ∧
      ∀a,a<P.first ∨ P.stop≤a→ out a=state a := by
  have dirState (f : Fin 4) (i : ℕ) (hi : i<2^(T).romBits) :
      (ProtocolRAMTurnDirectory.bank (T).rom (T).romBits f).read state (i:Word W)=
        ProtocolRAMTurnDirectory.words (T).turns (T).sites (T).seats (T).base f i := by
    apply Eq.trans _ (original f i hi)
    apply common
    have mul:=Nat.mul_le_mul_right (2^(T).romBits) (show f.val+1≤4 from f.isLt)
    rw [Nat.succ_mul] at mul
    change (T).rom+f.val*2^(T).romBits+(i:Word W).val%(2^(T).romBits)<cut
    omega
  obtain ⟨built,rom,ls,rs,frame⟩:=P.prepare state (ProtocolRAMGeneratedWrite.fits_mono _ below leftSafe)
    (ProtocolRAMGeneratedWrite.fits_mono _ below rightSafe) dirState (romLow.trans below) oldBaseLow bits room
  let mid:=P.prepared state
  have same (i : ℕ) (hi : i<cut) : mid i=m i := (frame i (.inl (hi.trans_le below))).trans (common i hi)
  have kept (c : Bank) (fit : c.Fits W cut) (r : Word W) : c.read mid r=c.read m r :=
    same _ ((Nat.add_lt_add_left (Nat.mod_lt r.val fit.1) _).trans_le fit.2.2)
  have earlier : P.first≤P.directory := by change P.first≤P.first+_+_;omega
  have floor : (L).floor=P.directory+4*2^(T).romBits:=rfl
  have zi : (L).zero=(L).floor+1:=rfl
  have bounds:=(L).bounds
  have cut_le_zero : cut≤(L).zero := by omega
  have rooms : (L).stop≤2^W:=room
  have wide : 1<2^W := by omega
  have headerAdm (j : Fin 6) : (get (T).header (T).headerBits j).Fits W cut := by
    have mult:=Nat.mul_le_mul_right (2^(T).headerBits) j.isLt
    rw [Nat.succ_mul] at mult
    exact ⟨⟨Nat.two_pow_pos _,by change 2^(T).headerBits<2^W;omega,
      by change (T).header+j.val*2^(T).headerBits+2^(T).headerBits≤cut;omega⟩,trivial⟩
  have headerMem : Loaded (T).header (T).headerBits u mid := fun f i=>
    (eval_below _ _ m mid (headerAdm f) same).trans («public» f i)
  have header (f : Fin 6) := ProtocolRAMGeneratedWrite.fits_mono _ cut_le_zero (headerAdm f)
  have sa : ProtocolRAMTurnCursor.Safe (d) W (L).zero := ⟨raised safe.rawSource cut_le_zero,raised safe.rawTarget cut_le_zero,
    raised safe.oldWidth cut_le_zero,raised safe.sourceRole cut_le_zero,raised safe.targetRole cut_le_zero,raised safe.half cut_le_zero⟩
  have oldMem i (hi : 0<w.width (u i).item) : (d).At w mid (u i) := by
    have o:=old i hi
    exact ⟨(kept _ safe.rawSource _).trans o.rawSource,(kept _ safe.rawTarget _).trans o.rawTarget,
      (kept _ safe.oldWidth _).trans o.width,(kept _ safe.sourceRole _).trans o.sourceRole,
      (kept _ safe.targetRole _).trans o.targetRole,(kept _ safe.half _).trans o.halfSource,
      (kept _ safe.half _).trans o.halfTarget,o.srcRoom,o.dstRoom⟩
  have mb (c : Bank) (hc : c∈oldBanks) := raised (bank c (.tail _ hc)) cut_le_zero
  have vals : (valueAt m)=(valueAt mid) := by
    have low (c : Bank) (hc : c∈oldBanks) (i : Word W) : c.read m i=c.read mid i := (kept _ (bank _ (.tail _ hc)) _).symm
    unfold ProtocolRAMTurnSnapshot.values
    congr 1 <;> funext i <;> exact congrArg Fin.val (low _ (by simp) _)
  have offMem : P.added.old.Fits W (L).zero ∧ P.added.new.Fits W (L).zero := by
    have l : P.added.old.base+P.added.old.size≤P.directory :=
      Nat.le_add_right (P.first + P.offsets.oldOffset.size) P.offsets.newOffset.size
    have r : P.added.new.base+P.added.new.size=P.directory := rfl
    exact ⟨⟨Nat.two_pow_pos _,by omega,by omega⟩,
      ⟨Nat.two_pow_pos _,by omega,by omega⟩⟩
  have fits:=(L).walk_fits (T).header (T).headerBits (d) (b).edge (b).tailSite (T).heads header sa
    (mb _ (by simp)) (mb _ (by simp)) (raised (bank _ (by simp)) cut_le_zero)
  have countLow : (ProtocolRAMVisitColumns.total P.walk).Fits W cut := by
    simp [ProtocolRAMVisitColumns.total,walk,ProtocolRAMTurnChart.walk,ProtocolRAMVisitColumns.edge,Expr.Fits,
      headerAdm,safe.rawSource,bank _ (by simp : (b).edge∈(T).heads::oldBanks),
      bank _ (by simp : (b).tailSite∈(T).heads::oldBanks),bank _ (by simp : (T).heads∈(T).heads::oldBanks)]
  -- The turn publisher uses the terminal counts; the address bounds use the window.
  have rows_eq : (T).turns = (L).rows := rfl
  have slots_eq : (T).sites * (T).seats = (L).sites * (L).seats := rfl
  have base_eq : P.base = (L).base := rfl
  have addr:=(L).scatter_fits P.directory (T).romBits floor.ge room
  obtain ⟨out,ran,stored,outside⟩:=Turns.publish (T).header (T).headerBits (L).zero (L).src (L).srcBits P.directory
    (T).romBits P.base (L).scratch (L).sink (d) (T).heads (b) (valueAt m) u P.added oldBase newBase w sitesAt mid
    headerMem oldMem (fun i=>(kept _ safe.oldWidth _).trans (weights i)) sa header rfl (L).site_room
    within lengthFit wide posPrev closed (fun i hi=>(eval_below _ _ m mid countLow same).trans (endpoint i hi))
    fits (by omega) vals mb siteFits offMem
    (fun i hi side sideH=>(ls ⟨_,(left i hi side sideH).1⟩).trans ((eval_below _ _ m state leftSafe common).trans (left i hi side sideH).2))
    (fun i hi side sideH=>(rs ⟨_,(right i hi side sideH).1⟩).trans ((eval_below _ _ m state rightSafe common).trans (right i hi side sideH).2))
    (P.fields_fit room header sa mb offMem) (by omega) put loc (by omega) (by omega) rom
    (bits ▸ (L).rom_capacity.1) (bits ▸ (L).rom_capacity.2) (L).src_room
    (by have : (L).base=(L).src+6*(L).rows+2^(L).srcBits:=rfl;omega)
    widthFit bounds.2.2.2.1 (by omega) (show (L).floor<(L).base by omega) addr.1 addr.2
  refine ⟨out,?_,stored,?_⟩
  · intro procs regs keys mach pc reg pub exit installed vals cfg raw entry entryEq
    exact Procedure.Exec.then built ran mach pc reg pub exit installed vals cfg raw entry entryEq
  · intro a ha
    have ends : (L).sink=(L).floor := rfl
    rcases ha with low|high
    · have a0 : a<(L).floor := by omega
      obtain ⟨q,r,s,t,u⟩:=(L).below a0
      exact (outside _ (.inl q) (.inl r) (.inl s) (.inl t) u).trans (frame _ (.inl low))
    · change (L).stop≤a at high
      exact (outside _ (.inr (by omega)) (.inr (by omega)) (.inr (by omega)) (.inr (by omega)) (by omega)).trans
        (frame _ (.inr (by omega)))


end Hierarchy.ProtocolRAM.DateSpill.TurnPage

end
end OAI
