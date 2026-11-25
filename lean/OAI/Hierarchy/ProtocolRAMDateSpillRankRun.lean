import OAI.Hierarchy.ProtocolRAMDateSpillRankTape

namespace OAI
/-! # The actual ordered execution of all dated spill ranks -/
noncomputable section
namespace Hierarchy.ProtocolRAM.DateSpill.RankTape
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open ThreeFlat.RAM PhysicalProcedure
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAMTurnReplayed ProtocolRAMPackedRanked ProtocolRAMDateSpillRank RouteSettlement Calendar
open scoped Classical Fin.CommRing

variable {h d k K W : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
variable (A : RankTape) (B : Mount (S:=S) π place A.edges) (o : CoreRoute.Orders h d k)
local notation "P" j => A.page j

structure Conditions (m : Memory W) (dates : ℕ) : Prop where
  core : A.core=coreCount o
  directory : ∃cj : CoreBoard.Columns h d×Fin k→ℕ,Directory A.accounts m (CoreRoute.enum B o) PurchaseInventory.slot cj
  index : A.accounts.index.Fits W A.first
  kind : A.accounts.kind.Fits W A.first
  oldKind : A.kind.Fits W A.first
  oldIndex : A.index.Fits W A.first
  current : ∀j<dates,(A.overflow j).Fits W A.first
  room : A.stop dates<2^W
  wide : 2<2^W

/-- The rank computation writes a whole immutable per-date extent. This receipt
retains the genuine per-word outputs even after subsequent dates execute. -/
structure Observation (j : ℕ) (archive final : Memory W) : Prop where
  stored : ∃mid printed : Memory W,
    RankRead B o (P j).rankStart (A.overflow j) mid printed ∧
    (∀a<A.first,mid a=archive a) ∧
    (∀i : Fin A.old, mid ((P j).amount.base+i.val)=((P j).term A.kind A.index).eval archive (i.val:Word W)) ∧
    ∀a<(P j).offsetsStart, final a=printed a

/-- Re-reading the rank words after subsequent dates gives the very same
per-occurrence and per-edge certificate, with the actual archived input. -/
theorem Observation.read {j : ℕ} {archive final : Memory W} (obs : Observation A B o j archive final)
    (core : A.core=coreCount o) :
    ∃mid, RankRead B o (P j).rankStart (A.overflow j) mid final ∧
      (∀a<A.first,mid a=archive a) ∧
      ∀i : Fin A.old,mid ((P j).amount.base+i.val)=((P j).term A.kind A.index).eval archive (i.val:Word W) := by
  obtain ⟨mid,printed,got,low,amount,keep⟩:=obs.stored
  refine ⟨mid,?_,low,amount⟩
  let lo:=(P j).rankStart
  let n:=A.edges+coreCount o
  have room:=rank_room lo n A.edges
  have prefixRoom:=group_capacity n
  have endEq : (P j).offsetsStart=endAt lo n A.edges+(P j).load.size := by
    change endAt lo (A.edges+A.core) A.edges+_=_
    rw [core]
  have block : (ranks lo n A.edges)+4*n≤(P j).offsetsStart := by
    rw [endEq]
    exact room.trans (Nat.le_add_right ..)
  have order : lo+n≤(ProtocolRAMTurnReplayed.weight lo n).base ∧
      (ProtocolRAMTurnReplayed.weight lo n).base+n≤counters lo n ∧
      counters lo n+A.edges=ranks lo n A.edges := by
    dsimp [ProtocolRAMTurnReplayed.weight,key,scratch,rows,groups,counters,ranks,Bank.size]
    omega
  refine ⟨fun i=>(keep _ ?_).trans (got.key i),fun i=>(keep _ ?_).trans (got.width i),
    fun i=>(keep _ ?_).trans (got.rank i),fun a ha=>(keep _ ?_).trans (got.frame a ha),
    fun e=>(keep _ ?_).trans (got.total e)⟩
  all_goals dsimp only [lo,n] at *; omega

private theorem read_low (b : Bank) (base : ℕ) (m u : Memory W) (low : b.Fits W base)
    (same : ∀a<base,u a=m a) (r : Word W) : b.read u r=b.read m r :=
  same _ ((Nat.add_lt_add_left (Nat.mod_lt r.val low.1) _).trans_le low.2.2)

private theorem monoFit (b : Bank) {x y : ℕ} (h : b.Fits W x) (xy : x≤y) : b.Fits W y :=
  ⟨h.1,h.2.1,h.2.2.trans xy⟩

private theorem rank_time (lo edges core : ℕ) (accounts : RouteSettlement.Banks) (paid : Bank) :
    ProtocolRAMTurnReplayed.time lo edges core accounts paid=66+539*(edges+core)+6*edges := by
  simp only [ProtocolRAMTurnReplayed.time,ProtocolRAMTurnPrefix.clock,
    (ProtocolRAMTurnPrefix.term_work (original accounts paid) edges).1,
    (ProtocolRAMTurnPrefix.term_work (original accounts paid) edges).2,
    ProtocolRAMPackedCommon.clock,ProtocolRAMRankCost.gather,ProtocolRAMPackedCommon.inputBanks,Expr.work]
  ring

theorem execute (inj : Function.Injective place) (pad : Chord K) (dates : ℕ) (archive : Memory W)
    (ok : Conditions A B o archive dates) :
    ∃out,(A.program W dates).Exec archive out (A.ticks dates) ∧
      (∀a<A.first,out a=archive a) ∧ (∀e : Fin A.edges,out (A.zero.base+e.val)=0) ∧
      ∀j<dates,Observation A B o j archive out := by
  obtain ⟨cj,rooted⟩:=ok.directory
  have mono : Monotone A.stop := by
    intro i j ij
    exact Nat.add_le_add_left (Nat.mul_le_mul_right A.stride ij) _
  have first (j : ℕ) : A.first+A.zero.size≤A.stop j := by dsimp [stop];omega
  have zeroRoom : A.edges≤A.zero.size := group_capacity A.edges
  have small : A.first+A.edges<2^W := by have:=first dates;have:=ok.room;omega
  have recur (j : ℕ) (hj : j≤dates) :
      ∃out,(A.program W j).Exec archive out (A.ticks j) ∧
        (∀a<A.first,out a=archive a) ∧ (∀e : Fin A.edges,out (A.zero.base+e.val)=0) ∧
        ∀t<j,Observation A B o t archive out := by
    induction j with
    | zero =>
      refine ⟨cleared A.zero A.edges archive,clear_exec _ _ _ small,
        fun a ha=>cleared_frame _ _ _ a (.inl ha),fun e=>Fin.ext (cleared_at _ _ _ e),by omega⟩
    | succ j ih =>
      obtain ⟨u,prev,low,zeros,obs⟩:=ih (Nat.le_of_lt hj)
      have after:=first j
      have finish:=(mono hj).trans_lt ok.room
      have bound:=A.page_end j
      have floor : A.first≤(P j).floor := by change A.first≤A.stop j;omega
      have amountRoom : (P j).floor+A.old≤(P j).rankStart :=
        Nat.add_le_add_left ((P j).amount_room) _
      have afterRank : (P j).rankStart+(A.edges+A.core)≤endAt (P j).rankStart (A.edges+A.core) A.edges := by
        have h:=rank_room (P j).rankStart (A.edges+A.core) A.edges
        have k:=group_capacity (A.edges+A.core)
        dsimp [ranks,counters,groups,rows,scratch,ProtocolRAMTurnReplayed.weight,key,Bank.size] at h
        omega
      have endRank : endAt (P j).rankStart (A.edges+A.core) A.edges≤(P j).offsetsStart :=
        Nat.le_add_right ..
      have scanRoom : (P j).floor+A.old<2^W := by omega
      have baseFit : ((P j).term A.kind A.index).Fits W A.first :=
        ⟨ok.oldKind,trivial,⟨ok.current j hj,ok.oldIndex⟩,trivial⟩
      let mid:=image (P j).floor A.old ((P j).term A.kind A.index) u
      have boot : ((P j).amounts W A.kind A.index).Exec u mid ((P j).amountTime A.kind A.index) :=
        scan_exec _ _ _ _ (ProtocolRAMGeneratedWrite.fits_mono _ floor baseFit) scanRoom
      have frozen (x : ℕ) (hx : x<(P j).floor) : mid x=u x :=
        ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl hx)
      have keep (x : ℕ) (hx : x<A.first) : mid x=archive x := (frozen x (hx.trans_le floor)).trans (low x hx)
      have dir : Directory A.accounts mid (CoreRoute.enum B o) PurchaseInventory.slot cj :=
        ⟨fun i=>(read_low _ _ _ _ ok.kind keep _).trans (rooted.headKind i),
         fun i=>(read_low _ _ _ _ ok.index keep _).trans (rooted.headIndex i),
         fun i=>(read_low _ _ _ _ ok.kind keep _).trans (rooted.tailKind i),
         fun i=>(read_low _ _ _ _ ok.index keep _).trans (rooted.tailIndex i)⟩
      have zeroFit : A.zero.Fits W (P j).rankStart :=
        ⟨Nat.two_pow_pos _,by have:=first dates;have:=ok.room;omega,
          after.trans (show (P j).floor≤(P j).rankStart from (Nat.le_add_right _ _).trans amountRoom)⟩
      have input : ∀b∈[A.zero,A.accounts.index,A.accounts.kind,A.overflow j],b.Fits W (P j).rankStart := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl|remain
        · exact zeroFit
        rcases List.mem_cons.mp remain with rfl|remain
        · exact monoFit _ ok.index (by omega)
        rcases List.mem_cons.mp remain with rfl|remain
        · exact monoFit _ ok.kind (by omega)
        obtain rfl:=List.mem_singleton.mp remain
        exact monoFit _ (ok.current j hj) (by omega)
      have sameZero (e : Fin A.edges) : mid (A.zero.base+e.val)=0 := by
        exact (frozen _ (show A.first+e.val<A.stop j from
          (Nat.add_lt_add_left (e.isLt.trans_le zeroRoom) _).trans_le after)).trans (zeros e)
      obtain ⟨out,step,printed⟩:=ProtocolRAMDateSpillRank.run B inj pad o (P j).rankStart A.accounts
        (A.overflow j) A.zero mid cj dir zeroRoom (by omega) sameZero input (by rw [←ok.core];omega) ok.wide
      rw [←ok.core] at step
      have time : ProtocolRAMTurnReplayed.time (P j).rankStart A.edges A.core
        (dateBanks A.accounts (A.overflow j) A.zero) A.zero=66+539*(A.edges+A.core)+6*A.edges :=
        rank_time _ _ _ _ _
      rw [time] at step
      have pageFrame (x : ℕ) (hx : x<A.stop j) : out x=u x :=
        (printed.frame x (by change x<(P j).floor at hx;omega)).trans (frozen x hx)
      refine ⟨out,prev.then (boot.then step),fun x hx=>(pageFrame x (hx.trans_le floor)).trans (low x hx),
        fun e=>(pageFrame _ ((Nat.add_lt_add_left (e.isLt.trans_le zeroRoom) _).trans_le after)).trans (zeros e),?_⟩
      intro t ht
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with earlier|equal
      · obtain ⟨v,p,rank,frame,amount,oldMem⟩:=(obs t earlier).stored
        exact ⟨v,p,rank,frame,amount,fun x hx=>(pageFrame _ ((hx.trans_le (A.page_end t)).trans_le
          (mono earlier))).trans (oldMem x hx)⟩
      · subst t
        refine ⟨mid,out,printed,keep,?_,fun _ _=>rfl⟩
        intro i
        exact (ProtocolRAMGeneratedWrite.read_image (P j).floor A.old ((P j).term A.kind A.index) u i).trans
          (eval_below _ _ archive u baseFit low)
  exact recur dates le_rfl

end Hierarchy.ProtocolRAM.DateSpill.RankTape
end

end OAI
