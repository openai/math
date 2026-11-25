import OAI.Hierarchy.TaggedWideDatedEmitters
import OAI.Hierarchy.TaggedWideDatedAddresses
import OAI.Hierarchy.TaggedWideRoleScans
import OAI.Hierarchy.TaggedWideSideScan
import OAI.ThreeFlat.RAM.ProcedureBank
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # The three successive physical role pages of an authentic dated frame -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets
open AdaptiveProbe ProtocolRAM RoleProgram ReportSockets
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing

variable (n : ℕ) (chart : Chart) (sock : Bool→Socket) (siteTable : Bank) (size number : Expr)
local notation "self" => DatedRows.split n sock false
local notation "peer" => DatedRows.split n sock true
local notation "sz" => DatedRows.each n size size
local notation "idWord" => DatedRows.each n number number

variable {h W k attempts N native : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : Marks h W k attempts) (unique : Exclusive mark) (rows : Fin N≃Source S π depth mark)
local notation "port" => named S π depth mark unique rows
local notation "L" => (siteLast h (2^W) k+1)*stride k S.degree attempts

def roleFact (start : ℕ) (qty id : Fin N→ℕ) (m : Memory native) (f : Fin 3) : Prop :=
  let data:=(role f).data (fun a : Fin N×Bool=>qty a.1) (fun a=>id a.1)
    (fun a=>(name (site S (port (a.1,!a.2)))).val)
  ∀q : Fin L,m (sheet start L n f+q.val)=(RoleWidths.shelf port (shelfSlot S) data q:Word native)

variable (start : ℕ) (m : Memory native) (qty id : Fin N→ℕ)
    (source : Fin n→Option (Fin N)) (side : Fin N→Bool→Bool)
local notation "dated" => DatedRows.stream source side
local notation "fact" => roleFact n S π depth mark unique rows start qty id
local notation "fit" => Fits n chart sock siteTable size number native start
local notation "page" => sheet start L n
local notation "sinkAt" => sink start L n

/-- Initial state reads for the actual two-sided source stream. The second
half enumerates opposite raw ends, including edges whose sorted orientation is reversed. -/
structure Reads : Prop where
  cover : ∀i,0<qty i→∃q,source q=some i
  onto : ∀i,Function.Surjective (side i)
  flip : ∀i b,side i (!b)=!(side i b)
  widthFit : ∀i,qty i<2^native
  idFit : ∀i,id i<2^native
  siteFit : siteLast h (2^W) k<2^native
  widthAt : ∀q,size.eval m (q.val:Word native)=((source q).elim 0 qty:ℕ)
  idAt : ∀q i,source q=some i→0<qty i→number.eval m (q.val:Word native)=(id i:Word native)
  socket : ∀q i,source q=some i→0<qty i→∀b,Resolved S chart (sock b) m (q.val:Word native) (port (i,side i b))
  strideAt : ∀p : Public S h W k attempts,siteTable.read m ((name (site S p)).val:Word native)=
    (((name (site S p)).val*stride k S.degree attempts:ℕ):Word native)

private theorem field_fits {n W cut : ℕ} {chart : Chart} {sock : Bool→Socket} {table : Bank}
    {size number : Expr} (ok : Fits n chart sock table size number W cut) (f : Fin 3) :
    (word n chart sock size number f).Fits W cut := by
  unfold word
  cases role f
  · exact ok.size
  · exact ⟨ok.size,trivial,trivial,ok.number⟩
  · exact ⟨ok.size,trivial,trivial,ok.peerSite⟩

theorem step_from (scope : ℕ) («scoped» : scope ≤ start)
    (ok : Fits n chart sock siteTable size number native scope) (ready : Reads n chart sock siteTable size number S π depth mark unique rows m qty id source side)
    (wordRoom : start+3*span L n<2^native) (f : Fin 3) (now : Memory native) (low : ∀a<scope,now a=m a) :
    ∃ after,(leaf n chart sock siteTable size number native start L f).Exec now after
        (leafWork n chart sock siteTable size number start L f) ∧ fact after f ∧
      ∀a,a<sinkAt f ∨ sinkAt f+span L n≤a→after a=now a := by
  have rowRoom : n+n≤2^native := by dsimp [span] at wordRoom;omega
  have interval : page f+L+(n+n)+(n+n)=sinkAt f+span L n := by simp only [sheet,span];omega
  have before : start≤page f := by dsimp [sheet,sink];omega
  have last : sinkAt f+span L n ≤ start+3*span L n := by
    have h:=Nat.mul_le_mul_right (span L n) f.isLt
    rw [Nat.succ_mul] at h
    dsimp [sink];omega
  have values : (word n chart sock size number f).Fits native scope:=field_fits ok f
  have destFit : (dest n chart sock siteTable size number start L f).Fits native scope :=
    ⟨values,trivial,trivial,trivial,⟨ok.table,ok.selfSite⟩,ok.selfCode⟩
  have activeIndex (q : Fin (n+n)) (b : Bool) (i : Fin N) (found : dated q=some (i,b)) :
      ∃p : Fin n,∃raw : Bool,DatedRows.visit n raw p=q ∧ source p=some i ∧ side i raw=b := by
    obtain ⟨raw,p,rfl⟩:=DatedRows.visit_at q
    rw [DatedRows.stream_at] at found
    cases src:source p with
    | none=>simp [src] at found
    | some j=>
      simp only [src,Option.map_some,Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨rfl,rfl⟩:=found
      exact ⟨p,raw,rfl,src,rfl⟩
  have liveRead (q : Fin (n+n)) (i : Fin N) (b : Bool) (found : dated q=some (i,b))
      (used : 0<qty i) (peerFlag : Bool) :
      Resolved S chart (DatedRows.split n sock peerFlag) now (q.val:Word native)
        (port (i,if peerFlag then !b else b)) := by
    obtain ⟨p,raw,rfl,located,rfl⟩:=activeIndex q b i found
    have original := ready.socket p i located used (if raw then !peerFlag else peerFlag)
    have real := DatedRows.split_resolved chart sock rowRoom m p peerFlag raw _ original
    have ss : (socketSite chart (DatedRows.split n sock peerFlag)).Fits native scope :=
      by cases peerFlag <;> first | exact ok.selfSite | exact ok.peerSite
    have sc : (socketCode chart (DatedRows.split n sock peerFlag)).Fits native scope :=
      by cases peerFlag <;> first | exact ok.selfCode | exact ok.peerCode
    have sign : side i (if raw then !peerFlag else peerFlag)=(if peerFlag then !(side i raw) else side i raw) := by
      cases raw <;> cases peerFlag <;> first | rfl | exact ready.flip i false | exact ready.flip i true
    rw [sign] at real
    exact ⟨(eval_below _ _ m now ss low).trans real.1,(eval_below _ _ m now sc low).trans real.2⟩
  have freeze (a : Word native) : siteTable.read now a=siteTable.read m a := by
    apply low
    have h:=Nat.mod_lt a.val ok.table.1
    have endAt:=ok.table.2.2
    change siteTable.base+a.val%siteTable.size<scope
    omega
  obtain ⟨after,exec,published,frame⟩:=scatter_field_all S π depth mark unique rows (role f) (page f) (page f+L)
    (sinkAt f) sz idWord chart self peer siteTable now qty id dated
    (fun i b hi=>by
      obtain ⟨q,hq⟩:=ready.cover i hi
      obtain ⟨raw,actual⟩:=ready.onto i b
      exact ⟨DatedRows.visit n raw q,by simp [DatedRows.stream_at,hq,actual]⟩)
    ready.widthFit ready.idFit ready.siteFit
    (fun q=>by
      rw [eval_below _ _ m now ok.size low]
      obtain ⟨b,i,rfl⟩:=DatedRows.visit_at q
      rw [DatedRows.each_read _ _ _ rowRoom,DatedRows.stream_at]
      cases found:source i <;> simp [found,ready.widthAt,ite_self])
    (fun q i b src hi=>by
      obtain ⟨p,raw,rfl,seen,_⟩:=activeIndex q b i src
      rw [eval_below _ _ m now ok.number low,DatedRows.each_read _ _ _ rowRoom,ite_self]
      exact ready.idAt p i seen hi)
    (fun q i b src hi=>liveRead q i b src hi false) (fun q i b src hi=>liveRead q i b src hi true)
    (fun p=>(freeze _).trans (ready.strideAt p)) (ProtocolRAMGeneratedWrite.fits_mono _ («scoped».trans before) values)
    (ProtocolRAMGeneratedWrite.fits_mono _ («scoped».trans before) destFit) le_rfl (by omega) (by dsimp [sheet];omega)
  refine ⟨after,exec,published,?_⟩
  intro a away
  apply frame
  · rcases away with l|r
    · exact Or.inl (by dsimp [sheet];omega)
    · exact Or.inr (by omega)
  · rcases away with l|r
    · exact Or.inl (by dsimp [sheet];omega)
    · exact Or.inr (by omega)
  · have positive : 0<span L n:=by dsimp [span];omega
    rcases away with l|r <;> omega

theorem step (ok : fit) (ready : Reads n chart sock siteTable size number S π depth mark unique rows m qty id source side)
    (wordRoom : start+3*span L n<2^native) (f : Fin 3) (now : Memory native) (low : ∀a<start,now a=m a) :
    ∃ after,(leaf n chart sock siteTable size number native start L f).Exec now after
        (leafWork n chart sock siteTable size number start L f) ∧ fact after f ∧
      ∀a,a<sinkAt f ∨ sinkAt f+span L n≤a→after a=now a :=
  step_from n chart sock siteTable size number S π depth mark unique rows start m qty id source side start le_rfl
    ok ready wordRoom f now low

/-- Each of the three scans preserves the other fields and all original
packet rows. The allocated span includes the literal sink and both scratch arrays. -/
theorem run (ok : fit) (ready : Reads n chart sock siteTable size number S π depth mark unique rows m qty id source side)
    (room : start+3*span L n<2^native) :
    ∃ after,(program n chart sock siteTable size number native start L).Exec m after
        (work n chart sock siteTable size number start L) ∧ (∀f,fact after f) ∧
      ∀a,a<start ∨ start+3*span L n≤a→after a=m a := by
  let B:=span L n
  have pos : 0<B:=by dsimp [B,span];omega
  have sel (f : Fin 3) : sinkAt f=start+f.val*B:=rfl
  have ptr (f : Fin 3) (q : Fin L) : sinkAt f≤page f+q.val ∧ page f+q.val<sinkAt f+B := by
    dsimp [sheet,B,span];have h:=q.isLt;omega
  have law:=step n chart sock siteTable size number S π depth mark unique rows start m qty id source side ok ready room
  obtain ⟨a,ha,pa,fa⟩:=law 0 m (fun _ _=>rfl)
  obtain ⟨b,hb,pb,fb⟩:=law 1 a (fun i hi=>fa i (.inl (by simp [sink];omega)))
  obtain ⟨c,hc,pc,fc⟩:=law 2 b (fun i hi=>(fb i (.inl (by simp [sink];omega))).trans (fa i (.inl (by simp [sink];omega))))
  have ss0 : sinkAt 0=start:=by simp [sink]
  have ss1 : sinkAt 1=start+B:=by simp [sink,B]
  have ss2 : sinkAt 2=start+2*B:=by simp [sink,B]
  refine ⟨c,Procedure.Exec.then ha (Procedure.Exec.then hb hc),?_,?_⟩
  · intro f q
    fin_cases f
    · have bound := (ptr 0 q).2
      have beforeOne : page 0 + q.val < sinkAt 1 := by omega
      have beforeTwo : page 0 + q.val < sinkAt 2 := by omega
      exact (fc (page 0 + q.val) (.inl beforeTwo)).trans
        ((fb (page 0 + q.val) (.inl beforeOne)).trans (pa q))
    · have bound := (ptr 1 q).2
      have beforeTwo : page 1 + q.val < sinkAt 2 := by omega
      exact (fc (page 1 + q.val) (.inl beforeTwo)).trans (pb q)
    · exact pc q
  · intro i hi
    have a0 : i<sinkAt 0 ∨ sinkAt 0+B ≤ i:=by omega
    have a1 : i<sinkAt 1 ∨ sinkAt 1+B ≤ i:=by omega
    have a2 : i<sinkAt 2 ∨ sinkAt 2+B ≤ i:=by omega
    exact (fc _ a2).trans ((fb _ a1).trans (fa _ a0))

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets

end
end OAI
