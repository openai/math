import OAI.Hierarchy.DescentRetainedControlRun

namespace OAI
/-! # The original low donor and its fields at the native sorted receiver slot -/
namespace Hierarchy.DescentRetainedControl.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetRetainedSetup
open DescentSixParty.Chronology DescentOrdinaryAtomFieldRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : DescentRetainedControl.Layout) {w : ℕ} (which : s.Targets) (base : ℕ)
variable (packet : Expr) (m : Memory w)
local notation "H" => s.hosts
local notation "G" => s.groups
local notation "M" => s.lanes
local notation "A" => s.oldLanes
local notation "dst" => s.image which base packet m

theorem stored_control (old : packet.Fits w base) (room : s.endAddress base<2^w) (live : 0<A)
    (X : Fin H→Fin G→Cell s.rootWidth) (seen : Source packet X A m) (t : Fin s.targets) :
    Source (.lookup (s.control base t) .row)
      (fun h g=>code (D:=s.degree) (L:=s.donors) (cap:=s.cap) (field:=s.field) (which t) (X h g)) M dst:=by
  obtain ⟨a,b,c,d⟩:=s.order base
  have r₃:=d.trans_lt room
  have r₂:=c.trans_lt r₃
  have r₁ : s.installed base<2^w:=(Nat.le_add_right ..).trans_lt (b.trans_lt r₂)
  let Y:=fun h g=>code (D:=s.degree) (L:=s.donors) (cap:=s.cap) (field:=s.field) (which t) (X h g)
  have one:=Book.mount (s.project which) s.rootWidth A base m (fun _=>by simp [project]) r₁
  have ready : Source packet X A (s.firstMem which base m):=fun j=>
    (eval_below packet _ m _ old (fun k hk=>one.2.2.1 k (.inl hk))).trans (seen j)
  have at_:Source (s.readControl which base packet t) Y A (s.firstMem which base m):=
    read_data _ _ _ _ (s.read_fits which base packet old r₁ t) _ (code_zero (D:=s.degree) (L:=s.donors) (cap:=s.cap) s.field (which t))
      _ (one.2.1 t) _ _ ready (DescentPrimitiveBirth.zero _)
  let es:=List.ofFn (s.readControl which base packet)
  have f : ∀e∈es,e.Fits w (s.installed base):=by
    intro e he
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
    obtain ⟨left,right,shiftFit,applyFit,_,_⟩:=s.read_fits which base packet old r₁ i
    exact ⟨applyFit,right,shiftFit,left⟩
  have copied : Reads (s.temp base t) Y A (s.copied which base packet m):=by
    intro j
    have len:t.val<es.length:=by simp [es]
    have got:=ProbeStage.Native.columns_read es (s.firstMem which base m) (le_refl _) f t.val len (row H G A j)
    simpa [es,scans,copied,temp,rows] using got.trans (by simpa [es] using at_ j)
  have cap:=s.temp_room base r₂ t
  have typed:=Strip.read (s.temporary base) H G A M s.selectorBits (s.temp base) (s.copied which base packet m)
    (fun j=>(s.temp_room base r₂ j).1) r₃ t Y live cap.2 copied
  have liveReg:=Strip.fits (s.temporary base) H G A M s.selectorBits t r₃
  have prior : Source (.lookup (s.control base t) .row) Y M (s.retiled which base packet m):=
    source_column _ _ liveReg.1 _ _ liveReg.2 typed
  have three:=Book.mount (s.strips which) s.aperture M (s.received base) (s.retiled which base packet m)
    (s.strip_width which) room
  exact fun j=>(eval_below (.lookup (s.control base t) .row) _ _ dst (out:=s.received base) ⟨liveReg.1,trivial⟩ (fun k hk=>three.2.2.1 k (.inl hk))).trans (prior j)

theorem paths_fit (previous sorted : Expr) (t : Fin s.targets) (prev : previous.Fits w (s.endAddress base))
    (ord : sorted.Fits w (s.endAddress base)) (space : s.endAddress base<2^w) :
    (s.targetStream which base t previous).Fits w (s.endAddress base) ∧
      (s.originalID which base t sorted).Fits w (s.endAddress base):=by
  have upper := (s.order base).2.2.2
  have tmp:=Strip.fits (s.temporary base) H G A M s.selectorBits t (upper.trans_lt space)
  have lookup : (Expr.lookup (s.control base t) .row).Fits w (s.endAddress base):=
    ProtocolRAMGeneratedWrite.fits_mono _ upper ⟨tmp.1,trivial⟩
  have geom (j : Fin 2):=Book.geometry (s.strips which) s.aperture M (s.received base) (finProdFinEquiv (j,t))
    (out:=s.endAddress base) le_rfl space (s.strip_width which _)
  exact ⟨⟨(geom 0).2,lookup,(geom 0).1,prev⟩,⟨(geom 1).2,lookup,(geom 1).1,ord⟩⟩

/-- Query an immutable gate later in the same run. The first operand may have been
produced after the controller, including the donor selected by the local decoder. -/
theorem gate_at (room : s.endAddress base<2^w) (next : Memory w)
    (keep : ∀u,u<s.endAddress base→next u=dst u) (limit : ℕ) (le : s.endAddress base≤limit)
    (i : Fin (2*s.targets)) (e k : Expr) (ef : e.Fits w limit) (kf : k.Fits w limit)
    (X : Fin H→Fin G→Cell (s.strips which i).left) (Y : Fin H→Fin G→Cell (s.strips which i).right)
    (dead : (s.strips which i).eval 0 0=0) (xs : Source e X M next) (ys : Source k Y M next) :
    let T:=Book.tables (s.strips which) s.aperture M (s.received base) i
    (T.read e k).Fits w limit ∧ Source (T.read e k) (fun h g=>(s.strips which i).eval (X h g) (Y h g)) M next:=by
  intro T
  have geom:=Book.geometry (s.strips which) s.aperture M (s.received base) i
    (out:=s.endAddress base) le_rfl room (s.strip_width which _)
  have mounted:=(Book.mount (s.strips which) s.aperture M (s.received base) (s.retiled which base packet m)
    (s.strip_width which) room).2.1 i
  have frozen : Static T (s.strips which i).eval M next:=by
    constructor
    · intro x
      exact (keep _ ((Nat.add_lt_add_left (show x.val<T.shift.size from x.isLt) _).trans_le geom.1.2.2)).trans (mounted.1 x)
    · intro x
      exact (keep _ ((Nat.add_lt_add_left (show x.val<T.apply.size from x.isLt) _).trans_le geom.2.2.2)).trans (mounted.2 x)
  have extend {B : Bank} (r : B.Fits w (s.endAddress base)) : B.Fits w limit:=⟨r.1,r.2.1,r.2.2.trans le⟩
  have fit : DescentPackedZip.Fits T e k (s.strips which i).left (s.strips which i).right M limit w:=
    ⟨ef,kf,extend geom.1,extend geom.2,rfl,rfl⟩
  exact ⟨⟨fit.apply,kf,fit.shift,ef⟩,read_data _ _ _ _ fit _ dead _ frozen X Y xs ys⟩

private theorem gate_as (room : s.endAddress base<2^w) (next : Memory w)
    (keep : ∀u,u<s.endAddress base→next u=dst u) (limit : ℕ) (le : s.endAddress base≤limit)
    (i : Fin (2*s.targets)) (g : Book.Gate) (hg : s.strips which i = g) (e k : Expr) (ef : e.Fits w limit) (kf : k.Fits w limit)
    (X : Fin H→Fin G→Cell g.left) (Y : Fin H→Fin G→Cell g.right)
    (dead : g.eval 0 0=0) (xs : Source e X M next) (ys : Source k Y M next) :
    let T:=Book.tables (s.strips which) s.aperture M (s.received base) i
    (T.read e k).Fits w limit ∧ Source (T.read e k) (fun h j=>g.eval (X h j) (Y h j)) M next:=by
  subst g
  exact s.gate_at which base packet m room next keep limit le i e k ef kf X Y dead xs ys

private theorem strips_at (j : Fin 2) (t : Fin s.targets) :
    s.strips which (finProdFinEquiv (j,t)) =
      if j=0 then
        ⟨s.stripBits,s.selectorBits,s.stripBits,fun data x =>
          take s.bits (restore (D:=s.degree) (cap:=s.cap) s.field (which t) x) data⟩
      else
        ⟨s.bits,s.selectorBits,s.bits,fun d x =>
          s.original d (restore (D:=s.degree) (cap:=s.cap) s.field (which t) x)⟩ := by
  unfold strips
  exact congrArg (fun p : Fin 2 × Fin s.targets =>
    if p.1=0 then
      (⟨s.stripBits,s.selectorBits,s.stripBits,fun data x =>
        take s.bits (restore (D:=s.degree) (cap:=s.cap) s.field (which p.2) x) data⟩ : Book.Gate)
    else
      ⟨s.bits,s.selectorBits,s.bits,fun d x =>
        s.original d (restore (D:=s.degree) (cap:=s.cap) s.field (which p.2) x)⟩)
    (finProdFinEquiv.symm_apply_apply (j,t))

theorem original_at (old : packet.Fits w base) (space : s.endAddress base<2^w) (live : 0<A)
    (X : Fin H→Fin G→Cell s.rootWidth) (seen : Source packet X A m) (t : Fin s.targets)
    (next : Memory w) (keep : ∀u,u<s.endAddress base→next u=dst u)
    (limit : ℕ) (le : s.endAddress base≤limit) (sorted : Expr) (fit : sorted.Fits w limit)
    (J : Fin H→Fin G→Cell s.bits) (numbers : Source sorted J M next) :
    (s.originalID which base t sorted).Fits w limit ∧ Source (s.originalID which base t sorted)
      (fun h g=>s.original (J h g) (filter (D:=s.degree) (L:=s.donors) (cap:=s.cap) (field:=s.field) (which t) (X h g))) M next:=by
  let q:=fun h g=>code (D:=s.degree) (L:=s.donors) (cap:=s.cap) (field:=s.field) (which t) (X h g)
  let k:=Expr.lookup (s.control base t) .row
  have upper := (s.order base).2.2.2
  have ok : k.Fits w (s.endAddress base):=ProtocolRAMGeneratedWrite.fits_mono _ upper
    ⟨(Strip.fits (s.temporary base) H G A M s.selectorBits t (upper.trans_lt space)).1,trivial⟩
  have ctl : Source k q M next:=fun j=>(eval_below k _ dst next ok keep).trans
    (s.stored_control which base packet m old space live X seen t j)
  let i:=finProdFinEquiv ((1:Fin 2),t)
  let g : Book.Gate := ⟨s.bits,s.selectorBits,s.bits,fun d x =>
    s.original d (restore (D:=s.degree) (cap:=s.cap) s.field (which t) x)⟩
  have hg : s.strips which i = g := (s.strips_at which 1 t).trans (ite_eq_right one_ne_zero)
  have go:=s.gate_as which base packet m space next keep limit le i g hg sorted k fit
    (ProtocolRAMGeneratedWrite.fits_mono _ le ok)
  have actual := go J q (by simp [g,original]) numbers ctl
  refine ⟨actual.1,?_⟩
  have eqValues : (fun h j => g.eval (J h j) (q h j)) =
      (fun h j => s.original (J h j) (filter (D:=s.degree) (L:=s.donors) (cap:=s.cap)
        (field:=s.field) (which t) (X h j))) := by
    funext h j
    exact congrArg (s.original (J h j)) (restore_code (D:=s.degree) (L:=s.donors)
      (cap:=s.cap) s.field (which t) (X h j))
  exact eqValues ▸ actual.2

theorem issued (old : packet.Fits w base) (room : s.endAddress base<2^w) (live : 0<A)
    (X : Fin H→Fin G→Cell s.rootWidth) (seen : Source packet X A m) (t : Fin s.targets)
    (previous sorted : Expr) (prev : previous.Fits w base) (ordinal : sorted.Fits w base)
    (Y : Fin H→Fin G→Cell s.stripBits) (J : Fin H→Fin G→Cell s.bits)
    (payload : Source previous Y M m) (numbers : Source sorted J M m) :
    Source (s.targetStream which base t previous)
      (fun h g=>take s.bits (filter (D:=s.degree) (L:=s.donors) (cap:=s.cap) (field:=s.field) (which t) (X h g)) (Y h g)) M dst ∧
    Source (s.originalID which base t sorted)
      (fun h g=>s.original (J h g) (filter (D:=s.degree) (L:=s.donors) (cap:=s.cap) (field:=s.field) (which t) (X h g))) M dst:=by
  let q:=fun h g=>code (D:=s.degree) (L:=s.donors) (cap:=s.cap) (field:=s.field) (which t) (X h g)
  have ctl:=s.stored_control which base packet m old room live X seen t
  obtain ⟨a,b,c,d⟩:=s.order base
  have baseLe : base≤ s.endAddress base:=a.trans ((Nat.le_add_right ..).trans (b.trans (c.trans d)))
  have frame:=(s.any which base packet m old room).2.2
  have stay {a : ℕ} (e : Expr) (V : Fin H→Fin G→Cell a) (fits : e.Fits w base) (v : Source e V M m) :
      Source e V M dst:=fun j=>(eval_below _ _ _ _ fits (fun i hi=>frame i (.inl hi))).trans (v j)
  have tmp:=Strip.fits (s.temporary base) H G A M s.selectorBits t (d.trans_lt room)
  have lookup : (Expr.lookup (s.control base t) .row).Fits w (s.endAddress base):=ProtocolRAMGeneratedWrite.fits_mono _ d ⟨tmp.1,trivial⟩
  constructor
  · let gate:=finProdFinEquiv ((0:Fin 2),t)
    let k:=Expr.lookup (s.control base t) .row
    let g : Book.Gate := ⟨s.stripBits,s.selectorBits,s.stripBits,fun data x =>
      take s.bits (restore (D:=s.degree) (cap:=s.cap) s.field (which t) x) data⟩
    have hg : s.strips which gate = g := (s.strips_at which 0 t).trans (ite_eq_left rfl)
    have go:=s.gate_as which base packet m room dst (fun _ _=>rfl) (s.endAddress base) le_rfl gate g hg
      previous k (ProtocolRAMGeneratedWrite.fits_mono _ baseLe prev) lookup
    have actual:=go Y q (take_zero s.bits _) (stay _ _ prev payload) ctl
    have eqValues : (fun h j => g.eval (Y h j) (q h j)) =
        (fun h j => take s.bits (filter (D:=s.degree) (L:=s.donors) (cap:=s.cap)
          (field:=s.field) (which t) (X h j)) (Y h j)) := by
      funext h j
      exact congrArg (fun ctrl => take s.bits ctrl (Y h j)) (restore_code (D:=s.degree)
        (L:=s.donors) (cap:=s.cap) s.field (which t) (X h j))
    exact eqValues ▸ actual.2
  · exact (s.original_at which base packet m old room live X seen t dst (fun _ _=>rfl)
      (s.endAddress base) le_rfl sorted (ProtocolRAMGeneratedWrite.fits_mono _ baseLe ordinal) J
      (stay _ _ ordinal numbers)).2

end
end Hierarchy.DescentRetainedControl.Layout

end OAI
