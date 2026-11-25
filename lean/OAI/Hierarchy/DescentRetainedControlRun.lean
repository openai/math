import OAI.Hierarchy.DescentRetainedControlLayout
import OAI.Hierarchy.DescentRetainedControlWord
import OAI.Hierarchy.DescentDatedNodeMetadata
import OAI.Hierarchy.DescentPrimitiveBirthDigits

namespace OAI
/-! # One printed home-selector per target and one pitch change per short register -/
namespace Hierarchy.DescentRetainedControl.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetRetainedSetup
open DescentSixParty.Chronology DescentOrdinaryAtomFieldRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : DescentRetainedControl.Layout) {w : ℕ}
abbrev Targets:=Fin s.targets→Option ℕ
variable (which : s.Targets)
def project (t : Fin s.targets) : Book.Gate :=
  ⟨s.rootWidth,0,s.selectorBits,fun x _=>code (D:=s.degree) (L:=s.donors) (cap:=s.cap) (field:=s.field) (which t) x⟩
def original (selected : Cell s.bits) (ctrl : Cell s.selectorBits) : Cell s.bits :=
  if h:0<selected.val ∧ selected.val≤ s.donors then
    ((source ctrl ⟨selected.val-1,by omega⟩).elim 0 fun d=>d.val+1:ℕ)
  else 0
def strips (i : Fin (2*s.targets)) : Book.Gate :=
  let p : Fin 2×Fin s.targets:=finProdFinEquiv.symm i
  if p.1=0 then ⟨s.stripBits,s.selectorBits,s.stripBits,fun data x=>take s.bits (restore (D:=s.degree) (cap:=s.cap) s.field (which p.2) x) data⟩
  else ⟨s.bits,s.selectorBits,s.bits,fun d x=>s.original d (restore (D:=s.degree) (cap:=s.cap) s.field (which p.2) x)⟩

variable (base : ℕ)
def readControl (packet : Expr) (t : Fin s.targets) :=
  (Book.tables (s.project which) s.rootWidth s.oldLanes base t).read packet (.lit 0)
def scans (packet : Expr) :=ProbeStage.Native.columns s.rows (s.installed base) (List.ofFn (s.readControl which base packet))
def retile (w : ℕ):=Strip.code (s.temporary base) s.hosts s.groups s.oldLanes s.lanes s.selectorBits w (s.temp base)
def stage₁ (w : ℕ) :=Book.install (s.project which) s.rootWidth s.oldLanes w base
def stage₂ (w : ℕ) :=Book.install (s.strips which) s.aperture s.lanes w (s.received base)
def program (w : ℕ) (packet : Expr) :=
  (((s.stage₁ which base w).seq (ProtocolRAM.program w (s.scans which base packet))).seq (s.retile base w).program).seq (s.stage₂ which base w)
def ticks (w : ℕ) (packet : Expr) :=
  ((4+10*(s.targets*(2*2^(s.rootWidth*s.oldLanes)))+clock (s.scans which base packet))+
    (s.retile base w).ticks)+(4+10*((2*s.targets)*(2*2^(s.aperture*s.lanes))))
def firstMem (m : Memory w) :=Book.image (s.project which) s.rootWidth s.oldLanes base m
def copied (packet : Expr) (m : Memory w):=result (s.scans which base packet) (s.firstMem which base m)
def retiled (packet : Expr) (m : Memory w):=(s.retile base w).image (s.copied which base packet m)
def image (packet : Expr) (m : Memory w):=Book.image (s.strips which) s.aperture s.lanes (s.received base) (s.retiled which base packet m)
def targetStream (t : Fin s.targets) (previous : Expr) :=
  (Book.tables (s.strips which) s.aperture s.lanes (s.received base) (finProdFinEquiv ((0:Fin 2),t))).read
    previous (.lookup (s.control base t) .row)
def originalID (t : Fin s.targets) (sorted : Expr) :=
  (Book.tables (s.strips which) s.aperture s.lanes (s.received base) (finProdFinEquiv ((1:Fin 2),t))).read
    sorted (.lookup (s.control base t) .row)

theorem order : base≤ s.installed base ∧ s.installed base+s.targets*s.rows≤ s.temporary base ∧
    s.temporary base≤ s.received base ∧ s.received base≤ s.endAddress base:=
  ⟨Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩

theorem temp_room (room : s.temporary base<2^w) (t : Fin s.targets) :
    (s.temp base t).Fits w (s.temporary base) ∧ s.rows≤(s.temp base t).size:=by
  have lim:=Nat.mul_le_mul_right s.rows t.isLt.le
  have cap : s.rows≤2^Nat.clog 2 s.rows:=Nat.le_pow_clog (by decide) _
  change (0<2^Nat.clog 2 s.rows ∧ 2^Nat.clog 2 s.rows<2^w ∧ s.installed base+t.val*s.rows+2^Nat.clog 2 s.rows≤_) ∧ _
  refine ⟨⟨Nat.two_pow_pos _,?_,?_⟩,cap⟩ <;>dsimp only [temporary] at * <;>omega

theorem strip_width (i : Fin (2*s.targets)) :
    (s.strips which i).left+(s.strips which i).right≤ s.aperture:=by
  by_cases h : i.divNat = 0 <;>
    simp [strips,h,aperture]

theorem read_fits (packet : Expr) (old : packet.Fits w base) (room : s.installed base<2^w) (t : Fin s.targets) :
    DescentPackedZip.Fits (Book.tables (s.project which) s.rootWidth s.oldLanes base t) packet (.lit 0)
      s.rootWidth 0 s.oldLanes (s.installed base) w:=by
  have geometry:=Book.geometry (s.project which) s.rootWidth s.oldLanes base t (out:=s.installed base) le_rfl room
    (by simp [project])
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (s.order base).1 old,trivial,geometry.1,geometry.2,rfl,rfl⟩

theorem any (packet : Expr) (m : Memory w) (old : packet.Fits w base) (room : s.endAddress base<2^w) :
    (s.program which base w packet).Exec m (s.image which base packet m) (s.ticks which base w packet) ∧
    CheapCode (s.program which base w packet) ∧ ∀i,i<base ∨ s.endAddress base≤ i→s.image which base packet m i=m i:=by
  obtain ⟨a,b,c,d⟩:=s.order base
  have r₃:=d.trans_lt room
  have r₂:=c.trans_lt r₃
  have r₁ : s.installed base<2^w:=(Nat.le_add_right ..).trans_lt (b.trans_lt r₂)
  let es:=List.ofFn (s.readControl which base packet)
  have count:es.length=s.targets:=List.length_ofFn
  have f : ∀e∈es,e.Fits w (s.installed base):=by
    intro e he
    obtain ⟨t,rfl⟩:=List.mem_ofFn.mp he
    have q:=s.read_fits which base packet old r₁ t
    exact ⟨q.apply,trivial,q.shift,q.left⟩
  have one:=Book.mount (s.project which) s.rootWidth s.oldLanes base m (fun _=>by simp [project]) r₁
  have scan : (ProtocolRAM.program w (s.scans which base packet)).Exec (s.firstMem which base m)
      (s.copied which base packet m) (clock (s.scans which base packet)) :=
    ProbeStage.Native.columns_exec es (s.firstMem which base m)
    (ProbeStage.Native.columns_safe (n:=s.rows) es (le_refl _) f (by simpa only [count] using b.trans_lt r₂))
  have two:=Strip.any (s.temporary base) s.hosts s.groups s.oldLanes s.lanes s.selectorBits
    (s.temp base) (s.copied which base packet m) (fun j=>(s.temp_room base r₂ j).1) r₃
  have three:=Book.mount (s.strips which) s.aperture s.lanes (s.received base) (s.retiled which base packet m)
    (s.strip_width which) room
  refine ⟨Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then one.1 scan) two.1) three.1,cheap_seq (cheap_seq (cheap_seq one.2.2.2 (@ProtocolRAM.program_cheap _ _)) (s.retile base w).cheap) three.2.2.2,?_⟩
  intro j off
  have past:=((Nat.le_add_right ..).trans b : s.installed base≤ s.temporary base)
  have range : j<s.installed base ∨ s.installed base+es.length*s.rows≤j:=by rw [count];exact off.imp (·.trans_le a) ((b.trans (c.trans d)).trans ·)
  exact (three.2.2.1 j (off.imp_left (·.trans_le (a.trans (past.trans c))))).trans
    ((two.2 j (off.imp (·.trans_le (a.trans past)) (d.trans ·))).trans
    ((ProbeStage.Native.columns_frame es (s.firstMem which base m) range).trans (one.2.2.1 j (off.imp_right ((past.trans (c.trans d)).trans ·)))))

end
end Hierarchy.DescentRetainedControl.Layout

end OAI
