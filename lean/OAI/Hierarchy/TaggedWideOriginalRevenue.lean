import OAI.Hierarchy.TaggedWideOriginalRoleFacts
import OAI.Hierarchy.TaggedWideStageWidthRun
import OAI.Hierarchy.TaggedWidePublishedSlots

namespace OAI
/-! # Genuine emitted positive widths and original packed port words in the dated scan -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing
variable {T W : ℕ} (g : Dated T) (rom work : ℕ)
local notation "n" => g.rawEdges
local notation "mask" => RoleROM.bank (g.maskROM rom) n

def Dated.widthResult (live : Fin n→Bool) (values : Fin n→ℕ) : PageResult W (g.widthPage rom work) where
  holds out:=∀i,(g.stageWidth work).read out ((3*i.val:ℕ):Word W)=((if live i then values i else 0:ℕ):Word W)
  localize:=by
    intro a b same seen i
    rw [←seen i]
    apply same
    · change g.maskStart work+1-1≤g.maskStart work+1+_
      omega
    · have bound:=Nat.mod_le ((3*i.val:ℕ):Word W).val (g.stageWidth work).size
      have val:=Nat.mod_le (3*i.val) (2^W)
      change g.maskStart work+1+((3*i.val:ℕ):Word W).val%(g.stageWidth work).size<
        g.maskStart work+1+3*n+2*n
      have maxval : ((3*i.val:ℕ):Word W).val≤3*i.val:=val
      have :=i.isLt
      omega

def Dated.slotResult (b : Bool) (m : Memory W) : PageResult W (g.slotPage work b) where
  holds out:=∀i:Fin n,(g.slotBank work b).read out (i.val:Word W)=(g.lanes:Word W)*(g.orderedSlot b).eval m (i.val:Word W)
  localize:=by
    intro a after same seen i
    rw [←seen i]
    apply same
    · change g.slotBase work b-1≤g.slotBase work b+_;omega
    · have v : (i.val:Word W).val≤ i.val:=Nat.mod_le ..
      have h:=Nat.mod_le (i.val:Word W).val (g.slotBank work b).size
      change g.slotBase work b+_ < g.slotBase work b+n+2*n
      have:=i.isLt;omega

private theorem bank_below (b : Bank) (m now : Memory W) (fit : b.Fits W work)
    (low : ∀a,a<work→now a=m a) (i : Word W) : b.read now i=b.read m i := by
  apply low
  have x:=Nat.mod_lt i.val fit.1
  have y:=fit.2.2
  change b.base+i.val%b.size<work
  omega

theorem Dated.width_issued (m : Memory W) (live : Fin n→Bool) (width : Fin n→ℕ)
    (origins : ∀i : Fin n,(mask).read m (i.val:Word W)=(live i).toNat)
    (data : ∀i : Fin n,g.measured.read m ((3*i.val:ℕ):Word W)=(width i:Word W))
    (old : g.measured.Fits W work) (marked : (mask).Fits W work)
    (room : g.workEnd work<2^W) :
    (g.widthResult rom work live width).Issued work m := by
  intro now low
  have floor : work≤g.maskStart work:=by dsimp only [Dated.maskStart,Dated.controlStart,Dated.rolesEnd,endOf];omega
  have fit : g.slotStart work<2^W:= lt_of_le_of_lt (Nat.le_add_right ..) room
  have one : 1<2^W:=by dsimp only [Dated.slotStart] at fit;omega
  have near : work≤g.maskStart work+1:=by omega
  obtain ⟨out,ran,vals,frame⟩:=width_run_flags g rom work now live width
    (fun i=>(bank_below work _ m now marked low _).trans (origins i))
    (fun i=>(bank_below work _ m now old low _).trans (data i))
    ⟨old.1,old.2.1,old.2.2.trans near⟩ ⟨marked.1,marked.2.1,marked.2.2.trans near⟩ fit one
  exact ⟨out,ran,vals,fun a ha=>frame a (.inl (by simpa [Dated.widthPage,Scatter.floor] using ha))⟩

theorem Dated.slot_issued (b : Bool) (m : Memory W) (src : (g.orderedSlot b).Fits W work)
    (room : g.workEnd work<2^W) : (g.slotResult work b m).Issued work m := by
  intro now low
  have next : work≤g.slotStart work:=by
    dsimp only [Dated.slotStart,Dated.maskStart,Dated.controlStart,Dated.rolesEnd,endOf];omega
  have bound : work≤g.slotBase work b:=by dsimp [Dated.slotBase];omega
  have after : g.slotBase work b+n+n+n<2^W:=by
    cases b <;> simp only [Dated.workEnd,Dated.slotBase,Bool.toNat_false,Bool.toNat_true,Nat.zero_mul,Nat.one_mul,
      Nat.add_zero] at room ⊢ <;> omega
  obtain ⟨out,ran,reads,lower⟩:=slot_run g work b now
    (ProtocolRAMGeneratedWrite.fits_mono _ bound src) after
  exact ⟨out,ran,fun i=>(reads i).trans (congrArg ((g.lanes:Word W)*·) (eval_below _ _ m now src low)),lower⟩

/-- The terminal turn publisher and all later original windows only need
retain the memory below the end of this batch to preserve all its receipts. -/
theorem Dated.revenue_frame (r : ∀t f,PageResult W (g.rolePage rom work t f))
    (positive : Fin n→Bool) (values : Fin n→ℕ) (original early later : Memory W)
    (frame : ∀a,a<g.workEnd work→later a=early a)
    (roles : ∀t f,(r t f).holds early) (widths : (g.widthResult rom work positive values).holds early)
    (slots : ∀b,(g.slotResult work b original).holds early) :
    (∀t f,(r t f).holds later) ∧ (g.widthResult rom work positive values).holds later ∧
      ∀b,(g.slotResult work b original).holds later := by
  have maxRole : g.rolesEnd work≤g.workEnd work:=by
    dsimp only [Dated.workEnd,Dated.slotStart,Dated.maskStart,Dated.controlStart,endOf];omega
  refine ⟨?_,?_,?_⟩
  · intro t f
    apply (r t f).localize early later _ (roles t f)
    intro a _ ha
    have e:=(role_order g rom work).upper (finProdFinEquiv (t,f))
    simp only [Equiv.symm_apply_apply] at e
    exact frame a (ha.trans_le (e.trans maxRole))
  · apply (g.widthResult rom work positive values).localize early later _ widths
    intro a _ ha
    apply frame a
    simp only [Dated.widthPage,Scatter.stop,Dated.workEnd,Dated.slotStart] at ha ⊢
    omega
  · intro b
    apply (g.slotResult work b original).localize early later _ (slots b)
    intro a _ ha
    apply frame a
    cases b <;> simp [Dated.slotPage,Scatter.stop,Dated.workEnd,Dated.slotBase] at ha ⊢ <;> omega

end Hierarchy.ProtocolRAM.Calendar.WideCPU
end

end OAI
