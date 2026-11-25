import OAI.Hierarchy.TraceReceiverOriginalRows
import OAI.Hierarchy.TraceReceiverAge

namespace OAI
/-! # The original leaf image survives the chronological compiler's earlier writes -/

namespace Hierarchy.TraceReceiverOriginal
open ThreeFlat Diagonal NavigationPass RAM PhysicalStage
open HistoryContraction Diagonal.TraceBitHeader TickWorkspace LaneCursor
open RAM.HistoryInitialSeed RAM.HistoryNodeDirectory RAM.HistoryNodeDirectory.Selected
open RAM.HistoryStageBody.Physical RAM.TraceBucketAtom Computability.VPVNP.BurstRAM PrivateRAM
open HistorySelectedSeedDecode TraceReceiverSeedWords HistorySelectedSeed
open scoped Fin.CommRing
noncomputable section

variable {F : Type} [Field F] [Fintype F] {W pc regs slots S base k low fuel : ℕ}
    (M : Machine W pc regs slots) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F≤2^W) (st : Word W) (raw dict masks gateBase : ℕ)
set_option quotPrecheck false
local notation "installed" => Installed (q:=k) (low:=low) (S:=S) (f:=fuel)
    hF t.width t.labels base st t.header t.time regs slots t.grid raw dict masks gateBase hF

/-- The compact template, inverse dictionary and offset table need exactly
the high bank containing those three arrays. -/
theorem image_above {m o : Memory W} {lo : ℕ} (source : installed m)
    (gate : lo≤gateBase) (directory : lo≤dict) (mask : lo≤ masks)
    (frame : ∀a,lo≤a → o a=m a) : installed o := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [frame (gateBase+i) (by omega)]
    exact source.mounted i hi
  · intro a
    rw [frame (dict+_) (by omega)]
    exact source.dictionary a
  · intro i
    rw [frame (masks+i.val) (by omega)]
    exact source.offsets i

/-- In particular the real booted source survives every earlier compiled
node, its result metadata, and the actual counter increment for this node. -/
theorem installed_at_entry {u n : ℕ} {D : Directory W n} {values : Fin n→NodeValue F}
    {tag : ((Fin 3→Bool)→F)→ℕ} {j : Fin n} {warm prev : Memory W}
    (live : Ledger u D tag values (TickTerminalRoot.slotKeep u) warm j.val prev)
    (ctrl : TickWorkspace.base u 18<2^W) (image : installed warm)
    (gate : TickWorkspace.base u 19≤gateBase) (directory : TickWorkspace.base u 19≤dict)
    (mask : TickWorkspace.base u 19≤ masks) : installed (bump (ownerData W u) prev) :=
  image_above M t hF st raw dict masks gateBase image gate directory mask
    (fun a ha=>NativeNavigation.bumped_kept live ctrl (by unfold stride;positivity) a (.inr ha))

/-- Writes of a single original occurrence are all strictly below S19. Thus
every authentic high table, independent of its length, is protected. -/
theorem protect_above {u : ℕ} (shape : TraceBucketAtom.Layout) (z : Site) {start : ℕ} (len : ℕ)
    (above : TickWorkspace.base u 19≤ start) (width : 2≤volume u)
    (scratch : volume u+42≤ stride u) (rows : 4*z.rows (initial u shape)≤volume u)
    (ext : z.extPins≤volume u)
    (stream : TickWorkspace.base u 12+(z.index+1)*(volume u)^2≤TickWorkspace.base u 13)
    (result : TickWorkspace.base u 13+8*z.index+8≤TickWorkspace.base u 14) :
    Protected (initial u shape) z start len := by
  let A:=initial u shape
  let V:=volume u
  have v2 : 2*V≤V*V := Nat.mul_le_mul_right _ width
  have chart : z.stream A+V*V≤TickWorkspace.base u 13 := by
    change TickWorkspace.base u 12+z.index*(V*V)+V*V≤_
    simpa only [pow_two,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using stream
  have s13:=apart (u:=u) (by decide : 13<19)
  have s14:=apart (u:=u) (by decide : 14<19)
  change 4*z.rows A≤V at rows
  change z.extPins≤V at ext
  refine ⟨.inr ?_,.inr ?_,.inr ?_,.inr ?_⟩
  · change TickWorkspace.base u 14+V+42≤_
    omega
  · change z.stream A+4*z.rows A≤_
    omega
  · change z.stream A+V+z.extPins≤_
    omega
  · change TickWorkspace.base u 13+8*z.index+6≤_
    omega

/-- All six seed header and output spans fit for every selected ID below V².
The two large arrays are from its independent native registration, and V⁴ is
the sector spacing in this receiver. -/
theorem selected_rooms {u n : ℕ} (j : Fin n) (wide : 4≤volume u) (size : n≤(volume u)^2) :
    TickWorkspace.base u 12+(j.val+1)*(volume u)^2≤TickWorkspace.base u 13 ∧
    TickWorkspace.base u 13+8*j.val+8≤TickWorkspace.base u 14 := by
  let V:=volume u
  have ji : j.val+1≤V^2:=Nat.succ_le_of_lt (j.isLt.trans_le size)
  have sq : 8≤V^2 := (by decide : 8≤4^2).trans (Nat.pow_le_pow_left wide 2)
  have fit : (j.val+1)*V^2≤V^2*V^2:=Nat.mul_le_mul_right _ ji
  have hold : 8*(j.val+1)≤V^2*V^2:=Nat.mul_le_mul sq ji
  have stroke : stride u=V^2*V^2 := by change V^4=_;ring
  have a:=apart (u:=u) (by decide : 12<13)
  have b:=apart (u:=u) (by decide : 13<14)
  rw [stroke] at a b
  change _+(j.val+1)*V^2≤_ ∧ _+8*j.val+8≤_
  omega

end
end Hierarchy.TraceReceiverOriginal

end OAI
