import OAI.Hierarchy.TraceReceiverDescendantExecution
import OAI.Hierarchy.TraceReceiverEntryFrame
import OAI.Hierarchy.TraceReceiverOriginalFrame
import OAI.Hierarchy.GridReceiverDirectoryFrame
import OAI.Hierarchy.GridReceiverBanks

namespace OAI
/-! # Reading the journal, published node banks and codebooks at the mounted descendant entry -/

namespace Hierarchy.TraceReceiverDescendantVisits
open ThreeFlat Diagonal PhysicalStage TickWorkspace RAM
open HistoryStageBody.Physical Computability.VPVNP.BurstRAM PrivateRAM GridRegisteredSetting
open TraceReceiverLeafSetup GridPinPublisher
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {w pc regs slots S addr fuel k : ℕ}
variable (D : RunData F (64*w) pc regs slots S addr fuel k (w/2)) (l : GridNativeImage.Layout)
set_option quotPrecheck false
local notation "u" => TraceAdmission.receiverAge w
local notation "W" => 64*w
local notation "B" => D.block
local notation "J" => GridDescription.sector w
local notation "g" => GridPinArena.slab w
local notation "P" => GridReceiverBanks.pinPlan D l
local notation "A" => GridReceiverTickDirectory.banks w u
local notation "installed" => TraceReceiverTablesMount.installed D
local notation "written" => TraceReceiverTablesMount.output D
local notation "entry" => TraceReceiverDescendantExecution.entry D
local notation "W0" => libraryWords B W

/-- Neither the classifier nor its S17/S18 election scan touches the retained
journal or the published S43/S44 columns. The number of selected entries is
bounded by the number of distinct actual factors. -/
theorem election_keeps {N d T : ℕ} (ht : 0<T) (cost : Fin N→Fin d→ℕ) (tick : Fin T)
    (saved classified elected : Memory W)
    (assignment : GridSimulation.Assigned ht cost saved classified)
    (election : GridReceiverTickDirectory.Ticked A (FactorAllocation.factors w cost (List.finRange N) tick)
      (tick.val:Word W) classified elected)
    (factorCount : N≤ stride u) (positive : 0<w) (upper : u^10≤5*w) (a : ℕ)
    (atLeast : base u 20≤a) (atMost : a<base u 45) : elected a=saved a := by
  let ids:=FactorAllocation.factors w cost (List.finRange N) tick
  have bounded : ids.length≤N := by simpa [ids] using (FactorAllocation.factors_nodup ht w cost tick).length_le_card
  have sector:=TraceReceiverOwnerMount.sector positive upper
  have step : 8≤ stride u := by
    have lower:=TraceAdmission.receiverAge_lower w
    change 2^3≤(2^(u^10))^4
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply GridReceiverTickDirectory.outside_receiver ht cost tick assignment election
  · change a<46*stride u at atMost;omega
  · apply Or.inr
    change 18*stride u+ids.length≤a
    change 21*stride u≤a at atLeast
    omega
  · apply Or.inr
    change 19*stride u+5≤a
    change 21*stride u≤a at atLeast
    omega

/-- Read the three physical code banks, the mounted S38 catalog and both
protected intervals after the canonical pin plan and the actual owner pass. -/
theorem entry_tables {K f n heap : ℕ} {m : Memory W}
    (R : GridPinArena.Scalars W P S (2^(k+1)) K g)
    (owners : PrefixOwners P (written m)) (room : TraceReceiverOwnerMount.Room W u f n (A).owners ((A).scratch+1))
    (wide : 2≤w) (upper : u^10≤5*w) (bits : S≤g) (heapFit : heap≤ start w)
    (tableSpan : start w+W0≤base u 43)
    (src : installed (written m)) (lib : Mounted B W W (start w) (written m))
    (decodeFrame : ∀z,z<gateBase D→(z< start w ∨ start w+W0≤z)→written m z=m z)
    (high : start w+W0≤gateBase D) :
    let live:=entry f n P m
    installed live ∧ Mounted B W W (start w) live ∧
    (∀z,base u 20≤z→z<heap→live z=m z) ∧ (∀z,base u 43≤z→z<base u 45→live z=m z) := by
  intro live
  have lower:=TraceAdmission.receiverAge_lower w
  have keep (i) (h : TraceReceiverEntryFrame.Kept w u i) : live i=written m i :=
    TraceReceiverEntryFrame.after R room wide lower upper bits (written m) owners i h
  have up {i j : ℕ} (h : i≤j) : base u i≤base u j := Nat.mul_le_mul_right _ (by omega)
  have sectors:=TraceReceiverOwnerMount.sector (by omega : 0<w) upper
  have g16 : 16*J≤gateBase D := by change _≤26*J;omega
  have d16 : 16*J≤dict D := by change _≤27*J;omega
  have m16 : 16*J≤ masks D :=
    (Nat.mul_le_mul_right J (by decide : 16≤27)).trans (Nat.le_add_right ..)
  have outside (z : ℕ) (ha : 16*J≤z) := keep z (Or.inr (Or.inr ha))
  refine ⟨TraceReceiverOriginal.image_above D.machine D.fit D.field D.state 0 (dict D) (masks D) (gateBase D)
    src g16 d16 m16 outside,⟨?_⟩,?_,?_⟩
  · intro i
    have below:=tableSpan.trans (up (by decide : 43≤45))
    exact (keep _ (Or.inr (.inl ⟨(up (by decide : 12≤38)).trans (Nat.le_add_right ..),
      by have:=i.isLt;change base u 38+_≤base u 45 at below;change base u 38+_<base u 45;omega⟩))).trans (lib.words i)
  · intro z low hi
    have strict:=hi.trans_le heapFit
    have keepZ:=keep z (Or.inr (.inl ⟨(up (by decide : 12≤20)).trans low,
      strict.trans_le (up (by decide : 38≤45))⟩))
    exact keepZ.trans (decodeFrame z (strict.trans_le ((Nat.le_add_right ..).trans high)) (.inl strict))
  · intro z low hi
    have lo45 : base u 45≤gateBase D := by change 46*stride u≤26*J;omega
    exact (keep z (.inr (.inl ⟨(up (by decide : 12≤43)).trans low,hi⟩))).trans
      (decodeFrame z (hi.trans_le lo45) (.inr (tableSpan.trans low)))

end
end Hierarchy.TraceReceiverDescendantVisits

end OAI
