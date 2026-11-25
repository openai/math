import OAI.Hierarchy.GridReceiverTickDirectory
import OAI.Hierarchy.TraceReceiverEntryTables
import OAI.ThreeFlat.RAM.HistorySelectedLedger
import OAI.ThreeFlat.RAM.TickSlotKeep

namespace OAI
/-! # Restoring the true elected terminal directory after descendant compilation -/

namespace Hierarchy.GridReceiverDirectoryRestore
set_option quotPrecheck false
open ThreeFlat Diagonal RAM PhysicalProcedure TickWorkspace
open HistoryStageBody.Physical HistoryNodeDirectory.Selected
open Computability.VPVNP.BurstRAM PrivateRAM GridPinPublisher GridReceiverTickDirectory
open scoped Fin.CommRing

variable {w u k n q pins pars sel text compact rails bits N stages full lib first dim T total : ℕ}
local notation "W" => 64*w
local notation "J" => GridDescription.sector w
local notation "g" => GridPinArena.slab w
local notation "P" => canonical w k n q pins pars sel text compact rails bits N stages full (2*2^(w/2))
local notation "A" => GridReceiverTickDirectory.banks w u
local notation "K" => ((20*(w+1)+2)^(k+2))
local notation "count" => (((20*(w+1)+2)^dim)*N)
local notation "beforeLoop" => (fun tables : Memory W => TraceReceiverOwnerMount.output u first N
  (A).owners ((A).scratch+1) ((P).intervalMemory (base u 5) tables))

/-- Rebuild from the durable component of the completed descendant ledger. -/
theorem rebuild_from_durable
    (ht : 0 < T) (cost : Fin N → Fin dim → ℕ) (t : Fin T)
    (R : GridPinArena.Scalars W P bits full K g)
    (ownerRoom : TraceReceiverOwnerMount.Room W u first N (A).owners ((A).scratch+1))
    (large : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w)
    (bitFit : bits ≤ g) (size : lib ≤ stride u) (rootsFit : N ≤ g)
    (classes : (20*(w+1)+2)^dim < 2^W) (ticks : T < 2^W)
    (room : GridReceiverTickDirectory.Room A W (2+text) N count)
    (low : 2+text+W ≤ base u 1)
    {original classified elected tables afterDesc : Memory W}
    (stored : GridSimulation.Assigned ht cost original classified)
    (roster : Ticked A (FactorAllocation.factors w cost (List.finRange N) t) (t.val:Word W) classified elected)
    (retained : TraceReceiverEntryTables.TableFrame w u lib elected tables) (ready : PrefixOwners P tables)
    (durable : ∀ a, TickTerminalRoot.slotKeep u a → afterDesc a=beforeLoop tables a)
    (rawTick : ∀ i < W, original (2+text+i)=((t.val.testBit (W-1-i)).toNat:Word W)) :
    (GridReceiverTickDirectory.build A W (2+text) N count).Spec (·=afterDesc)
      (fun _ restored => Ticked A (FactorAllocation.factors w cost (List.finRange N) t)
        (t.val:Word W) afterDesc restored ∧ ∀ a < base u 1, restored a=original a)
      (GridReceiverTickDirectory.clock W count) := by
  have sep := TraceReceiverOwnerMount.sector (by omega : 0 < w) upper
  have banksFit := GridPinArena.scales w (by omega)
  have keys := room.key
  have owners := room.owner
  have high := room.high
  have rootRoom := room.separate
  have idsFit : (FactorAllocation.factors w cost (List.finRange N) t).length ≤ count := by
    rw [←GridReceiverDirectoryOrder.rows ht w cost t]
    exact (List.length_filterMap_le ..).trans_eq List.length_range
  have keptLow (a : ℕ) (ha : a < base u 1) : TickTerminalRoot.slotKeep u a :=
    .inl (by change a < 13*stride u; change a < 2*stride u at ha;omega)
  have keptHigh (a : ℕ) (ha : 14*J ≤ a) : TickTerminalRoot.slotKeep u a :=
    .inr (by change 20*stride u ≤ a;omega)
  have past (a : ℕ) (left : (A).keys ≤ a) (right : a < (A).scratch) : elected a=classified a :=
    roster.frame a (.inr (by omega)) (.inr (by omega)) (.inl right)
  have frame := TraceReceiverEntryTables.after_classifier R ownerRoom large lower upper bitFit
    size retained ready
  have keyRead (i : Fin N) : afterDesc ((A).keys+i.val)=(GridPinPrefixMemory.factorKey w cost i:Word W) := by
    have hi := i.isLt.trans_le rootsFit
    have stable := durable ((A).keys+i.val) (keptHigh _ (by change 14*J ≤ 15*J+g+i.val;omega))
    exact stable.trans ((frame.1 i.val hi).trans ((past ((A).keys+i.val) (Nat.le_add_right ..) (by have := i.isLt;omega)).trans (stored.key i)))
  have ownerRead (i : Fin N) : afterDesc ((A).owners+i.val)=((FactorAllocation.owner ht w cost i).val:Word W) := by
    have hi := i.isLt.trans_le rootsFit
    have stable := durable ((A).owners+i.val) (keptHigh _ (by change 14*J ≤ 15*J+3*g+i.val;omega))
    exact stable.trans ((frame.2.1 i.val hi).trans ((past ((A).owners+i.val) (by omega) (by have := i.isLt;omega)).trans (stored.owner i)))
  have originalLow (a : ℕ) (lo : a < base u 1) : afterDesc a=original a := by
    have prior := TraceReceiverEntryTables.original R ownerRoom large lower upper bitFit size retained ready a (.inl lo)
    have addr : a < 2*stride u := lo
    have restore := GridReceiverTickDirectory.outside_receiver ht cost t stored roster a
      (by omega) (.inl (by change a < 18*stride u;omega)) (.inl (by change a < 19*stride u;omega))
    exact (durable a (keptLow a lo)).trans (prior.trans restore)
  have tickRead (i : ℕ) (hi : i < W) : afterDesc (2+text+i)=((t.val.testBit (W-1-i)).toNat:Word W) :=
    (originalLow _ (by omega)).trans (rawTick i hi)
  intro pcs regs pubs M pc reg pub exit rom data cfg m entry hm
  subst m
  obtain ⟨time,timeFit,last,out,advance,exitAt,published⟩ :=
    GridReceiverTickDirectory.build_spec A (2+text) w ht cost t room classes ticks
      M pc reg pub exit rom data cfg afterDesc entry ⟨keyRead,ownerRead,tickRead⟩
  refine ⟨time,timeFit,last,out,advance,exitAt,published,?_⟩
  intro a small
  have early : a < 2*stride u := small
  have rootAt : (A).roots=18*stride u := rfl
  exact (published.frame a (.inl (by omega)) (.inl (by omega)) (.inl (by omega))).trans (originalLow a small)

/-- The first procedure in `TraceReceiverProgram.terminal` reads the original
T tick word and the surviving E/T classifier outputs. The input can be the
complete chronological descendant ledger, with S17/S18 in their final scratch
state. Its post supplies the restored roots, both counts, the three zero
cursors, the packed tick word, and the untouched complement relative to that
very descendant memory. -/
theorem rebuild {F : Type*} {dir : HistoryNodeDirectory.Selected.Directory W total}
    {tag : ((Fin 3 → Bool) → F) → ℕ} {vals : Fin total → NodeValue F}
    (ht : 0 < T) (cost : Fin N → Fin dim → ℕ) (t : Fin T)
    (R : GridPinArena.Scalars W P bits full K g)
    (ownerRoom : TraceReceiverOwnerMount.Room W u first N (A).owners ((A).scratch+1))
    (large : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w)
    (bitFit : bits ≤ g) (size : lib ≤ stride u) (rootsFit : N ≤ g)
    (classes : (20*(w+1)+2)^dim < 2^W) (ticks : T < 2^W)
    (room : GridReceiverTickDirectory.Room A W (2+text) N count)
    (low : 2+text+W ≤ base u 1)
    {original classified elected tables afterDesc : Memory W}
    (stored : GridSimulation.Assigned ht cost original classified)
    (roster : Ticked A (FactorAllocation.factors w cost (List.finRange N) t) (t.val:Word W) classified elected)
    (retained : TraceReceiverEntryTables.TableFrame w u lib elected tables) (ready : PrefixOwners P tables)
    (ledger : Ledger u dir tag vals (TickTerminalRoot.slotKeep u) (beforeLoop tables) total afterDesc)
    (rawTick : ∀ i < W, original (2+text+i)=((t.val.testBit (W-1-i)).toNat:Word W)) :
    (GridReceiverTickDirectory.build A W (2+text) N count).Spec (·=afterDesc)
      (fun _ restored => Ticked A (FactorAllocation.factors w cost (List.finRange N) t)
        (t.val:Word W) afterDesc restored) (GridReceiverTickDirectory.clock W count) := by
  exact Procedure.Spec.mono (rebuild_from_durable ht cost t R ownerRoom large lower upper bitFit size
    rootsFit classes ticks room low stored roster retained ready ledger.durable rawTick)
    (fun _ h=>h) (fun _ _ h=>h.1) le_rfl

/-- Every address below S17, every address from S19 through the original
14J registry, and the high journals from 16J preserve the descendant output.
This includes the S12/S13 caches and S43/S44 archive maps. -/
theorem rebuild_frame (pos : 0 < w) (upper : u^10 ≤ 5*w) (five : 5 ≤ stride u) (ht : 0 < T)
    (cost : Fin N → Fin dim → ℕ) (t : Fin T) (src : ℕ)
    (room : GridReceiverTickDirectory.Room A W src N count)
    {afterDesc restored : Memory W}
    (pub : Ticked A (FactorAllocation.factors w cost (List.finRange N) t) (t.val:Word W) afterDesc restored)
    (a : ℕ) (kept : a < base u 17 ∨ (base u 19 ≤ a ∧ a < 15*J) ∨ 16*J ≤ a) :
    restored a=afterDesc a := by
  have countFit := room.separate
  have keys := room.key
  have high := room.high
  have owners := room.owner
  have len : (FactorAllocation.factors w cost (List.finRange N) t).length ≤ count := by
    rw [←GridReceiverDirectoryOrder.rows ht w cost t]
    exact (List.length_filterMap_le ..).trans_eq List.length_range
  have sep := TraceReceiverOwnerMount.sector pos upper
  have sectors := (GridPinArena.scales w pos).1
  have page : base u 18+stride u ≤ base u 19 := by
    change 19*stride u+stride u ≤ 20*stride u
    omega
  have rootAt : (A).roots=base u 17 := rfl
  have ctlAt : (A).controls=base u 18 := rfl
  have scratchAt : (A).scratch=15*J+20*g := rfl
  have space : 0 < g := Nat.two_pow_pos _
  have ctlSize : (A).controls+5 ≤ base u 19 := by
    rw [ctlAt]
    exact (Nat.add_le_add_left five _).trans page
  have controlAt : (A).controls=19*stride u := rfl
  apply pub.frame a <;> rcases kept with h|⟨h1,h2⟩|h <;> omega

/-- The raw input premise of the restore follows from the mounted shifted
controller header, using its exact MSB-first tick field. -/
theorem tick_input {w text args ell T : ℕ} (t : Fin T) (ticks : T < 2^(64*w))
    (fit : text ≤ w^2) (self : Fin (w^2) → Bool) (parameters : Fin args → Word (64*w))
    (selector : Fin ell → Bool) (original : Memory (64*w))
    (hold : let hdr := GridReceiverHeader.header text fit self (t.val:Word (64*w)) parameters selector
      ∀ j : Fin hdr.length,original (2+j.val)=((hdr[j.val]).toNat:Word (64*w))) :
    ∀ i < 64*w, original (2+text+i)=((t.val.testBit (64*w-1-i)).toNat:Word (64*w)) := by
  intro i hi
  let b : Fin (64*w) := ⟨i,hi⟩
  have words : 64*w ≤ (args+1)*(64*w) := Nat.le_mul_of_pos_left _ (Nat.succ_pos args)
  have headerBound : text+i < (GridReceiverHeader.header text fit self (t.val:Word (64*w)) parameters selector).length := by
    rw [GridReceiverHeader.length]
    omega
  have rd := hold ⟨text+i,headerBound⟩
  rw [GridReceiverTickDirectory.header_tick fit self (t.val:Word (64*w)) parameters selector b] at rd
  simpa [b,Fin.val_cast_of_lt (t.isLt.trans ticks),Nat.add_assoc] using rd

end Hierarchy.GridReceiverDirectoryRestore

end OAI
