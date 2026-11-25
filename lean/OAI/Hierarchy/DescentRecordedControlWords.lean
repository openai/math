import OAI.Hierarchy.DescentResetControlPortRead
import OAI.Hierarchy.DescentResetVenueActorRead
import OAI.Hierarchy.DescentResetNewActorDirectory
import OAI.Hierarchy.DescentRecordedActorDirectoryAfterRoots

namespace OAI
/-! # The public operand registers on the reset's attained successor actors -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentDenseHostOrder DescentStageEdgeReceipt
open DescentActorRaster DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDatedAddressBook
open DescentVenueQuantityPlanes DescentResetControlRegisters
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {old : Reached W G q ε S k i z D wire hist} {rates : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset old rates) {oldH H oldM M w a : ℕ}
    (previous : Fintype.card old.V ≤ oldH) (next : Fintype.card B.next.V ≤ H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "Q" => (DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) (GroupStage.depthBound D n f g)).card
local notation "J" => S.groupCount (i+1)
local notation "num" => Fintype.card B.next.V
local notation "cap" => old.placement.cap
local notation "oldId" => old.vertex.trans (Fin.castLEEmb previous)
local notation "chosen" => B.next.vertex.trans (Fin.castLEEmb next)
local notation "rank" => (B.frame.host.symm.toEmbedding.trans old.vertex).trans (Fin.castLEEmb previous)
local notation "raw" => (Z).rawHostRank T rank
local notation "parent" v:arg => DescentDenseHostOrder.position (Z).graph (v).val
local notation "shapeId" v:arg => ((Z).hostFields T rank v).2.val
local notation "depthAt" v:arg => (Z).placement.b (parent v)
local notation "dims" => quantityDims B 1 oldH H oldM M
local notation "c" => (⟨dims,a⟩ : Chart)
local notation "values" x:arg => fun h g=>actualBit B next h g x
variable (start first : ℕ) (src depth levels : Bank) (before rendered : Memory w)
local notation "dir" => (⟨first,oldH,Q,chunks (2^cc) oldM⟩ : DescentResetNewActorDirectory.Layout)
local notation "returned" => (dir).result src before
local notation "L" => State.layout dims start src (dir).count (dir).inverse
local notation "finished" => ((c).phase start src (dir).count (dir).inverse w).image rendered

/-- Read the live bit and all four public register words on the attained
compact host. Every inactive sheet in the same packed word contributes zero. -/
theorem recorded_control_all_rows (oldPos : 0 < oldM) (newPos : 0 < M) (oldBits : oldM ≤ w)
    (actors : ∀(j : Fin Q) (p : Row oldH (2^cc) oldM),before (src.base+j.val*(oldH*chunks (2^cc) oldM)+(row _ _ _ p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) j) p).val:Word w))
    (oldDepth : ∀v,before (depth.base+(oldId v).val)=((Z).placement.b (B.frame.host v):Word w))
    (levelRows : ∀d,d < levels.size → before (levels.base+d)=((d-cc+1:ℕ):Word w))
    (srcFit : src.Fits w first) (srcRoom : oldH*Q*chunks (2^cc) oldM ≤ src.size)
    (depthFit : depth.Fits w first) (depthRoom : oldH ≤ depth.size) (levelFit : levels.Fits w first)
    (levelsRoom : ∀v : B.next.V,depthAt v < levels.size)
    (oldWidth : chunks (2^cc) oldM ≤ 2^w) (directoryEnd : (dir).endAddress < 2^w)
    (earlier : (dir).endAddress ≤ start)
    (held : ∀address,address < (dir).endAddress → rendered address=returned address)
    (room : DescentVenueQuantityPlanes.Room dims L 0 w) (roof : (c).endAddress start < 2^w)
    (short : ∀v : B.next.V,∀t∈[1,cap,depthAt v-cc+1,shapeId v],t < 2^a) :
    (∀x : DescentColonies.Block k,Source ((c).active start x.val) (values x) M finished) ∧
    ∀(v : B.next.V) (x : DescentColonies.Block k) (j : Fin (chunks J M)),
      let p : Row H J M:=(chosen v,j)
      let mask:=data (values x) p
      ((c).live start x.val).eval finished ((row H J M p).val:Word w)=(((c).withMask mask 1).val:Word w) ∧
      ∀i : Fin 4,((c).ports start cap x.val (dir).inverse depth levels i).eval finished ((row H J M p).val:Word w)=
        (((c).withMask mask (![cap,depthAt v-cc+1,0,shapeId v] i)).val:Word w) := by
  by_cases emptyH : H=0
  · constructor
    · intro x p
      have h:=p.1.isLt
      omega
    · intro v
      have h:=(chosen v).isLt
      omega
  by_cases emptyJ : chunks J M=0
  · constructor
    · intro x p
      have h:=p.2.isLt
      omega
    · intro v x j
      have h:=j.isLt
      omega
  have hosts : 0 < H := Nat.pos_of_ne_zero emptyH
  have sheets : 0 < chunks J M := Nat.pos_of_ne_zero emptyJ
  obtain ⟨_,count,inverse,_,_,untouched⟩:=paid_actor_result B previous first src before oldPos oldBits actors srcFit srcRoom oldWidth directoryEnd
  have low : first ≤ (dir).endAddress:=Nat.le_add_right ..
  have original (address : ℕ) (h : address < first) : rendered address=before address:=
    (held _ (h.trans_le low)).trans (untouched _ (.inl h))
  have addressable := (dir).fits directoryEnd
  have countFits := addressable.2.2.2.1
  have invFits := addressable.2.2.2.2
  have invRoom : num ≤ (dir).inverse.size:=by
    let embed : B.next.V ↪ Fin (oldH*Q) := ⟨fun v=>raw v, fun _ _ eq=>(raw).injective eq⟩
    have wide : num ≤ oldH*Q := by simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding embed
    exact wide.trans (dir).ordered.1
  have fit : DescentVenueQuantityPlanes.Room dims L num w:=
    { room with inverseSize:=invRoom, usedFit:=invRoom.trans_lt invFits.2.1 }
  have census : rendered (dir).count.base=(num:Word w):=
    (held _ ((Nat.lt_add_of_pos_right countFits.1).trans_le countFits.2.2)).trans count
  have acquired (v : B.next.V) :
      rendered ((dir).inverse.base+(B.next.vertex v).val)=((raw v).val:Word w) := by
    rw [held _ ((Nat.add_lt_add_left ((B.next.vertex v).isLt.trans_le invRoom) _).trans_le invFits.2.2)]
    simpa only [dense_physical B previous] using inverse v
  have all (j : Fin Q) (p : Row oldH (2^cc) oldM) :
      rendered (src.base+j.val*(oldH*chunks (2^cc) oldM)+(row _ _ _ p).val)=
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) j) p).val:Word w) := by
    have bound:=Nat.mul_le_mul_right (oldH*chunks (2^cc) oldM) j.isLt
    have pos:=(row oldH (2^cc) oldM p).isLt
    rw [Nat.succ_mul] at bound
    have cap₀:Q*(oldH*chunks (2^cc) oldM) ≤ src.size:=by simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using srcRoom
    rw [original _ (by have := srcFit.2.2; omega)]
    exact actors j p
  have measured:=actor_quantity_source B previous next L rendered fit oldPos newPos hosts sheets all census
    (fun v=>by
      change rendered ((dir).inverse.base+((Z).denseHostRank T rank v).val)=_
      rw [dense_physical B previous]
      exact acquired v)
  have regs (x : DescentColonies.Block k) := (c).physical_inputs start src (dir).count (dir).inverse rendered roof x (values x) (measured x)
  refine ⟨fun x=>(regs x).1,?_⟩
  intro v x j p mask
  have control:=((c).any start src (dir).count (dir).inverse rendered fit roof).2
  have finalLow (addr : ℕ) (h : addr < first) : finished addr=before addr:=
    (control _ (.inl (h.trans_le (low.trans earlier)))).trans (original addr h)
  have wide {b : Bank} (ht : b.Fits w (dir).endAddress) : b.Fits w ((c).endAddress start) :=
    ⟨ht.1,ht.2.1,ht.2.2.trans (earlier.trans (by rw [(c).size start,Chart.first,State.shift dims start];omega))⟩
  have older {b : Bank} (ht : b.Fits w first) : b.Fits w ((c).endAddress start) :=
    wide ⟨ht.1,ht.2.1,ht.2.2.trans low⟩
  have ix : (chosen v).val < (dir).inverse.size:=(B.next.vertex v).isLt.trans_le invRoom
  have index : (raw v).val/Q=(oldId (B.frame.host.symm (parent v))).val ∧ (raw v).val%Q=shapeId v := by
    have large : 0 < Q:=Nat.zero_lt_of_lt ((Z).hostFields T rank v).2.isLt
    rw [(Z).rawHostRank_read T rank v]
    rw [Nat.add_mul_div_left _ _ large,Nat.div_eq_of_lt ((Z).hostFields T rank v).2.isLt,
      Nat.zero_add,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ((Z).hostFields T rank v).2.isLt]
    exact ⟨rfl,rfl⟩
  have lastIndex : (raw v).val%(dims).shapes=shapeId v := index.2
  have resident:=(c).resident start src (dir).count (dir).inverse rendered
  have rawAt:=((c).host_read start finished resident roof (dir).inverse (wide invFits) p ix).trans
    ((control _ (.inl ((Nat.add_lt_add_left ix _).trans_le (invFits.2.2.trans earlier)))).trans (acquired v))
  have bound : (raw v).val/Q < depth.size := by
    rw [index.1]
    exact (oldId (B.frame.host.symm (parent v))).isLt.trans_le depthRoom
  have dep : finished (depth.base+(raw v).val/Q)=(depthAt v:Word w) := by
    rw [finalLow _ ((Nat.add_lt_add_left bound _).trans_le depthFit.2.2),index.1]
    simpa only [Equiv.apply_symm_apply] using oldDepth (B.frame.host.symm (parent v))
  have available:=levelsRoom v
  have lev:=(finalLow _ ((Nat.add_lt_add_left available _).trans_le levelFit.2.2)).trans (levelRows _ available)
  have outputs := (c).ports_read start finished resident roof x.val cap (dir).inverse depth levels p mask
    ((regs x).1 p) (raw v) rawAt (depthAt v) (depthAt v-cc+1) bound dep (older depthFit) (older levelFit) available lev
    (by simpa only [lastIndex] using short v)
  refine ⟨outputs.1, ?_⟩
  intro t
  exact (outputs.2 t).trans (congrArg (fun q : ℕ => (((c).withMask mask (![cap,depthAt v-cc+1,0,q] t)).val:Word w)) lastIndex)

theorem recorded_control_words (oldPos : 0 < oldM) (newPos : 0 < M) (oldBits : oldM ≤ w)
    (_hosts : 0 < H) (_sheets : 0 < chunks J M)
    (actors : ∀(j : Fin Q) (p : Row oldH (2^cc) oldM),before (src.base+j.val*(oldH*chunks (2^cc) oldM)+(row _ _ _ p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B previous) j) p).val:Word w))
    (oldDepth : ∀v,before (depth.base+(oldId v).val)=((Z).placement.b (B.frame.host v):Word w))
    (levelRows : ∀d,d < levels.size → before (levels.base+d)=((d-cc+1:ℕ):Word w))
    (srcFit : src.Fits w first) (srcRoom : oldH*Q*chunks (2^cc) oldM ≤ src.size)
    (depthFit : depth.Fits w first) (depthRoom : oldH ≤ depth.size) (levelFit : levels.Fits w first)
    (levelsRoom : ∀v : B.next.V,depthAt v < levels.size)
    (oldWidth : chunks (2^cc) oldM ≤ 2^w) (directoryEnd : (dir).endAddress < 2^w)
    (earlier : (dir).endAddress ≤ start)
    (held : ∀address,address < (dir).endAddress → rendered address=returned address)
    (room : DescentVenueQuantityPlanes.Room dims L 0 w) (roof : (c).endAddress start < 2^w)
    (short : ∀v : B.next.V,∀t∈[1,cap,depthAt v-cc+1,shapeId v],t < 2^a) :
    (∀x : DescentColonies.Block k,Source ((c).active start x.val) (values x) M finished) ∧
    ∀(v : B.next.V) (x : DescentColonies.Block k) (j : Fin (chunks J M)),
      let p : Row H J M:=(chosen v,j)
      let mask:=data (values x) p
      ((c).live start x.val).eval finished ((row H J M p).val:Word w)=(((c).withMask mask 1).val:Word w) ∧
      ∀i : Fin 4,((c).ports start cap x.val (dir).inverse depth levels i).eval finished ((row H J M p).val:Word w)=
        (((c).withMask mask (![cap,depthAt v-cc+1,0,shapeId v] i)).val:Word w) :=
  recorded_control_all_rows B previous next start first src depth levels before rendered
    oldPos newPos oldBits actors oldDepth levelRows srcFit srcRoom depthFit depthRoom levelFit levelsRoom
    oldWidth directoryEnd earlier held room roof short

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
