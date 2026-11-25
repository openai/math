import OAI.Hierarchy.DescentPackedMatchChooserInput

namespace OAI
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Chooser
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM
noncomputable section
variable {D H G M a w low high : ℕ}

theorem bank_before {B : Bank} (old : B.Fits w low) (grow : low≤high) : B.Fits w high :=
  ⟨old.1,old.2.1,old.2.2.trans grow⟩

theorem accessible_before (P : Ports D) (act : Bank) (old : Accessible P act H G M w low) (grow : low≤high) :
    Accessible P act H G M w high :=
  ⟨fun i=>bank_before (old.ids i) grow,old.idsRoom,bank_before old.roster grow,old.rosterRoom,
    bank_before old.offsets grow,old.offRoom,bank_before old.chunks grow,old.chunkRoom,
    bank_before old.source grow,old.srcRoom⟩

theorem reads_before (B : Bank) (data : Fin H→Fin G→Cell a) (m o : Memory w)
    (input : Reads B data M m) (reads : ∀i < low,o i=m i)
    (fit : B.Fits w low) (span : H*chunks G M≤B.size) : Reads B data M o := by
  intro p
  exact (reads _ ((Nat.add_lt_add_left ((row H G M p).isLt.trans_le span) B.base).trans_le fit.2.2)).trans (input p)

theorem mounted_before (P : Ports D) (act : Bank) (roster : Fin H→Fin D→Option (Fin H))
    (m o : Memory w) (input : Mounted P roster m G M) (reads : ∀i < low,o i=m i)
    (safe : Accessible P act H G M w low) : Mounted P roster o G M := by
  have here (B : Bank) (h : B.Fits w low) {j : ℕ} (inBounds : j<B.size) :=
    reads (B.base+j) ((Nat.add_lt_add_left inBounds _).trans_le h.2.2)
  refine ⟨fun p i=>(here _ (safe.ids i) ((row H G M p).isLt.trans_le (safe.idsRoom i))).trans (input.ids p i),?_,
    fun i=>(here _ safe.offsets (i.isLt.trans_le safe.offRoom)).trans (input.offsets i),
    fun p=>(here _ safe.chunks ((row H G M p).isLt.trans_le safe.chunkRoom)).trans (input.chunks p)⟩
  intro v i
  have below:=Nat.mul_le_mul_right D v.isLt
  rw [Nat.succ_mul] at below
  have bounded : v.val*D+i.val<H*D:=by have :=i.isLt;omega
  exact (here _ safe.roster (bounded.trans_le safe.rosterRoom)).trans (input.roster v i)

theorem winners_before (C : Layout) (k b D H G M w endAt : ℕ)
    (ordered : C.last D k b H G M+2^(Nat.clog 2 (H*chunks G M+1))≤endAt) (room : endAt<2^w)
    (x : Fin (2^k)) : (C.winners D k b H G M x).Fits w endAt ∧ H*chunks G M≤(C.winners D k b H G M x).size := by
  let count:=H*chunks G M
  let mask:=2^(Nat.clog 2 (count+1))
  have after_ : (C.winners D k b H G M x).base≤C.last D k b H G M :=
    Nat.add_le_add_left (Nat.mul_le_mul_right count x.isLt.le) _
  have size : (C.winners D k b H G M x).size=mask:=rfl
  have stops := (Nat.add_le_add_right after_ mask).trans ordered
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (stops.trans_lt room),stops⟩,
    (Nat.le_succ count).trans (Nat.le_pow_clog (by decide) _)⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Chooser

end OAI
