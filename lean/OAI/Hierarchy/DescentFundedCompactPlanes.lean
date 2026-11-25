import OAI.Hierarchy.DescentOrdinaryRasterRun

namespace OAI
/-! # Compact the two successor quantity planes inside their true native allocations -/
namespace Hierarchy.DescentOrdinaryRasterReturn
open DescentSIMDLookup DescentVenueQuantityPlanes ProtocolRAM
noncomputable section

theorem allocated_bank_fits {w top : ℕ} (b : Bank) (hi : b.base+b.size≤top) (room : top<2^w) :
    b.Fits w top := ⟨Nat.two_pow_pos _,(Nat.le_add_left b.size b.base).trans_lt (hi.trans_lt room),hi⟩

theorem allocated_bank_later {w a b : ℕ} {p : Bank} (f : p.Fits w a) (hi : a≤b) : p.Fits w b :=
  ⟨f.1,f.2.1,f.2.2.trans hi⟩

/-- Both quantity compactions read the same authenticated new-host count bank and
the same dyadic identity column. Their output spans occur consecutively. -/
theorem room_from_allocated_columns (d : Dims) (B : DescentOrdinaryRasterReturn.Sources) (base w : ℕ)
    (paid : B.paid.Fits w base) (alive : B.alive.Fits w base) (count : B.count.Fits w base)
    (paidSize : d.shapes*d.oldHosts*chunks (d.groups*d.blocks) d.oldLanes≤B.paid.size)
    (aliveSize : d.shapes*d.oldHosts*chunks (d.groups*d.blocks) d.oldLanes≤B.alive.size)
    (lanes : 0<d.lanes) (blocks : 0<d.blocks) (room : DescentOrdinaryRasterReturn.roof d base<2^w) :
    DescentOrdinaryRasterReturn.Room d B base 0 w := by
  have bf : base≤first d base:=Nat.le_add_right ..
  have fs : first d base≤ second d base:=by
    change first d base≤State.roof d (first d base)
    rw [State.shift]
    exact Nat.le_add_right ..
  have se : second d base≤DescentOrdinaryRasterReturn.roof d base:=by
    change second d base≤State.roof (actor d) (second d base)
    rw [State.shift]
    exact Nat.le_add_right ..
  have firstFit: first d base<2^w:=(fs.trans se).trans_lt room
  have span : d.hosts≤2^(Nat.clog 2 d.hosts):=Nat.le_pow_clog (by decide) _
  have column : base+d.hosts<2^w:=(Nat.add_le_add_left span base).trans_lt firstFit
  have host : d.hosts≤2^w:=((Nat.le_add_left d.hosts base).trans_lt column).le
  have inv : (inverse d base).Fits w (first d base):=allocated_bank_fits _ (le_refl _) firstFit
  refine ⟨State.room d (first d base) B.paid B.count (inverse d base) (allocated_bank_later paid bf) (allocated_bank_later count bf)
    inv paidSize (Nat.zero_le _) (Nat.two_pow_pos _) host lanes blocks (se.trans_lt room),?_,column⟩
  exact State.room (actor d) (second d base) B.alive B.count (inverse d base) (allocated_bank_later alive (bf.trans fs))
    (allocated_bank_later count (bf.trans fs)) (allocated_bank_later inv fs) aliveSize (Nat.zero_le _) (Nat.two_pow_pos _)
    host lanes blocks room

end
end Hierarchy.DescentOrdinaryRasterReturn

end OAI
