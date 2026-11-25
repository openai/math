import OAI.Hierarchy.DescentPackedMaskedData
import OAI.Hierarchy.DescentPackedMatchProfileMenu

namespace OAI
/-! # Matched incidence handles and dense profile words in one native execution -/
namespace Hierarchy.DescentPacking.PackedMatch
open DescentSIMDLookup DescentPackedProfileWindow ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M R : ℕ}

def topologyWords (s : Shape) (x : Fin H→Fin G→Inputs s)
    (i : Fin (H*chunks G M)) : Cell (s.outputBits*M) :=
  data (fun h j=>encodeOutput (transform (x h j))) ((row H G M).symm i)

theorem topology_key (s : Shape) (x : Fin H→Fin G→Inputs s) (p : Row H G M) :
    masked (lookupCell s) (fun h j=>encodeInput (x h j)) p =
      (topologyWords s x (row H G M p)).val := by
  rw [masked_eq_data]
  simp only [topologyWords,Equiv.symm_apply_apply,lookupCell,decode_encode]

def full (w R H G M : ℕ) (g : Banks) (l : ProfileTable.Layout) :=
  (physical g l.topology.base H G M w).seq (ProfileTable.issue w R (H*chunks G M) l)

def finished (R H G M : ℕ) (g : Banks) (l : ProfileTable.Layout) (m : Memory w) :=
  ProfileTable.issued l R (H*chunks G M) (result g l.topology.base H G M m)

structure Earlier (w : ℕ) (l : ProfileTable.Layout) : Prop where
  counts : l.countROM.Fits w l.topology.base
  topo : l.tables.topology.Fits w l.topology.base
  off : l.tables.offset.Fits w l.topology.base
  low : l.tables.low.Fits w l.topology.base
  finalROM : l.tables.result.Fits w l.topology.base
  raw : l.raw.Fits w l.topology.base

private theorem before {w B cut d : ℕ} (f : (⟨B,d⟩ : Bank).Fits w cut) (k : Cell d) :
    B+k.val<cut := (Nat.add_lt_add_left k.isLt B).trans_le f.2.2

theorem full_run (s : Shape) (g : Banks) (l : ProfileTable.Layout)
    (fit : DescentSIMDLookup.Fits g s.inputBits s.outputBits M H G w l.topology.base)
    (r : ProfileTable.Room s M R (H*chunks G M) w l) (prior : Earlier w l)
    (x : Fin H→Fin G→Inputs s) (m : Memory w) (stream : ℕ→Cell s.digit)
    (ready : resident s g H G M m)
    (source : ∀p : Row H G M,m (g.source.base+(row H G M p).val)=
      ((data (fun h j=>encodeInput (x h j)) p).val:Word w))
    (pos : 0<R) (size : M*s.pairs≤R) (room : 2*R≤2^w) (digits : R≤2^(s.digit*R))
    (counts : ∀k : Cell (s.outputBits*M),m (l.countROM.base+k.val)=(chunkCount s M k:Word w))
    (menu : ProfileTable.static s M R l.tables m)
    (raw : ∀i<l.raw.size,m (l.raw.base+i)=((word s.digit R stream i).val:Word w))
    (windowRoom : ∀i : Fin (H*chunks G M),
      PackedProfileCursor.total (ProfileTable.quota (M:=M) s (topologyWords (M:=M) s x)) i.val/R+1<l.raw.size) :
    let n:=H*chunks G M
    let keys:=topologyWords (M:=M) s x
    let out:=finished R H G M g l m
    (full w R H G M g l).Exec m out ((4+44*n)+ProfileTable.clock n) ∧
    (∀i : Fin n,out (l.topology.base+i.val)=((keys i).val:Word w)) ∧
    (∀i : Fin n,∀a : Fin M,∀j : Fin s.pairs,
      digit s.digit (finProdFinEquiv (a,j)).val (out (l.out+i.val)).val=
        if j.val<(laneCounts s M (keys i) a).val then
          (stream (PackedProfileCursor.total (ProfileTable.quota s keys) i.val+
            localPrefix (laneCounts s M (keys i)) a+j.val)).val else 0) ∧
    ∀a<l.topology.base,out a=m a := by
  let mid:=result g l.topology.base H G M m
  let keys:=topologyWords (M:=M) s x
  obtain ⟨top,posted,low⟩ := execute s g l.topology.base fit x m ready source
  have stored (i : Fin (H*chunks G M)) : mid (l.topology.base+i.val)=((keys i).val:Word w) := by
    have e:=posted ((row H G M).symm i)
    rw [topology_key,Equiv.apply_symm_apply] at e
    exact e
  have early {b : Bank} {d : ℕ} (fit : b.Fits w l.topology.base) (bw : b.bits=d) (i : Cell d) :
      mid (b.base+i.val)=m (b.base+i.val) := by
    apply low
    have limit : i.val<b.size := by simpa only [Bank.size,bw] using i.isLt
    exact (Nat.add_lt_add_left limit _).trans_le fit.2.2
  have count' := fun k=>(early prior.counts r.countBits k).trans (counts k)
  have menu' : ProfileTable.static s M R l.tables mid :=
    ⟨fun k=>(early prior.topo r.scan.keyT k).trans (menu.1 k),
     fun k=>(early prior.off r.scan.keyO k).trans (menu.2.1 k),
     fun k=>(early prior.low r.scan.keyL k).trans (menu.2.2.1 k),
     fun k=>(early prior.finalROM r.scan.keyR k).trans (menu.2.2.2 k)⟩
  have raw' := fun i hi=>(low _ ((Nat.add_lt_add_left hi _).trans_le prior.raw.2.2)).trans (raw i hi)
  obtain ⟨run_,profiles,keeps⟩ := ProfileTable.run s l r mid keys stream pos size room digits stored count' menu' raw' windowRoom
  exact ⟨top.then run_,fun i=>(keeps _ ((Nat.add_lt_add_left (i.isLt.trans_le r.scan.groups) _).trans_le r.topology.2.2)).trans
    (stored i),profiles,fun a ha=>(keeps _ (ha.trans_le ((Nat.le_add_right l.topology.base l.topology.size).trans r.topology.2.2))).trans (low _ ha)⟩

theorem full_cheap (w R H G M : ℕ) (g : Banks) (l : ProfileTable.Layout) :
    CheapCode (full w R H G M g l) :=
  @cheap_seq w (physical g l.topology.base H G M w) (ProfileTable.issue w R (H*chunks G M) l)
    (@cheap g l.topology.base H G M w) (@ProfileTable.issue_cheap w R (H*chunks G M) l)

theorem full_fee (s : Shape) (H G payload W ratio : ℕ)
    (nonzero : 0<ProfileTable.envelope s) (wide : 2*ProfileTable.envelope s≤payload)
    (compare : W≤ratio*payload) :
    let M:=lanes payload (ProfileTable.envelope s)
    let n:=H*chunks G M
    ((4+44*n)+ProfileTable.clock n)*W≤ratio*(428*payload+636*(H*payload+4*H*G*ProfileTable.envelope s)) := by
  let M:=lanes payload (ProfileTable.envelope s)
  let n:=H*chunks G M
  have vol:=volume H G payload (ProfileTable.envelope s) nonzero wide
  have fee:=(ProfileTable.fee s H G payload W ratio nonzero wide compare).1
  have topology : (4+44*n)*W≤ratio*(4*payload+44*(H*payload+4*H*G*ProfileTable.envelope s)) := by
    have h:=Nat.mul_le_mul_left (4+44*n) compare
    change n*payload≤_ at vol
    have h' := Nat.mul_le_mul_left ratio vol
    nlinarith only [h,h']
  change ((4+44*n)+ProfileTable.clock n)*W≤_
  rw [Nat.add_mul]
  change ProfileTable.clock n*W≤_ at fee
  nlinarith only [topology,fee]

end
end Hierarchy.DescentPacking.PackedMatch

end OAI
