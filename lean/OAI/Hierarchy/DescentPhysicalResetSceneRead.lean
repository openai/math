import OAI.Hierarchy.DescentPhysicalResetScene
import OAI.Hierarchy.DescentResetParentDirectoryRead

namespace OAI
/-! # Actual intermediate memory words in the completed stem image -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (v : CandidateFront) (base : ℕ) (s : v.Scene) {w : ℕ} (space : v.SceneRoom base s w)
local notation "P" => v.peer
local notation "C" => v.contactLayout base
local notation "last₀" => (P).endAddress (v.peers base)
local notation "F" => v.received base s space

def preDonors (m : Memory w) :=(v.originalPhase base s space).image m
def preContacts (m : Memory w) :=(v.donorPhase base s space).image (v.preDonors base s space m)
def prePeers (m : Memory w) :=(v.contactPhase base s space).image (v.preContacts base s space m)
def preScalar (m : Memory w) :=(v.triplePhase base s space).image (v.prePeers base s space m)
def preParent (m : Memory w) :=(v.scalarPhase base s w).image (v.preScalar base s space m)

include space in
theorem peer_boundaries : base≤v.rawTablesEnd base ∧ v.rawTablesEnd base≤v.donorEnd base ∧
    v.donorEnd base≤v.peers base ∧ v.peers base≤last₀ := by
  have low : base≤v.oldKeys base:=by dsimp [oldKeys,DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start];omega
  obtain ⟨d₁,d₂,d₃⟩:=v.donor.ordered (v.donorStart base)
  obtain ⟨a,b,c,d,e⟩:=(C).ordered
  obtain ⟨x,y,z,t⟩:=(P).ordered (v.peers base)
  refine ⟨?_,(d₁.trans d₂).trans d₃,(((a.trans b).trans c).trans d).trans e,((x.trans y).trans z).trans t⟩
  rw [←v.tables_end base space.sameLanes,(v.rawTables base).end_eq]
  exact low.trans (Nat.le_add_right ..)

/-- Every stage below the stem keeps its original physical read at the final date image. -/
theorem retained_cuts (m : Memory w) :
    (∀a,a<v.parentStart base → (F).image m a=v.preParent base s space m a) ∧
    (∀a,a<last₀ → (F).image m a=v.preScalar base s space m a) ∧
    (∀a,a<v.peers base → (F).image m a=v.prePeers base s space m a) ∧
    (∀a,a<v.donorEnd base → (F).image m a=v.preContacts base s space m a) ∧
    ∀a,a<base → (F).image m a=m a := by
  have m₁:=(C).any s.rotor s.boardReads (v.sensor base s) space.contact (v.preContacts base s space m)
  have m₂:=(P).publish s.peers (v.peers base) (v.prePeers base s space m) space.peers
  have m₃:=DescentResetTrunkCompactScalar.any v.newHosts last₀ s.count s.inverse s.rawHeader
    (v.preScalar base s space m) space.count space.inverse space.scalar space.parent
  have m₄:=v.stem_any s.stems base space.stems (v.preParent base s space m)
  have s₃: last₀≤v.parentStart base:=Nat.le_add_right ..
  have s₂ : v.peers base≤last₀:=by
    obtain ⟨a,b,c,d⟩:=(P).ordered (v.peers base)
    exact ((a.trans b).trans c).trans d
  have s₁ : v.donorEnd base≤v.peers base:=by
    obtain ⟨a,b,c,d,e⟩:=(C).ordered
    exact (((a.trans b).trans c).trans d).trans e
  have k₄ (a) (h:a<v.parentStart base) : (F).image m a=v.preParent base s space m a:=m₄.2.1 a (.inl h)
  have k₃ (a) (h:a<last₀) : (F).image m a=v.preScalar base s space m a:=
    (k₄ a (h.trans_le s₃)).trans (m₃.2.1 a (.inl h))
  have k₂ (a) (h:a<v.peers base) : (F).image m a=v.prePeers base s space m a:=
    (k₃ a (h.trans_le s₂)).trans (m₂.2.1 a (.inl h))
  have k₁ (a) (h:a<v.donorEnd base) : (F).image m a=v.preContacts base s space m a:=
    (k₂ a (h.trans_le s₁)).trans (m₁.2.2 a (.inl h))
  exact ⟨k₄,k₃,k₂,k₁,fun a h=>(v.received_any base s space m).2 a (.inl h)⟩

theorem preScalar_lower (m : Memory w) (i : ℕ) (low : i<base) : v.preScalar base s space m i=m i := by
  obtain ⟨f,g,h,j⟩:=v.peer_boundaries base s space
  have held:=v.retained_cuts base s space m
  exact (held.2.1 i (low.trans_le (((f.trans g).trans h).trans j))).symm.trans
    (held.2.2.2.2 i low)

theorem preScalar_palette (m : Memory w) (j : Fin 3)
    (i : Fin ((P).oldHosts*(DescentDenseHostOrder.roster s.peers.board s.peers.rootBits s.peers.depth).card)) :
    v.preScalar base s space m ((P).threshold (v.peers base)+j.val*(P).hosts+i.val)=
      (DescentResetTrunkPalette.value s.peers.board s.peers.rootBits s.peers.depth j i:Word w) :=
  (P).palette_word s.peers (v.peers base) (v.prePeers base s space m) space.peers j i

/-- Keep the same attained roster, including membership of loops, after the three later peer scans. -/
theorem preScalar_peers (m : Memory w)
    (property : (Fin (P).hosts→Fin 3→Option (Fin (P).hosts))→Prop)
    (found : ∃rows, (∀h j,
      DescentResetPeerUnionRAM.Program.output (v.peers base) (P).oldHosts (P).shapes (P).oldDegree
        (P).bits (P).evidenceLanes (P).evidenceGroups s.peers.old s.peers.test s.peers.src
        (v.prePeers base s space m) ((P).rawPeers (v.peers base)+j.val*(P).hosts+h.val)=
          (DescentPackedExchange.target (rows h j):Word w)) ∧ property rows) :
    ∃rows,(∀h j,v.preScalar base s space m ((P).rawPeers (v.peers base)+j.val*(P).hosts+h.val)=
      (DescentPackedExchange.target (rows h j):Word w)) ∧ property rows := by
  obtain ⟨rows,received,holds⟩:=found
  refine ⟨rows,fun h j=>?_,holds⟩
  exact ((P).three_word s.peers (v.peers base) (v.prePeers base s space m) space.peers j h).trans (received h j)

/-- The original three neighbor ordinals survive the compact scalar, bounded parent and every stem. -/
theorem neighbor_read (m : Memory w) (j : Fin 3) (i : Fin (P).hosts) :
    let lo:=v.peers base
    let adr:=(P).rawPeers lo+j.val*(P).hosts+i.val
    (F).image m adr=DescentResetPeerUnionRAM.Program.output lo (P).oldHosts (P).shapes (P).oldDegree
      (P).bits (P).evidenceLanes (P).evidenceGroups s.peers.old s.peers.test s.peers.src (v.prePeers base s space m) adr := by
  intro lo adr
  obtain ⟨_,a,b,c⟩:=(P).ordered lo
  have whole:(P).rawPeers lo+3*(P).hosts≤(P).three lo:=le_rfl
  have l:=Nat.mul_le_mul_right (P).hosts (Nat.succ_le_of_lt j.isLt)
  rw [Nat.succ_mul] at l
  have early:adr<(P).three lo:=by dsimp only [adr];have:=i.isLt;omega
  exact ((v.retained_cuts base s space m).2.1 adr (early.trans_le ((a.trans b).trans c))).trans
    ((P).three_word s.peers lo (v.prePeers base s space m) space.peers j i)

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
