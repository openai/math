import OAI.Hierarchy.DescentResetPrivatePeerChip
import OAI.Hierarchy.DescentResetStemPeerChip
import OAI.Hierarchy.DescentResetTrunkChip

namespace OAI
/-! # Static peer evidence tables for both stems, the trunk and private devices -/
namespace Hierarchy.DescentResetPeerUnionRAM.RawTables
open DescentSIMDLookup DescentPackedColony DescentDenseHostOrder DescentDyadicSpan ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

/-- These extents depend solely on the date's public ports, palette, packing width and device size. -/
structure Layout where
  base : ℕ
  hosts : ℕ
  shapes : ℕ
  degree : ℕ
  groups : ℕ
  lanes : ℕ
  privateSlots : ℕ
  privateBits : ℕ
  keyBits : ℕ
  ticketBits : ℕ

namespace Layout
variable (L : Layout)
def privateWords := PrivateEvidence.extent L.hosts L.shapes L.privateSlots L.privateBits L.lanes
def stemWords := span (L.hosts*L.shapes)+span (L.shapes*2^(L.keyBits*L.lanes))
def trunkWords := span (L.hosts*L.shapes)+span (L.shapes*2^L.lanes)
def first := L.base+L.privateWords
def second := L.first+L.stemWords
def trunk := L.second+L.stemWords
def endAddress := L.trunk+L.trunkWords
def words := L.privateWords+2*L.stemWords+L.trunkWords
def ticks := 16+10*L.words

theorem end_eq : L.endAddress=L.base+L.words := by
  dsimp [endAddress,trunk,second,first,words]
  omega

theorem bounds : L.base ≤ L.first ∧ L.first ≤ L.second ∧ L.second ≤ L.trunk ∧ L.trunk ≤ L.endAddress :=
  ⟨Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩

def privateData := PrivateEvidence.constants L.hosts L.shapes L.degree L.privateSlots L.privateBits L.lanes L.ticketBits L.groups

end Layout

variable {n h : ℕ} (board : NonlinearExpanders.Graph n h) (r depth : ℕ)
variable {K : ℕ} (L : Layout)
variable (templ : Bool→Fin K→Option (Fin L.shapes×Fin L.shapes))
local notation "st" s => DescentResetStemPeerChip.constants (templ s) L.hosts L.lanes L.degree L.keyBits L.ticketBits
local notation "tr" => DescentResetTrunkChip.constants board r depth L.hosts L.lanes L.degree L.ticketBits

def program (w : ℕ) : Procedure w :=
  (((DescentStaticWordColumn.program w L.base L.privateData L.privateWords).seq
    (DescentStaticWordColumn.program w L.first (st false) L.stemWords)).seq
    (DescentStaticWordColumn.program w L.second (st true) L.stemWords)).seq
    (DescentStaticWordColumn.program w L.trunk tr L.trunkWords)

def image₀ {w : ℕ} (m : Memory w) := DescentStaticWordColumn.image L.base L.privateData m L.privateWords
def image₁ {w : ℕ} (m : Memory w) := DescentStaticWordColumn.image L.first (st false) (image₀ L m) L.stemWords
def image₂ {w : ℕ} (m : Memory w) := DescentStaticWordColumn.image L.second (st true) (image₁ L templ m) L.stemWords
def image {w : ℕ} (m : Memory w) := DescentStaticWordColumn.image L.trunk tr (image₂ L templ m) L.trunkWords

theorem frame₀ {w : ℕ} (m : Memory w) (x : ℕ) (away : x < L.base ∨ L.first ≤ x) :
    image₀ L m x=m x := DescentStaticWordColumn.frame _ _ _ _ _ away

theorem frame₁ {w : ℕ} (m : Memory w) (x : ℕ) (away : x < L.first ∨ L.second ≤ x) :
    image₁ L templ m x=image₀ L m x := DescentStaticWordColumn.frame _ _ _ _ _ away

theorem frame₂ {w : ℕ} (m : Memory w) (x : ℕ) (away : x < L.second ∨ L.trunk ≤ x) :
    image₂ L templ m x=image₁ L templ m x := DescentStaticWordColumn.frame _ _ _ _ _ away

theorem frame₃ {w : ℕ} (m : Memory w) (x : ℕ) (away : x < L.trunk ∨ L.endAddress ≤ x) :
    image board r depth L templ m x=image₂ L templ m x := DescentStaticWordColumn.frame _ _ _ _ _ away

theorem any {w : ℕ} (m : Memory w) (room : L.endAddress < 2^w) :
    (program board r depth L templ w).Exec m (image board r depth L templ m) L.ticks ∧
    CheapCode (program board r depth L templ w) ∧
    DescentStaticWordColumn.names (program board r depth L templ w)=15*(L.words+4) ∧
    ∀x,x < L.base ∨ L.endAddress ≤ x → image board r depth L templ m x=m x := by
  obtain ⟨a,b,c,d⟩:=L.bounds
  refine ⟨?_,cheap_seq (cheap_seq (cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _)
    (@DescentStaticWordColumn.cheap _ _ _ _)) (@DescentStaticWordColumn.cheap _ _ _ _)) (@DescentStaticWordColumn.cheap _ _ _ _),?_,?_⟩
  · have cost : L.ticks = ((4+10*L.privateWords)+(4+10*L.stemWords))+
        (4+10*L.stemWords)+(4+10*L.trunkWords) := by
      unfold Layout.ticks Layout.words
      omega
    rw [cost]
    intro P R K' machine
    exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then
      (@DescentStaticWordColumn.mount w L.base L.privateWords L.privateData m ((b.trans (c.trans d)).trans_lt room))
      (@DescentStaticWordColumn.mount w L.first L.stemWords (st false) (image₀ L m) ((c.trans d).trans_lt room)))
      (@DescentStaticWordColumn.mount w L.second L.stemWords (st true) (image₁ L templ m) (d.trans_lt room)))
      (@DescentStaticWordColumn.mount w L.trunk L.trunkWords tr (image₂ L templ m) room) machine
  · dsimp only [program]
    rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq]
    simp only [DescentStaticWordColumn.names_mount,Layout.words]
    omega
  · intro x away
    have outside (lo hi : ℕ) (l : L.base ≤ lo) (t : hi ≤ L.endAddress) : x < lo ∨ hi ≤ x := away.imp (fun h=>h.trans_le l) (fun h=>t.trans h)
    exact (frame₃ board r depth L templ m x (outside _ _ ((a.trans b).trans c) le_rfl)).trans
      ((frame₂ L templ m x (outside _ _ (a.trans b) d)).trans ((frame₁ L templ m x (outside _ _ a (c.trans d))).trans
        (frame₀ L m x (outside _ _ le_rfl (b.trans (c.trans d))))))

end
end Hierarchy.DescentResetPeerUnionRAM.RawTables

end OAI
