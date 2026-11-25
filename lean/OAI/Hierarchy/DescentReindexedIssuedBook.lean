import OAI.Hierarchy.DescentNamedRootReindex
import OAI.Hierarchy.DescentRecordedRootBook

namespace OAI
/-! # The reindexed receiver constructs the same root book and sender sources -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentPackedWalsh DescentPackedColony DescentPlainTerminal.Suffix
open DescentSixParty DescentResetGates DescentSharedLeafLookup DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false

/-- Only these four operands of the root issuer have types depending on reindexed widths. -/
structure IssuedDeck (D n r h bits : ℕ) where
  peers : Ports D
  board : NonlinearExpanders.Graph n h
  primitive : CanonicalTag (2^n)→Cell bits
  page : DescentSixParty.Chronology.RootPage r (2^n)

variable {D cap N n r c H G K R M hm lb tiny field Ht w Db cb nb rb depth hosts groups height h bits : ℕ}
  (a : Receiver D cap N n r c H G K R M hm lb tiny field Ht w)
  (E : EstimatorArena) (st : StencilBook) (old : StencilBook.Sources) (base split width : ℕ)
  (id : Bank) (prior : Expr) (f fee full total pitch packet C groupDigits batches layerBits factor : ℕ)
  (deck : IssuedDeck D n r h bits)
local notation "bookAt" recv:arg menu:arg => (recv).issuedBook E st old base split width (menu).peers id prior f fee full total pitch
  (menu).board packet C groupDigits batches layerBits factor (menu).primitive (menu).page
local notation "sourcesAt" recv:arg menu:arg => (recv).atlasSources E st old base split width (menu).peers id prior f fee full total pitch
  (menu).board packet C groupDigits batches layerBits factor (menu).primitive (menu).page

namespace IssuedDeck
/-- Reindex the rotor and endpoints in the four dependent inputs simultaneously. -/
def reindex (d : D=Db) (nn : n=nb) (rr : r=rb) : IssuedDeck Db nb rb h bits :=by
  subst Db; subst nb; subst rb; exact deck

theorem original (d : D=Db) (nn : n=nb) (rr : r=rb) :
    let next:=deck.reindex d nn rr
    HEq next.peers deck.peers ∧ HEq next.board deck.board ∧ HEq next.primitive deck.primitive ∧ HEq next.page deck.page :=by
  subst Db; subst nb; subst rb;exact ⟨HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩
theorem mounted {HH GG MM ww : ℕ} (d : D=Db) (nn : n=nb) (rr : r=rb)
    (rs : Fin HH→Fin D→Option (Fin HH)) (m : Memory ww)
    (seen : Mounted deck.peers rs m GG MM) :
    Mounted (deck.reindex d nn rr).peers (fun v j=>rs v (j.cast d.symm)) m GG MM :=by
  subst Db; subst nb; subst rb; exact seen

theorem accessible {HH GG MM ww roof : ℕ} (d : D=Db) (nn : n=nb) (rr : r=rb)
    (prior : Bank) (room : Accessible deck.peers prior HH GG MM ww roof) :
    Accessible (deck.reindex d nn rr).peers prior HH GG MM ww roof :=by
  subst Db; subst nb; subst rb; exact room

end IssuedDeck

/-- The reindexed book and atlas sources are the two original constructors on the same transported arguments. -/
theorem reindex_issued (prepared : a.PreparedFits (bookAt a deck)) (d : D=Db) (cp : cap=cb)
    (nn : n=nb) (rr : r=rb) (cc : c=depth) (hh : H=hosts) (gg : G=groups) (ht : Ht=height) :
    let set:=IndexedRoots.mk a (bookAt a deck) prepared (sourcesAt a deck)
    let result:=set.reindex d cp nn rr cc hh gg ht
    let after:=deck.reindex d nn rr
    result.book=bookAt result.receiver after ∧ result.sources=sourcesAt result.receiver after :=by
  subst Db; subst cb; subst nb; subst rb; subst depth; subst hosts; subst groups; subst height
  exact ⟨rfl,rfl⟩

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
