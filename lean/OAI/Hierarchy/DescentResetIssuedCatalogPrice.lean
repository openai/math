import OAI.Hierarchy.DescentIssuedRootWork
import OAI.Hierarchy.DescentPreparedSignedTariff
import OAI.Hierarchy.DescentSharedBookTariff

namespace OAI
/-! The real root catalog pays one scatter and gather per host group and one original
rank scan per fallback shape. -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSixParty.Chronology DescentPackedZip DescentPacking.PackedMatch.Local.Gather
open DescentPackedWalsh DescentPackedColony DescentPlainTerminal.Suffix DescentPackedColony.Phase.Arena
open DescentSixParty DescentResetGates DescentSharedLeafLookup DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false

def catalogUnit (r n D H groups M Ht limit : ℕ) :=
  let rows:=H*chunks groups M
  let guardWork:=10000*(D+1)^2*(2^Ht+1)
  let hosts:=H*DescentSharedBookScan.width r (2^n) D
  let time:=(4+hosts*(2*guardWork+4))+(4+rows*(2*limit+4))+(4+44*rows)
  let text:=(11+4*guardWork)+102+4*limit
  Fintype.card (RootPage r (2^n))*(time+7*text)+109

variable {D cap N n r c H G K R M h₀ l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w)
    (book : RootBook n r D (2^r) cap field)

theorem root_catalog_price (limit : ℕ) (operand : ∀(p : RootPage r (2^n))
    (tbl : Fin (book.table p).1→Tables), (assembly tbl (book.table p).2.reads).work ≤ limit) :
    a.rootCatalogBill book ≤ catalogUnit r n D H (2^c) M Ht limit := by
  let ts:=a.rootedTemplates book
  let rows:=H*chunks (2^c) M
  let guardWork:=10000*(D+1)^2*(2^Ht+1)
  let hosts:=H*DescentSharedBookScan.width r (2^n) D
  let time:=(4+hosts*(2*guardWork+4))+(4+rows*(2*limit+4))+(4+44*rows)
  let text:=(11+4*guardWork)+102+4*limit
  have price (p : RootPage r (2^n)) : ts.fee H (2^c) M Ht p ≤ time ∧ ts.textFee H Ht p ≤ text := by
    rcases p with ⟨side,⟨k,j⟩|q⟩
    · let p : RootPage r (2^n):=(side,.inl (k,j))
      let body:=(ts.good side k j).2
      have win:(assembly body.tables body.reads).work ≤ limit:=operand p body.tables
      have work:=Nat.mul_le_mul_left rows (Nat.add_le_add_right (Nat.mul_le_mul_left 2 win) 4)
      change (4+rows*(2*(assembly body.tables body.reads).work+4))+(4+44*rows) ≤ time ∧
        102+4*(assembly body.tables body.reads).work ≤ text
      dsimp only [time,text]
      omega
    · let p : RootPage r (2^n):=(side,.inr q)
      let block:=ts.exceptional side q
      have win:(assembly block.2.tables block.2.reads).work ≤ limit:=operand p block.2.tables
      have guard_:(DescentSharedBookScan.record block.1 H D (2^Ht) (Ht+2)).work ≤ guardWork:=
        DescentSharedBookScan.shared_work ..
      have run:=Nat.mul_le_mul_left rows (Nat.add_le_add_right (Nat.mul_le_mul_left 2 win) 4)
      have root:=Nat.mul_le_mul_left hosts (Nat.add_le_add_right (Nat.mul_le_mul_left 2 guard_) 4)
      change (4+hosts*(2*(DescentSharedBookScan.record block.1 H D (2^Ht) (Ht+2)).work+4))+
          ((4+rows*(2*(assembly block.2.tables block.2.reads).work+4))+(4+44*rows)) ≤ time ∧
        (11+4*(DescentSharedBookScan.record block.1 H D (2^Ht) (Ht+2)).work)+(102+4*(assembly block.2.tables block.2.reads).work) ≤ text
      dsimp only [time,text]
      omega
  have total:=Finset.sum_le_sum (fun p (_ : p∈(Finset.univ : Finset (RootPage r (2^n))))=>(price p).1)
  have gates:=Finset.sum_le_sum (fun p (_ : p∈(Finset.univ : Finset (RootPage r (2^n))))=>(price p).2)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at total gates
  change _+4+7*(_+15)≤_*(time+7*text)+109
  nlinarith only [total,gates]

section
variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr) (f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n))
local notation "L" => 2^r
local notation "groups" => 2^c
local notation "prev" => a.issuedSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch
local notation "B" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage


theorem issued_catalog_price :
    a.rootCatalogBill (B) ≤ catalogUnit r n D H groups M Ht
      (1+arityLimit D L cap n r*(readWork stencil.m old.count priorCapacity+11)) :=
  a.root_catalog_price (B) _ (a.issued_assembly E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage)
end
end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
