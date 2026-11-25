import OAI.Hierarchy.DescentResetRootROMPrice
import OAI.Hierarchy.DescentResetSignedPagePrice
import OAI.Hierarchy.DescentResetIssuedCatalogPrice

namespace OAI
/-! The entire issued root program has three traffic terms: host rows, packed groups,
and shared tables. Its scalar coefficient is independent of the number of hosts and of
the processor word width. -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.SignedFields DescentGLNielsen
open DescentSIMDLookup DescentPackedWalsh DescentPlainTerminal.Suffix DescentPackedColony DescentResetGates
open DescentPackedPrivateMenu DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

structure Charges where
  cap : ℕ
  limbs : ℕ
  depth : ℕ
  projections : ℕ
  pages : ℕ
  arity : ℕ
  matrix : ℕ
  scalar : ℕ
  dimension : ℕ
  guardWork : ℕ
  rowWork : ℕ

namespace Charges
variable (s : Charges)

def retile (rows share : ℕ) :=
  let qty:=2*rows+share
  let fieldCount:=2*s.cap*s.limbs
  (8+10*qty+fieldCount*(4+rows*100))+7*(15*(qty+1)+(15+fieldCount*203))

def signed (rows share : ℕ) :=
  let printed:=s.depth+s.depth*share+6*s.depth*(2*(2*s.cap*rows+1)+share)
  let joined:=s.limbs*(2*share)
  let read:=1+18*s.limbs
  let lanes:=2*s.cap
  (4+10*joined)+((8+10*printed)+(4+lanes*(4+rows*(2*read+4)))+
    ((4+s.depth*42)+(4+s.depth*(4+lanes*rows*224))))+
  7*(15*(joined+1)+15*(printed+2)+(15+lanes*(11+4*read))+(87+(15+s.depth*451)))

def projected (rows share : ℕ) :=
  s.projections*(8+10*(share+2*rows+1)+44*rows)+4+7*(s.projections*(15*(share+2*rows+2)+91)+15)

def rom (hosts rows share : ℕ) :=
  DescentSharedBookScan.Public.lanes*(2*(hosts*s.matrix+s.scalar)+1)+2*(2*rows+1)+(2*share+1)+
  s.pages*((2*s.arity+2)*share+(2*rows+2)+((2*(s.dimension+2)+1)*(1+share)+4*hosts+2))

def catalog (hosts rows : ℕ) :=
  let time:=(4+hosts*s.matrix*(2*s.guardWork+4))+(4+rows*(2*s.rowWork+4))+(4+44*rows)
  let text:=(11+4*s.guardWork)+102+4*s.rowWork
  s.pages*(time+7*text)+109

def total (hosts rows share : ℕ) :=
  s.retile rows share+s.signed rows share+s.projected rows share+
  ((4+10*s.rom hosts rows share)+7*(15*(s.rom hosts rows share+1)))+s.catalog hosts rows

theorem linear (hosts rows share : ℕ) (positive : 0 < share) :
    s.total hosts rows share ≤ s.total 1 1 1*(hosts+rows+share) := by
  let z:=hosts+rows+share
  have H:hosts ≤ z:=by dsimp [z];omega
  have R:rows ≤ z:=by dsimp [z];omega
  have S:share ≤ z:=by dsimp [z];omega
  have up:s.total hosts rows share ≤ s.total z z z := by
    unfold total retile signed projected rom catalog
    dsimp only
    gcongr
  apply up.trans
  change s.total z z z ≤ s.total 1 1 1*z
  obtain ⟨d,eq⟩:=Nat.exists_eq_add_of_le (show 1 ≤ z by dsimp [z];omega)
  rw [eq]
  unfold total retile signed projected rom catalog
  dsimp only
  ring_nf
  omega

end Charges

variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr) (f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n))
local notation "book" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
local notation "L" => 2^r
local notation "b" => DescentSignedCableCodec.width D cap
local notation "args" => arityLimit D L cap n r
local notation:max "half" payload:arg => 2^(payload/2)

def issuedCharges (D cap N n r high low Ht dimension read : ℕ) : Charges where
  cap:=cap
  limbs:=N
  depth:=(schedule (high+low)).length
  projections:=count (2^r) cap
  pages:=Fintype.card (RootPage r (2^n))
  arity:=arityLimit D (2^r) cap n r
  matrix:=DescentSharedBookScan.width r (2^n) D
  scalar:=(r+1)+2^r+(2^n+1)+DescentFallbackShapeTable.imageSize r (2^n) (2^Ht)
  dimension:=dimension
  guardWork:=10000*(D+1)^2*(2^Ht+1)
  rowWork:=1+arityLimit D (2^r) cap n r*(read+11)

/-- The split is valid for every original item count and absolute start, including
a clipped output with many more high groups than its Walsh tile. -/
theorem prepared_traffic (payload : ℕ) (groups : G=2^c)
    (rows : 2^h₀=chunks (2^c) M)
    (ratio : R ≤ payload+1) (lanes : M ≤ payload)
    (oldKey : b*(R*M) ≤ payload/2) (matrixKey : (h₀+l)*(h₀+l) ≤ payload/2)
    (glKey : (b+b)*2^l ≤ payload/2)
    (joinKey : joinWidth b N*M ≤ payload/2) (queryKey : maxBits t D cap L*M ≤ payload/2)
    (lookupKey : (field*(args+1))*M ≤ payload/2) (copyKey : stencil.n*M ≤ payload/2)
    (reserveKey : total ≤ payload/2) (digit : field ≤ payload/2) :
    a.wholeBill book ≤
      (issuedCharges D cap N n r h₀ l Ht E.dim (readWork stencil.m old.count priorCapacity)).total 1 1 1*
      (H+H*chunks (2^c) M+(payload+1)*2^(payload/2)) := by
  let s:=issuedCharges D cap N n r h₀ l Ht E.dim (readWork stencil.m old.count priorCapacity)
  let tr:=H*chunks (2^c) M
  let shared:=(payload+1)*2^(payload/2)
  have one:0 < shared:=Nat.mul_pos (Nat.succ_pos _) (Nat.two_pow_pos _)
  have exp:half payload ≤ shared:=Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have reserved:2^total ≤ shared:=(Nat.pow_le_pow_right (by decide) reserveKey).trans exp
  have repeated:(M+1)*2^field ≤ shared:=Nat.mul_le_mul (Nat.add_le_add_right lanes 1)
    (Nat.pow_le_pow_right (by decide) digit)
  have oldTable:R*half payload ≤ shared:=Nat.mul_le_mul_right _ ratio
  have A:=retile_keys (N:=N) (H:=H) (G:=G) (payload/2) oldKey
  have retile:retileBill D cap N H G R M ≤ s.retile tr shared := by
    apply A.trans
    unfold retileCharge Charges.retile
    simp only [groups]
    change 8+10*(2*tr+R*half payload)+_+7*(15*(2*tr+R*half payload+1)+_) ≤
      8+10*(2*tr+shared)+_+7*(15*(2*tr+shared+1)+_)
    dsimp only [s,issuedCharges]
    gcongr
  have B:=a.chip_keys payload matrixKey glKey joinKey
  have signed:chipBill D cap N H M h₀ l a.printed ≤ s.signed tr shared := by
    apply B.trans
    unfold signedCharge signedWords Charges.signed
    dsimp only [s,issuedCharges,tr]
    simp only [rows,Nat.mul_assoc]
    gcongr
  have C₀:=a.projections_bound (payload/2) queryKey
  have projected:a.projectionsBill ≤ s.projected tr shared := by
    apply C₀.trans
    unfold Charges.projected
    dsimp only [s,issuedCharges,tr]
    gcongr
  have D₀:=a.issued_rom_price E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
    (payload/2) lookupKey copyKey
  have installed:a.rootROMWords book ≤ s.rom H tr shared := by
    apply D₀.trans
    unfold Charges.rom
    dsimp only [s,issuedCharges,tr]
    simp only [Nat.add_assoc]
    gcongr
  have catalog:a.rootCatalogBill book ≤ s.catalog H tr:=
    a.issued_catalog_price E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
      f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
  apply (show a.wholeBill book ≤ s.total H tr shared by
    unfold wholeBill Charges.total
    omega).trans
  exact s.linear H tr shared one

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
