import OAI.Hierarchy.DescentNamedResetSheets
import OAI.Hierarchy.DescentPhysicalResetOriginalSeries
import OAI.Hierarchy.DescentResetPublicDonorRead

namespace OAI
/-! # One original-cable compilation chart for the actual four reset sectors -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs
open DescentCompiler DescentSixParty DescentResetLocalRoster DescentSIMDLookup DescentResetPublicParentWord
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
noncomputable section
variable {n d : ℕ} (S : AtomSchedule) (board : NonlinearExpanders.Graph n d)
  (k tail age D f g cap M : ℕ)
set_option quotPrecheck false
local notation "s" => CandidateSheets.fromBoard S board k tail age D f g cap M
local notation "Ht" => GroupStage.depthBound D n f g
local notation "X" => 2^k
local notation "N" => (2^k)*(2*cap)
local notation "J" => 2*N
local notation "sockets" => max (2^n) (2^Ht)
local notation "p₀" => DescentResetCableSlots.cableCap board Ht

def geometryFor : Shape :=⟨D+2,k,2^n,(2^k+1)*(D+2)*2^k,cap,sockets,p₀⟩

/-- The direct sector starts immediately after the unique trunk slot. -/
def publicAt : Fin ((s).contacts+1)↪Fin (s).candidates where
  toFun j:=⟨J+j.val,by have cut:=j.isLt;rw [CandidateSheets.roster];omega⟩
  inj' a b h:=Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

def stemAt : Fin J↪Fin (s).candidates:=
  Fin.castLEEmb (by rw [CandidateSheets.roster];omega)

def privateAt : Fin (s).privates↪Fin (s).candidates where
  toFun j:=⟨J+1+(s).contacts+j.val,by have cut:=j.isLt;rw [CandidateSheets.roster];omega⟩
  inj' a b h:=Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

def requestAt (half : ℕ) (j : Fin (2*half)) : Bool×ℕ:=
  let p : Fin 2×Fin half:=finProdFinEquiv.symm j
  (finTwoEquiv p.1,p.2.val+1)

def sideAt (count cap : ℕ) (j : Fin (2*(count*(2*cap)))) :=
  ((DescentResetStemPackedIssue.ordinal count cap).symm j).1

/-- The public graph and dimensions determine every instruction, sector and
orientation. The six prior data channels have the physical lane layout of the
original sender and compact halo. -/
def fromBoard (sensor : DescentResetOriginalDonors.Sensors N) (prev : DescentResetPublicOriginalPhase.Prior X (s).contacts N)
    (stem : Fin X→Fin J→Fin 6→Expr) (privateMeta : Fin X→Fin (s).privates→Expr)
    (zero halo : Fin X→Expr) : (s).OriginalInputs where
  boardBits:=n
  boardPorts:=d
  board:=board
  signedSlots:=N
  stems:=J
  geometry:=geometryFor board k D f g cap
  treeHeight:=Ht
  degree:=D
  blockBits:=k
  resultBits:=originalBits D k n Ht cap (programCount board Ht) g
  publicShelf:=publicAt S board k tail age D f g cap M
  stemShelf:=stemAt S board k tail age D f g cap M
  privateShelf:=privateAt S board k tail age D f g cap M
  request:=requestAt (rootSlots k (2^n)*(2^n+2^Ht))
  side:=sideAt X cap
  sensor:=sensor
  sources:=prev
  stem:=stem
  privateMeta:=privateMeta
  zero:=zero
  halo:=halo

theorem original_sector (sensor : DescentResetOriginalDonors.Sensors N) (prev : DescentResetPublicOriginalPhase.Prior X (s).contacts N)
    (stem : Fin X→Fin J→Fin 6→Expr) (priv : Fin X→Fin (s).privates→Expr) (zero halo : Fin X→Expr) :
    let u:=fromBoard S board k tail age D f g cap M sensor prev stem priv zero halo
    (∀j,(u.stemShelf j).val=j.val) ∧ (∀j,(u.publicShelf j).val=J+j.val) ∧
      (∀j,(u.privateShelf j).val=J+1+(s).contacts+j.val) ∧ u.resultBits=originalBits D k n Ht cap p₀ g ∧
      ∀sign j,u.side (DescentResetStemPackedIssue.ordinal X cap (sign,j))=sign :=by
  refine ⟨fun _=>rfl,fun _=>rfl,fun _=>rfl,rfl,?_⟩
  intro sign j
  exact congrArg Prod.fst ((DescentResetStemPackedIssue.ordinal X cap).symm_apply_apply (sign,j))

end
end Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs

end OAI
