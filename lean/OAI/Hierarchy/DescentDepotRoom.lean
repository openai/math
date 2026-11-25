import OAI.Hierarchy.DescentDepotPage
import OAI.Hierarchy.DescentDepotSetup
import OAI.Hierarchy.DescentDepotZipRoom

namespace OAI
/-! # Native address and dictionary bounds at the mounted ordinary-stage format -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch ProtocolRAM Computability.VPVNP.BurstRAM
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section

namespace Fresh.Book
variable (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape) (K H G M base out w : ℕ)
local notation "rows" => H*chunks G M
local notation "R" => rawBits s*M
local notation "T" => SixBirths.topology z M
local notation "U" => SixBirths.width z M
local notation "slot" => 2^(bits s z M)
local notation "bytes" => physicalSize s z K H G M

/-- The old matching topology and the six printed births are the two dynamic
input banks. Every other address of Fresh.Room follows from the literal layout. -/
theorem bounds (top born : Bank) (input : Expr) (raw : input.Fits w out)
    (topFit : top.Fits w out) (bornFit : born.Fits w out)
    (topWords : (K*H)*chunks G M≤top.size) (bornWords : (K*H)*chunks G M≤born.size)
    (width : U≤w) (before : base+2*(bytes+1)≤out) (cpu : out<2^w) :
    Fresh.Room s z (bank s z K H G M base top born) input H G M w out := by
  have sf:=ceilPage rows
  have endAt:base+rows+2^R+2^T+K*slot≤out:=by unfold physicalSize at before;omega
  refine ⟨raw,bankFits _ ?_ cpu,topFit,bornFit,bankFits _ ?_ cpu,bankFits _ ?_ cpu,
    fun q=>bankFits _ ?_ cpu,sf.1,topWords,bornWords,width,le_rfl,le_rfl,fun _=>room s z M⟩
  · have rowsFit : rows≤bytes := Nat.le_add_right _ _
    exact (Nat.add_le_add_left (sf.2.trans (Nat.mul_le_mul_left 2 (Nat.succ_le_succ rowsFit))) base).trans before
  · exact (Nat.le_add_right _ (2^T)).trans ((Nat.le_add_right _ (K*slot)).trans endAt)
  · exact (Nat.le_add_right _ (K*slot)).trans endAt
  · have edge:=Nat.mul_le_mul_right slot q.isLt
    change base+rows+2^R+2^T+q.val*slot+slot≤out
    rw [Nat.succ_mul] at edge;omega
end Fresh.Book

namespace Setup
variable (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape) (K H J M unit base : ℕ)
local notation "roof" => base+2*(words s z K H J M unit+1)
local notation "first" => DescentSIMDLookup.Book.words (totalBits s) H J M
local notation "second" => base+first
local notation "freshBase" => second+Binary.count s*(2*2^(unit*M))
local notation "rows" => H*chunks J M

theorem lookup_room {w out : ℕ} (src : Bank) (earlier : roof≤ src.base)
    (size : rows≤ src.size) (endAt : src.base+src.size≤out) (space : out+rows<2^w)
    (small : M*max (totalBits s) (outputBits s)≤w/2) :
    let rom:=DescentSIMDLookup.Book.banks base (totalBits s) H J M src
    DescentSIMDLookup.Fits rom (totalBits s) (outputBits s) M H J w out ∧
      rom.dictionary.base+rom.dictionary.size≤rom.source.base ∧ rom.mask.base+rom.mask.size≤rom.source.base := by
  intro rom
  have ceiling:=ceilPage rows
  have scalar:=Nat.two_pow_pos (totalBits s*M)
  have dict : base+2^(totalBits s*M)≤ src.base := by
    unfold words DescentSIMDLookup.Book.words at earlier;omega
  have mask : base+2^(totalBits s*M)+2^(Nat.clog 2 rows)≤ src.base := by
    unfold words DescentSIMDLookup.Book.words at earlier;omega
  have cpu : out<2^w:=by omega
  have low : src.base≤out:=by omega
  exact ⟨⟨bankFits _ endAt cpu,bankFits _ (dict.trans low) cpu,bankFits _ (mask.trans low) cpu,
    size,rfl,ceiling.1,space,small⟩,dict,mask⟩

theorem fresh_room {w out : ℕ} (top born : Bank) (e : Expr) (read : e.Fits w out)
    (topFit : top.Fits w out) (bornFit : born.Fits w out)
    (topWords : (K*H)*chunks J M≤top.size) (bornWords : (K*H)*chunks J M≤born.size)
    (bornWord : SixBirths.width z M≤w) (before : roof≤out) (cpu : out<2^w) :
    Fresh.Room s z (Fresh.Book.bank s z K H J M freshBase top born) e H J M w out := by
  apply Fresh.Book.bounds _ _ _ _ _ _ _ _ _ _ _ _ read topFit bornFit topWords bornWords bornWord _ cpu
  unfold words Binary.words at before;omega

end Setup
end
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
