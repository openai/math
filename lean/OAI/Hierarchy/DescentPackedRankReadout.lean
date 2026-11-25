import OAI.Hierarchy.DescentPackedLeafAddress
import OAI.Hierarchy.DescentPackedIssuedBookRank

namespace OAI
/-! # End-to-end packed read from the measured shared book table and real signed wires -/
namespace Hierarchy.DescentPackedLeafAddress
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSharedBookScan DescentSharedLeafLookup
open DescentFallbackShapeTable DescentPacking.PackedMatch.Local.Gather DescentSharedCableNames.Stage
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {r Y D cap b d H G M w : ℕ}
local notation "K" => DescentSharedBookScan.bits r Y D
local notation "N" => DescentSharedBookScan.width r Y D
variable (P : Ports D) (prior : Bank) (tables : Fin D→Tables) (select : Tables) (signed : Expr)
    (B : Header) (scores : Fin (DescentSharedBookScan.width r Y D)→Tables) (final : Tables)
local notation "pointer" => addressExpr P prior H tables select signed
local notation "dict" => collect scores (source B) (List.finRange N)
local notation "operation" => DescentSharedLeafLookup.lookup B scores final pointer

theorem compiled_read (s : Bool) (root : Fin (rows r Y)) (out : ℕ) (m : Memory w)
    (rs : Fin H→Fin D→Option (Fin H)) (roster : Mounted P rs m G M) (access : Accessible P prior H G M w out)
    (data : Fin H→Fin G→Cell b) (value : Reads prior (fun h j=>tagged (data h j)) M m)
    (chips : Fin H→Fin G→Option (Live D cap)) (sign : Source signed (fun h j=>DescentSignedCableCodec.encode (chips h j)) M m)
    (ports : Bounds (w:=w) (d:=b+1) (M:=M) tables (peerExpr P prior H) out)
    (rom : ∀i,Static (tables i) (setField (d:=b+1) i) M m)
    (fit : DescentPackedZip.Fits select signed (collect tables (peerExpr P prior H) (List.finRange D))
      (DescentSignedCableCodec.width D cap) ((b+1)*D) M out w)
    (static : Static select (key (D:=D) (cap:=cap) (b:=b) s root) M m)
    (readable : Readable B N H G M d w out) (fixed : Fixed B N H G M d m)
    (rank : Fin H→Fin N→Cell d) (measured : ∀h j,m (B.ranks.base+(h.val*N+j.val))=((rank h j).val:Word w))
    (safeDict : Bounds (w:=w) (d:=d) (M:=M) scores (source B) out)
    (staticDict : ∀i,Static (scores i) (setField (d:=d) i) M m)
    (safeRead : DescentPackedZip.Fits final pointer dict K (d*N) M out w)
    (readRom : Static final (choose (k:=K) (d:=d) N) M m)
    (endFit : out+H*chunks G M<2^w) :
    let bound : Fin H → Fin G → Cell K := fun h j=>((chips h j).bind fun chip=>if chip.target=s then
      (rs h chip.neighbor).map (fun u=>(chip.neighbor,u)) else none).elim 0
        (fun t=>remote root (some t.1) (data t.2 j).val)
    let result:=image out (H*chunks G M) operation m
    (scan w out (H*chunks G M) operation).Exec m result (4+H*chunks G M*(2*(operation).work+4)) ∧
      (∀p : Row H G M,result (out+(row H G M p).val)=
        ((DescentSIMDLookup.data (fun h j=>choose (k:=K) (d:=d) N (bound h j) (encode d N (rank h))) p).val:Word w)) ∧
      CheapCode (scan w out (H*chunks G M) operation) := by
  intro bound result
  have addr : Source pointer bound M m := gathered P prior tables select signed s root out m rs roster access data value chips sign ports rom fit static
  have sourceRank : Source (operation) (fun h j=>choose (k:=K) (d:=d) N (bound h j) (encode d N (rank h))) M m :=
    DescentSharedLeafLookup.lookup_source B scores final pointer out m readable fixed rank measured
      safeDict staticDict safeRead readRom bound addr
  have safe : (operation).Fits w out:=⟨safeRead.apply,⟨safeRead.right,⟨safeRead.shift,safeRead.left⟩⟩⟩
  have read:=DescentSharedLeafLookup.lookup_issued B scores final pointer out m safe endFit _ sourceRank
  exact ⟨read.1,read.2,@scan_cheap _ _ _ _⟩

end
end Hierarchy.DescentPackedLeafAddress

end OAI
