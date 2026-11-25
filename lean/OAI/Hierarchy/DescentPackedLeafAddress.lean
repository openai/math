import OAI.Hierarchy.DescentSignedChartAddress
import OAI.Hierarchy.DescentSignedCableCodec
import OAI.Hierarchy.DescentPackedMaskedData
import OAI.Hierarchy.DescentPackedFieldGather

namespace OAI
/-! # Routing real signed and opposite-endpoint chips to the fallback rank lookup -/
namespace Hierarchy.DescentPackedLeafAddress
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSharedBookScan DescentFallbackShapeTable
open DescentPacking.PackedMatch.Local.Gather DescentSharedCableNames.Stage
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {r Y D cap b H G M w : ℕ}

def tagged (x : Cell b) : Cell (b+1) := ⟨x.val+1,by
  rcases Nat.eq_zero_or_pos b with e|_
  · subst b;simp at *
  · have a:=x.isLt
    have z:=Nat.one_lt_two_pow ‹0<b›.ne'
    rw [pow_succ];omega⟩

theorem publish_tag (B : Banks) (out : ℕ) (fit : DescentSIMDLookup.Fits B b (b+1) M H G w out)
    (raw : Fin H→Fin G→Cell b) (m : Memory w) (inputs : PinFrame (M:=M) B tagged raw m) :
    let reached:=image out (H*chunks G M) (DescentSIMDLookup.lookup B) m
    (DescentSIMDLookup.program B out H G M w).Exec m reached (4+H*chunks G M*44) ∧
      ∀p : Row H G M,reached (out+(row H G M p).val)=
        ((data (fun h j=>tagged (raw h j)) p).val:Word w) := by
  have fits : (DescentSIMDLookup.lookup B).Fits w out := by
    simp [DescentSIMDLookup.lookup,Expr.Fits,fit.source,fit.dictionary,fit.mask]
  refine ⟨scan_exec _ _ _ m fits fit.output,fun p=>?_⟩
  exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans
    ((lookup_read B out fit tagged raw m inputs p).trans (by rw [masked_eq_data]))

def key (s : Bool) (root : Fin (rows r Y)) (signed : Cell (DescentSignedCableCodec.width D cap))
    (others : Cell ((b+1)*D)) : Cell (bits r Y D) :=
  match DescentSignedCableCodec.decode D cap signed with
  | none=>0
  | some z=>
    let v:=((encode (b+1) D).symm others z.neighbor).val
    if z.target=s ∧ 0<v then remote root (some z.neighbor) (v-1) else 0

theorem key_data (s : Bool) (root : Fin (rows r Y)) (z : Option (Live D cap))
    (peers : Fin D→Option (Fin H)) (word : Fin H→Cell b) :
    key s root (DescentSignedCableCodec.encode z) (encode (b+1) D (fun j=>(peers j).elim 0 (fun h=>tagged (word h))))=
      (z.bind (fun chip=>if chip.target=s then (peers chip.neighbor).map (fun h=>(chip.neighbor,h)) else none)).elim 0
        (fun p=>remote root (some p.1) (word p.2).val) := by
  rw [key,DescentSignedCableCodec.decode_encode]
  cases z with
  | none=>rfl
  | some z=>
    cases hg:peers z.neighbor with
    | none=>simp [Equiv.symm_apply_apply,hg]
    | some a=>by_cases side:z.target=s <;> simp [Equiv.symm_apply_apply,hg,side,tagged]

def addressExpr (P : Ports D) (old : Bank) (H : ℕ) (g : Fin D→Tables) (select : Tables) (signed : Expr) :=
  select.read signed (collect g (peerExpr P old H) (List.finRange D))

theorem gathered (P : Ports D) (old : Bank) (tables : Fin D→Tables) (select : Tables) (signed : Expr)
    (s : Bool) (root : Fin (rows r Y)) (out : ℕ) (m : Memory w)
    (rs : Fin H→Fin D→Option (Fin H)) (roster : Mounted P rs m G M) (access : Accessible P old H G M w out)
    (data : Fin H→Fin G→Cell b) (value : Reads old (fun h j=>tagged (data h j)) M m)
    (chips : Fin H→Fin G→Option (Live D cap)) (real : Source signed (fun h j=>DescentSignedCableCodec.encode (chips h j)) M m)
    (bounds : Bounds (w:=w) (d:=b+1) (M:=M) tables (peerExpr P old H) out)
    (rom : ∀i,Static (tables i) (setField (d:=b+1) i) M m)
    (fit : DescentPackedZip.Fits select signed (collect tables (peerExpr P old H) (List.finRange D))
      (DescentSignedCableCodec.width D cap) ((b+1)*D) M out w)
    (static : Static select (key (D:=D) (cap:=cap) (b:=b) s root) M m) :
    Source (addressExpr P old H tables select signed)
      (fun h j=>((chips h j).bind fun chip=>if chip.target=s then (rs h chip.neighbor).map
        (fun u=>(chip.neighbor,u)) else none).elim 0 (fun p=>remote root (some p.1) (data p.2 j).val)) M m := by
  let words h j i:=(rs h i).elim 0 (fun u=>tagged (data u j))
  have word (i : Fin D) : Source (peerExpr P old H i) (fun h j=>words h j i) M m :=
    peerSource P old out access rs m roster _ value i
  have array:=collected tables (peerExpr P old H) out bounds m rom words word (List.finRange D)
  simp only [List.mem_finRange,ite_true] at array
  have null : key (D:=D) (cap:=cap) (b:=b) s root 0 0=0 := by
    rw [←DescentSignedCableCodec.empty (D:=D) (cap:=cap),key,DescentSignedCableCodec.decode_encode]
  have got:=read_data select signed _ out fit (key s root) null m static _ _ real array
  simpa only [addressExpr,words,key_data] using got

end
end Hierarchy.DescentPackedLeafAddress

end OAI
