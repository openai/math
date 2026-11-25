import OAI.Hierarchy.DescentIssuedContactShape

namespace OAI
/-! # Read a portable contact ticket before communication across the old signed port -/
namespace Hierarchy.DescentContactSenderTicket
open DescentResetLocalRoster DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image DescentIssuedGoodHeaders
open DescentPacking.PackedMatch.Local.Gather DescentSharedCableNames DescentIssuedContactShape DescentContactReceiver
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M w field : ℕ}

/-- Combine a one-based owner, an attained row or leaf start, and the actual book depth. -/
def join (Ht r Y ownerNumber rowNumber treeHeight : ℕ) : Cell (Packed.bits (bound Ht r Y)) :=
  let q:=ownerNumber-1
  let z:=if q<2^(r+1) then rowNumber else Y+treeSlot Ht treeHeight rowNumber
  if live : 0<ownerNumber ∧ q<rootSlots r Y ∧ z<Y+2^Ht then
    Packed.token (some (finProdFinEquiv (⟨q,live.2.1⟩,⟨z,live.2.2⟩)))
  else 0

def sender (Ht r Y : ℕ) (x : Fin 3→Cell field) := join Ht r Y (x 0).val (x 1).val (x 2).val

theorem empty (Ht r Y : ℕ) (x : Fin 3→Cell field) (absent : (x 0).val=0) :
    sender Ht r Y x=0 := by simp [sender,join,absent]

theorem join_good (Ht r Y : ℕ) (q : code r) (z : Fin Y) (treeHeight : ℕ) :
    (join Ht r Y ((rootId r Y (.inl q)).val+1) z.val treeHeight).val=
      (rootId r Y (.inl q)).val*(Y+2^Ht)+z.val+1 := by
  have live:=(rootId r Y (.inl q)).isLt
  have left : (rootId r Y (.inl q)).val<2^(r+1) := by
    exact (DescentResetCableSlots.interval r q).isLt
  have small : z.val<Y+2^Ht:=z.isLt.trans_le (Nat.le_add_right ..)
  simp [join,left,live,small,Packed.token,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]

theorem good (Ht r Y : ℕ) (q : code r) (z : Fin Y) (x : Fin 3→Cell field)
    (own : (x 0).val=(rootId r Y (.inl q)).val+1) (row : (x 1).val=z.val) :
    (sender Ht r Y x).val=(rootId r Y (.inl q)).val*(Y+2^Ht)+z.val+1 := by
  simpa only [sender,own,row] using join_good Ht r Y q z (x 2).val

theorem join_fallback (Ht r Y : ℕ) (q : code r×Option (Fin Y)) (d : ℕ) (v : Fin d→Bool) (depth : d≤Ht) :
    (join Ht r Y ((rootId r Y (.inr q)).val+1) (DescentTreePrefixIntervals.start Ht v) d).val=
      (rootId r Y (.inr q)).val*(Y+2^Ht)+(Y+(DescentRotor.bitWord d v).val)+1 := by
  have live:=(rootId r Y (.inr q)).isLt
  have right : ¬(rootId r Y (.inr q)).val<2^(r+1) := by
    change ¬ 2^(r+1)+_ < 2^(r+1)
    omega
  have small:=Nat.add_lt_add_left ((DescentRotor.bitWord d v).isLt.trans_le (Nat.pow_le_pow_right (by decide) depth)) Y
  simp [join,right,live,treeSlot_read,small,Packed.token,finProdFinEquiv_apply_val,
    Nat.add_comm,Nat.mul_comm]
theorem fallback (Ht r Y : ℕ) (q : code r×Option (Fin Y)) (d : ℕ) (v : Fin d→Bool) (depth : d≤Ht)
    (x : Fin 3→Cell field) (own : (x 0).val=(rootId r Y (.inr q)).val+1)
    (observed : (x 1).val=DescentTreePrefixIntervals.start Ht v) (height : (x 2).val=d) :
    (sender Ht r Y x).val=(rootId r Y (.inr q)).val*(Y+2^Ht)+
      (Y+(DescentRotor.bitWord d v).val)+1 := by
  simpa only [sender,own,observed,height] using join_fallback Ht r Y q d v depth

theorem issue (Ht r Y : ℕ)
    (tables : Fin 3→Tables) (reads : Fin 3→Expr) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (x : Fin H→Fin G→Fin 3→Cell field) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*3) (Packed.bits (bound Ht r Y)) M H G w out.base)
    (rom : resident (sender Ht r Y ∘ (encode field 3).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*3)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (outputRoom : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>sender Ht r Y (x a g)) M dst ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out.base ∨ out.base+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,whole,_,frame⟩:=gathered_words (sender Ht r Y) tables reads menu mid out.base
    x pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ outputRoom whole,frame⟩

end
end Hierarchy.DescentContactSenderTicket

namespace Hierarchy.DescentSixParty.ResetInput
open DescentChosenRouter DescentCommonHost DescentDenseHostOrder DescentContacts DescentContactReceiver DescentRelativeContacts
open DescentResetTrunks DescentResetAttachments DescentContactShapeRead
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bw : P→ℕ} {A : MarkedWorld F d P bw}
    {price ε : ℝ} {h C Ht H : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "R" => Z.placement
local notation "Y" => 2^Z.n
local notation "r" => Z.k-T.commonDepth
local notation "X" => Node Z.V (Z.V×Endpoint Y) (DescentCommonPalette.rotor Z.graph).Site
local notation "W" => reenter Z T
local notation "pal" => roster Z.graph r Ht
local notation "lab" => fun t=>shortName T.commonDepth (T.code t)
local notation "wires" => installedWireNames A T.home (R).input T.hub (funext (fun e=>(Z.allWidths e).symm)) Z.bank Z.tables
local notation "sock" => fun s c=>direct Z.graph s (linkSocket (R) lab T.commonDepth s c)

open DescentIssuedContactShape

open DescentContactSenderTicket

theorem good_sender_word {field : ℕ} (s : Bool) (c) (x : Fin 3→DescentSIMDLookup.Cell field)
    (own : (x 0).val=(DescentResetLocalRoster.rootId r Y (rootTicket Z T ((R).owner s (.inl c)))).val+1)
    (measured : (x 1).val=(R).reservedColumn T.commonDepth T.columns.host T.columns.near T.columns.size s c) :
    (sender Ht r Y x).val=(DescentResetLocalRoster.rootId r Y (rootTicket Z T ((R).owner s (.inl c)))).val*(Y+2^Ht)+
      contactSlotWord Z T s (.inl c)+1 := by
  cases s <;> apply good
  all_goals first | exact own | exact measured.trans (T.columns.read _ c).symm

theorem fallback_sender_word {field : ℕ} (s : Bool) (c) (x : Fin 3→DescentSIMDLookup.Cell field)
    (own : (x 0).val=(DescentResetLocalRoster.rootId r Y (rootTicket Z T ((R).owner s (.inr c)))).val+1)
    (measured : (x 1).val=DescentTreePrefixIntervals.start Ht
      (((R).fallbackBook s (fallEnd (R) s c)).codes (fallLeg (R) s c)))
    (depth : (x 2).val=((R).fallbackBook s (fallEnd (R) s c)).height) :
    (sender Ht r Y x).val=(DescentResetLocalRoster.rootId r Y (rootTicket Z T ((R).owner s (.inr c)))).val*(Y+2^Ht)+
      contactSlotWord Z T s (.inr c)+1 := by
  cases s <;> apply DescentContactSenderTicket.fallback
  all_goals first | exact T.bookHeight _ _ | exact own | exact measured | exact depth

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
