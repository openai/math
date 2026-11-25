import OAI.Hierarchy.DescentContactShapeRead

namespace OAI
/-! # Emit a real public-contact socket and root in a bounded preceding shape column -/
namespace Hierarchy.DescentIssuedContactShape
open DescentResetLocalRoster DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image DescentIssuedGoodHeaders
open DescentPacking.PackedMatch.Local.Gather DescentSharedCableNames DescentContactShapeRead
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {n h H G M w field : ℕ} (board : NonlinearExpanders.Graph n h)

def bound (Ht r Y : ℕ) := rootSlots r Y*(Y+2^Ht)

theorem ticket_injective {r Y : ℕ} : Function.Injective (ticket (r:=r) (Y:=Y)) := by
  rintro (a|⟨a,i⟩) (b|⟨b,j⟩) eqn
  · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj eqn))
  · cases eqn
  · cases eqn
  · have same:=Sum.inr.inj eqn
    exact congrArg Sum.inr (Prod.ext (Subtype.ext (congrArg Prod.fst same)) (congrArg (fun v : (ℕ×ℕ)×Option (Fin Y)=>v.2) same))

def compact (Ht r Y : ℕ) (v : Ticket Y×ℕ) : Option (Fin (bound Ht r Y)) :=
  if live : ∃q : Root r Y,ticket q=v.1 then
    if tail : v.2<Y+2^Ht then some (finProdFinEquiv (rootId r Y live.choose,⟨v.2,tail⟩))
    else none
  else none

theorem compact_read {Ht r Y : ℕ} (q : Root r Y) (z : Fin (Y+2^Ht)) :
    compact Ht r Y (ticket q,z.val)=some (finProdFinEquiv (rootId r Y q,z)) := by
  have live : ∃v : Root r Y,ticket v=ticket q:=⟨q,rfl⟩
  have same:=ticket_injective live.choose_spec
  simp only [compact,dite_eq_left live,dite_eq_left z.isLt,same]
  rfl

def panel (Ht r : ℕ) (x : Fin 2→Cell field) : Cell (Packed.bits (bound Ht r (2^n))) :=
  Packed.token ((lookup board r Ht (x 0).val (x 1).val).bind (compact Ht r (2^n)))

theorem issue (Ht r : ℕ)
    (tables : Fin 2→Tables) (reads : Fin 2→Expr) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (x : Fin H→Fin G→Fin 2→Cell field) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*2) (Packed.bits (bound Ht r (2^n))) M H G w out.base)
    (rom : resident (panel board Ht r ∘ (encode field 2).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*2)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (outputRoom : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>panel board Ht r (x a g)) M dst ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out.base ∨ out.base+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,whole,_,frame⟩:=gathered_words (panel board Ht r) tables reads menu mid out.base
    x pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ outputRoom whole,frame⟩

end
end Hierarchy.DescentIssuedContactShape

namespace Hierarchy.DescentSixParty.ResetInput
open DescentChosenRouter DescentCommonHost DescentDenseHostOrder DescentContacts DescentContactReceiver DescentRelativeContacts
open DescentResetTrunks DescentResetAttachments DescentContactShapeRead
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bw : P→ℕ} {A : MarkedWorld F d P bw}
    {price ε : ℝ} {h C Ht H : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z) (vertex : Z.V↪Fin H)
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

theorem contactSlotWord_lt (s : Bool) (c : (R).Contact) : contactSlotWord Z T s c<Y+2^Ht := by
  cases c with
  | inl c=>exact lt_of_lt_of_le ((R).outputName T.commonDepth s c).2.isLt (Nat.le_add_right ..)
  | inr c=>exact Nat.add_lt_add_left ((DescentResetCableSlots.leaf (R) Ht T.bookHeight s (fallEnd (R) s c)) (fallLeg (R) s c)).isLt _

theorem contact_shape_word {field : ℕ} (s : Bool) (c : (R).Contact) (x : Fin 2→DescentSIMDLookup.Cell field)
    (own : (x 0).val=(R).b (rootVertex Z T ((R).owner s c))-T.commonDepth)
    (slot : (x 1).val=codeHost Z T vertex (sock s c)%(pal).card) :
    (panel Z.graph Ht r x).val=
      (DescentResetLocalRoster.rootId r Y (rootTicket Z T ((R).owner s c))).val*(Y+2^Ht)+contactSlotWord Z T s c+1 := by
  let z : Fin (Y+2^Ht):=⟨_,contactSlotWord_lt Z T s c⟩
  rw [panel,own,slot,from_contact_header,Option.bind_some]
  have recode:=compact_read (Ht:=Ht) (rootTicket Z T ((R).owner s c)) z
  rw [recode]
  simp [DescentSharedCableNames.Packed.token,finProdFinEquiv_apply_val,z,Nat.add_comm,Nat.mul_comm]

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
