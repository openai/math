import OAI.Hierarchy.DescentContactReceiver

namespace OAI
/-! # Both root and socket read from a directed contact's actual endpoint shape -/
namespace Hierarchy.DescentContactShapeRead
open DescentCommonHost DescentDenseHostOrder DescentContacts DescentChosenRouter DescentRelativeContacts
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {V : Type} {n h : ℕ} (G : NonlinearExpanders.Graph n h)
local notation "widthAt" => (2^n)
local notation "Q" => DescentCommonPalette.rotor G
local notation "Shape" => Node Unit (Unit×Endpoint widthAt) (Q).Site

abbrev Ticket (Y : ℕ) := (ℕ×ℕ) ⊕ ((ℕ×ℕ)×Option (Fin Y))

def ticket {r Y : ℕ} : DescentResetLocalRoster.Root r Y→Ticket Y
  | .inl k=>.inl k.val
  | .inr (k,tag)=>.inr (k.val,tag)

/-- The numerical leaf word is computed from the actual printed path in its own bit order. -/
def pathNumber (bits : List Bool) :=
  (DescentRotor.bitWord bits.length bits.get).val

theorem pathNumber_ofFn {d : ℕ} (bits : Fin d→Bool) :
    pathNumber (List.ofFn bits)=(DescentRotor.bitWord d bits).val := by
  let size : (List.ofFn bits).length=d:=List.length_ofFn
  have recode {a b : ℕ} (same : a=b) (v : Fin a→Bool) :
      (DescentRotor.bitWord a v).val=(DescentRotor.bitWord b (fun j=>v (Fin.cast same.symm j))).val := by
    subst b;rfl
  have same : (fun j=>(List.ofFn bits).get (Fin.cast size.symm j))=bits := by
    funext i
    simp
  exact (recode size (List.ofFn bits).get).trans (congrArg (fun b=>(DescentRotor.bitWord d b).val) same)

def «fields» (relativeDepth : ℕ) : Shape→Option (Ticket widthAt×ℕ)
  | .trunk _ _=>none
  | .good _ base cell=>some (.inl (relativeDepth,base.2),cell.1.val)
  | .fall _ z digits=>some (.inr z.2,widthAt+pathNumber digits)

def lookup (r height relativeDepth ordinal : ℕ) : Option (Ticket widthAt×ℕ) :=
  if has : ∃x : ↥(roster G r height),(localRank G r height x).val=ordinal then
    «fields» G relativeDepth has.choose.val else none

theorem lookup_read (r height depth : ℕ) (x : ↥(roster G r height)) :
    lookup G r height depth (localRank G r height x).val=«fields» G depth x.val := by
  have has : ∃y : ↥(roster G r height),(localRank G r height y).val=(localRank G r height x).val:=⟨x,rfl⟩
  have same:= (localRank G r height).injective (Fin.ext has.choose_spec)
  simp only [lookup,dite_eq_left has,same]

end
end Hierarchy.DescentContactShapeRead

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

def contactSlotWord (s : Bool) : (R).Contact→ℕ
  | .inl c=>((R).outputName T.commonDepth s c).2.val
  | .inr c=>Y+(DescentResetCableSlots.leaf (R) Ht T.bookHeight s (fallEnd (R) s c) (fallLeg (R) s c)).val

theorem direct_fields (s : Bool) (c : (R).Contact) :
    let g:=(R).owner s c
    «fields» Z.graph ((R).b (rootVertex Z T g)-T.commonDepth) (shape Z.graph (sock s c))=
      some (ticket (rootTicket Z T g),contactSlotWord Z T s c) := by
  cases c with
  | inl c=>cases s <;> rfl
  | inr c=>
    cases s <;> change some ((Sum.inr _ : Ticket Y),Y+pathNumber (List.ofFn _))=some ((Sum.inr _ : Ticket Y),Y+_)
    all_goals rw [pathNumber_ofFn]; rfl

theorem contact_shape_member (s : Bool) (c : (R).Contact) : shape Z.graph (sock s c)∈pal := by
  let e:=(wires).symm (.inr (.inr (.inl c)))
  have body:=contactFields Z T c
  cases s
  · have same : commonName Z T ((W).graph.src e)=sock false c:=congrArg DescentResetTrunks.RawFields.src body
    exact same ▸ (localShape Z T (placed Z T ((W).graph.src e))).property
  · have same : commonName Z T ((W).graph.dst e)=sock true c:=congrArg DescentResetTrunks.RawFields.dst body
    exact same ▸ (localShape Z T (placed Z T ((W).graph.dst e))).property

/-- The quotient discards the one absolute host numeral. Only the residue enters the short
    local table, even when the record is observed from the opposite endpoint. -/
theorem from_contact_header (s : Bool) (c : (R).Contact) :
    let g:=(R).owner s c
    let row:=codeHost Z T vertex (sock s c)
    lookup Z.graph r Ht ((R).b (rootVertex Z T g)-T.commonDepth) (row%(pal).card)=
      some (ticket (rootTicket Z T g),contactSlotWord Z T s c) := by
  let node:=sock s c
  let sh:↥pal:=⟨shape Z.graph node,contact_shape_member Z T s c⟩
  let digit:=localRank Z.graph r Ht sh
  have address : codeHost Z T vertex node=digit.val+(pal).card*(vertex (position Z.graph node)).val := by
    simp only [codeHost, contact_shape_member Z T s c, dite_eq_left, node]
    rfl
  change lookup _ _ _ _ (_%_)=_
  rw [address,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt digit.isLt]
  exact (lookup_read Z.graph r Ht _ sh).trans (direct_fields Z T s c)

theorem direct_header_word (s : Bool) (c : (R).Contact) :
    let e:=(wires).symm (.inr (.inr (.inl c)))
    actualRecord Z T vertex e (if s then 2 else 1)=codeHost Z T vertex (sock s c) := by
  let e:=(wires).symm (.inr (.inr (.inl c)))
  have body:=contactFields Z T c
  cases s
  · have same : commonName Z T ((W).graph.src e)=sock false c:=congrArg DescentResetTrunks.RawFields.src body
    exact (codeHost_at Z T vertex ((W).graph.src e)).symm.trans (congrArg (codeHost Z T vertex) same)
  · have same : commonName Z T ((W).graph.dst e)=sock true c:=congrArg DescentResetTrunks.RawFields.dst body
    exact (codeHost_at Z T vertex ((W).graph.dst e)).symm.trans (congrArg (codeHost Z T vertex) same)

theorem from_actual_contact (s : Bool) (c : (R).Contact) :
    let g:=(R).owner s c
    let e:=(wires).symm (.inr (.inr (.inl c)))
    let row:=actualRecord Z T vertex e (if s then 2 else 1)
    lookup Z.graph r Ht ((R).b (rootVertex Z T g)-T.commonDepth) (row%(pal).card)=
      some (ticket (rootTicket Z T g),contactSlotWord Z T s c) := by
  dsimp only
  rw [direct_header_word Z T vertex s c]
  exact from_contact_header Z T vertex s c

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
