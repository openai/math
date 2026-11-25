import OAI.Hierarchy.DescentRegisteredOperandFields
import OAI.Hierarchy.DescentTicketFragment
import OAI.Hierarchy.DescentPriorOperandColumns
import OAI.Hierarchy.DescentPackedOperandFields
import OAI.Hierarchy.DescentOperandStateCodec

namespace OAI
/-! # Measured retained operand headers at the next ten-column resolver -/
namespace Hierarchy.DescentPriorOperandColumns
open DescentSIMDLookup DescentPackedColony DescentPackedOperand DescentOperandStateBanks
open DescentOrdinaryAtomFieldRAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {P K k H G M w slots : ℕ}

theorem header_value (t : Side k) (p : Pointer) (fit : ∀f,p.header f<2^(k+2)) (f : Fin 4) :
    (sourceFields (t.withHeader p fit) (headerIndex f)).val=p.header f := by
  cases p <;> fin_cases f <;> rfl

theorem exterior (t : Side k) (stamp chunk : ℕ) (fit : ∀f,(Pointer.pin stamp chunk).header f<2^(k+2)) :
    resolve (t.withHeader (.pin stamp chunk) fit)=.pin stamp chunk := rfl

theorem carried (t : Side k) («alias» : ℕ) (fit : ∀f,(Pointer.privateWord «alias»).header f<2^(k+2)) :
    resolve (t.withHeader (.privateWord «alias») fit)=.carried t.donor.val «alias» := rfl

def fields (header : Fin 4→Bank) (side : Fin 6→Bank) : Fin 10→Bank :=
  ![header 0,side 0,header 1,header 2,header 3,side 1,side 2,side 3,side 4,side 5]

def selectedLayout (H G M : ℕ) (out : ℕ) (arg : Fin slots) (j : Fin K) (side : Fin 6→Bank) (rest : Layout) : Layout :=
  {rest with field:=fields (fun f=>fieldBank out (H*chunks G M) (pageOf arg f) j) side}

variable (old : Pages slots→Bank) (base out : ℕ) (m : Memory w)
    (books : Pages slots→Fin H→Fin G→Cell ((k+2)*K))
local notation "nr" => H*chunks G M
local notation "after_" => image old (k+2) K M nr base out m

/-- Genuine unchanged side fields are combined with the four native scalar
columns. The compiler's ten-field readback uses the original exterior stamp. -/
theorem measured_fields (arg : Fin slots) (node : Fin K) (ports : Fin H→Fin G→Pointer)
    (route : Fin H→Fin G→Side k) (sizes : ∀h g f,(ports h g).header f<2^(k+2))
    (side : Fin 6→Bank) (rest : Layout) (low : ∀p,(old p).Fits w base)
    (capacity : ∀p,nr≤(old p).size) (apart : base+K*2^(((k+2)*K)*M)≤out)
    (room : out+((7*slots)*K)*nr<2^w) (prior : ∀p,Reads (old p) (books p) M m)
    (header : ∀f h g,(ScalarOperand.take node (books (pageOf arg f) h g)).val=(ports h g).header f)
    (sideLow : ∀i,(side i).base+nr≤base)
    (sides : ∀i,Reads (side i) (fun h g=>sourceFields ((route h g).withHeader (ports h g) (sizes h g)) (sideIndex i)) M m) :
    let x:=fun h g=>(route h g).withHeader (ports h g) (sizes h g)
    let L:=selectedLayout H G M out arg node side rest
    ∀i,Reads (L.field i) (fun h g=>sourceFields (x h g) i) M after_ := by
  intro x L
  obtain ⟨_,emitted,frame,_⟩:=run old base out m books low capacity apart room prior
  have head (f : Fin 4) : Reads (fieldBank out nr (pageOf arg f) node) (fun h g=>sourceFields (x h g) (headerIndex f)) M after_ := by
    have eqn : (fun h g=>ScalarOperand.take node (books (pageOf arg f) h g)) = (fun h g=>sourceFields (x h g) (headerIndex f)) := by
      funext h g;apply Fin.ext;exact (header f h g).trans (header_value (route h g) (ports h g) (sizes h g) f).symm
    simpa only [eqn] using emitted (pageOf arg f) node
  have tail (i : Fin 6) : Reads (side i) (fun h g=>sourceFields (x h g) (sideIndex i)) M after_ := by
    intro p
    have h : (side i).base+(row H G M p).val<base:=(Nat.add_lt_add_left (row H G M p).isLt _).trans_le (sideLow i)
    exact (frame _ (.inl h) (.inl (h.trans_le ((Nat.le_add_right ..).trans apart)))).trans (sides i p)
  intro i
  fin_cases i
  · exact head 0
  · exact tail 0
  · exact head 1
  · exact head 2
  · exact head 3
  · exact tail 1
  · exact tail 2
  · exact tail 3
  · exact tail 4
  · exact tail 5

/-- An already initialized finite resolver keeps its actual join pages and
short-key dictionary while the retained field extraction runs. -/
theorem installed_after {w H G M k : ℕ} (L : Layout) (x : Fin H→Fin G→Fragment k)
    (before after : Memory w) (base : ℕ) (stable : ∀a,a<base→after a=before a)
    (fields_ : ∀i,Reads (L.field i) (fun h g=>sourceFields (x h g) i) M after)
    (joinRead : ∀i,DescentPackedZip.Static (L.joins i) (DescentPacking.PackedMatch.Local.Gather.setField (d:=k+2) i) M before)
    (shiftEnd : ∀i,(L.joins i).shift.base+2^(((k+2)*10)*M)≤base)
    (joinEnd : ∀i,(L.joins i).apply.base+2^(((k+2)*10+(k+2))*M)≤base)
    (staticEnd : ∀j : Cell (inputWidth k*M)⊕Fin (H*chunks G M),fixedAddr L.remap j<base)
    (dictionary : ∀j : Cell (inputWidth k*M)⊕Fin (H*chunks G M),
      before (fixedAddr L.remap j)=fixedWord (M:=M) (H:=H) (r:=G) (transition k) j) : Installed L x M after := by
  refine ⟨fields_,?_,?_⟩
  · intro i
    constructor
    · intro j
      exact (stable _ ((Nat.add_lt_add_left j.isLt _).trans_le (shiftEnd i))).trans ((joinRead i).1 j)
    · intro j
      exact (stable _ ((Nat.add_lt_add_left j.isLt _).trans_le (joinEnd i))).trans ((joinRead i).2 j)
  · intro j;exact (stable _ (staticEnd j)).trans (dictionary j)

end
end Hierarchy.DescentPriorOperandColumns

end OAI
