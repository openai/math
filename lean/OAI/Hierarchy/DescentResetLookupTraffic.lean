import OAI.Hierarchy.DescentNamedSheetReturnBill
import OAI.Hierarchy.DescentResetPrimitiveReceivedVolume

namespace OAI
/-! The shared operand dictionaries and per-row lookups in the reset sheet return. -/
namespace Hierarchy
open DescentSIMDLookup DescentOperandFamilyBook DescentResetCandidatePair
noncomputable section
set_option quotPrecheck false
namespace DescentResetCandidatePair
def scanFactor (J U : ℕ) := 120*(J+1)*(U+1)
theorem scan_area (J rows U T : ℕ) (cap : rows≤T) (pos : 0<T) : scanBill J rows U≤ scanFactor J U*T:=by
  calc
    _≤4+J*(4+T*(2*U+4))+7*(15+J*(11+4*U)):=by unfold scanBill;gcongr
    _≤_:=by
      unfold scanFactor
      obtain ⟨d,rfl⟩:=Nat.exists_eq_succ_of_ne_zero pos.ne'
      rw [Nat.succ_eq_add_one]
      ring_nf
      omega
end DescentResetCandidatePair
namespace DescentOperandFamilyBook
theorem dict_area (n N T : ℕ) (count : n≤N*T) (pos : 0<T) : dictionaryCharge n≤120*(N+1)*T:=by
  unfold dictionaryCharge
  have times:=Nat.mul_le_mul_left 115 count
  ring_nf at times ⊢
  omega

theorem family_area (K n a M h T : ℕ) (size : unit n a*M≤h/2) (stock : 2^(h/2)≤T) (pos : 0<T) :
    dictionaryCharge (words K n a M)≤120*(2*(n+K)+1)*T:=by
  apply dict_area _ _ _ _ pos
  have page:2^(unit n a*M)≤T:=(Nat.pow_le_pow_right (by decide) size).trans stock
  unfold words
  calc
    _≤(n+K)*(2*T):=by gcongr
    _=_:=by ring
end DescentOperandFamilyBook
namespace DescentResetOperandSetup.Chart
variable (C : DescentResetOperandSetup.Chart)
def tableFactor :=
  120*(7+(2*C.inputs+1)+(2*(C.inputs+1)+1)+(2*(C.inputs+2)+1)+11+
    (2*(4+C.members)+1)+(2*(4+7*C.members)+1)+
    (2*(C.fallbackInputs+C.members)+1)+(2*(C.fallbackInputs+7*C.members)+1))

theorem table_volume (h T : ℕ) (stock : 2^(h/2)≤T)
    (public_ : C.publicCasts.bound*C.publicCasts.lanes≤h/2) (old : C.sourceWidth*C.lanes≤h/2)
    (carry : unit C.inputs C.fieldBits*C.lanes≤h/2) (slices : (C.fieldBits+2)*C.lanes≤h/2)
    (private_ : unit 4 C.rotorBits*C.lanes≤h/2) (surface : unit C.fallbackInputs C.fallbackBits*C.lanes≤h/2) :
    C.tableInvoice≤C.tableFactor*T:=by
  have positive:0<T:=(Nat.two_pow_pos _).trans_le stock
  have pow_ (b) (lim : b≤h/2) : 2^b≤T:=(Nat.pow_le_pow_right (by decide) lim).trans stock
  have p:=dict_area C.publicCasts.words 6 T (by
    unfold DescentOperandPublicCasts.Plan.words
    calc _≤3*(2*T):=by gcongr;exact pow_ _ public_
         _=_:=by ring) positive
  have o:=dict_area (DescentOperandInputCast.words C.inputs C.sourceWidth C.lanes) (2*C.inputs) T (by
    unfold DescentOperandInputCast.words
    calc _≤C.inputs*(2*T):=by gcongr;exact pow_ _ old
         _=_:=by ring) positive
  have s:=dict_area (10*2^((C.fieldBits+2)*C.lanes)) 10 T (Nat.mul_le_mul_left 10 (pow_ _ slices)) positive
  have a:=family_area 1 C.inputs C.fieldBits C.lanes h T carry stock positive
  have b:=family_area 2 C.inputs C.fieldBits C.lanes h T carry stock positive
  have c:=family_area C.members 4 C.rotorBits C.lanes h T private_ stock positive
  have d:=family_area (7*C.members) 4 C.rotorBits C.lanes h T private_ stock positive
  have e:=family_area C.members C.fallbackInputs C.fallbackBits C.lanes h T surface stock positive
  have f:=family_area (7*C.members) C.fallbackInputs C.fallbackBits C.lanes h T surface stock positive
  have same (K n a M : ℕ) : words K n a M = DescentOperandFamilyBook.words K n a M := rfl
  unfold tableInvoice tableFactor
  simp only [same]
  ring_nf at p o s a b c d e f ⊢
  omega
end DescentResetOperandSetup.Chart
namespace DescentDatedAddressBook.ResetOutput
open DescentResetRankedWindows DescentOperandCandidateLookup DescentResetFieldAssembler
variable (v : ResetOutput)
local notation "a" => v.receiver
local notation "c" => v.setup

/-- The row and table expenses apart from reindexing and moving original packets. -/
def sheetLookups (candidates header : ℕ) :=
  let n:=(a).hosts*chunks (a).groups (a).lanes
  let U:=(c).selectorWork
  scanBill ((a).blocks*candidates) n header+scanBill ((a).blocks*candidates) n 7+
    v.portBill+dictionaryCharge v.keepWords+v.pointerBill U (U+12)+
    DescentResetNodeBooks.invoice v.nodeNames v.nodes (a).hosts (a).groups v.nodeBits (a).lanes+(c).tableInvoice

def lookupFactor (header : ℕ) :=
  let U:=(c).selectorWork
  scanFactor ((a).blocks*(a).candidates) header+scanFactor ((a).blocks*(a).candidates) 7+12000+
    120*3+(120*(4*(a).candidates+1)+scanFactor (a).fields (visit U (U+12) 7 (Layout.finalWork (a).candidates 7) (a).candidates))+
    (120*(v.nodes+2)+scanFactor v.nodeNames (1+v.nodes*18))+(c).tableFactor

structure LookupLimits (header bound : ℕ) : Prop where
  inputs : (c).inputs≤bound
  members : (c).members≤bound
  fallback : (c).fallbackInputs≤bound
  nodes : v.nodes≤bound
  nodePages : v.nodeNames≤bound
  channels : (a).fields≤bound
  candidates : (a).candidates≤bound
  blocks : (a).blocks≤bound
  headers : header≤bound

theorem lookup_volume (h T header : ℕ) (stock : 2^(h/2)≤T)
    (hosts : v.sheets.hosts≤T) (rows : v.sheets.hosts*chunks v.sheets.groups v.sheets.lanes≤T)
    (receiver : (a).hosts*chunks (a).groups (a).lanes≤T)
    (cast : (c).fieldBits*(a).lanes≤h/2) (raw : ((a).queryBits+(a).signedBits)*(a).lanes≤h/2)
    (nodes : (v.nodeBits*v.nodes+v.nodeBits)*(a).lanes≤h/2) (tables : (c).tableInvoice≤(c).tableFactor*T) :
    v.sheetLookups (a).candidates header≤v.lookupFactor header*T:=by
  have pos:0<T:=(Nat.two_pow_pos _).trans_le stock
  have pow_ (b) (lim : b≤h/2) : 2^b≤T:=(Nat.pow_le_pow_right (by decide) lim).trans stock
  have left:=scan_area ((a).blocks*(a).candidates) _ header T receiver pos
  have right:=scan_area ((a).blocks*(a).candidates) _ 7 T receiver pos
  have port : v.portBill≤12000*T:=by
    unfold portBill DescentScalarHaloPortROM.length
    omega
  have kept:=dict_area v.keepWords 2 T (by
    change 1*(2*2^((c).fieldBits*(a).lanes))≤2*T
    simpa only [Nat.one_mul] using Nat.mul_le_mul_left 2 (pow_ _ cast)) pos
  have ptr:=dict_area v.finalWords (4*(a).candidates) T (by
    unfold finalWords bits
    calc _≤(2*(a).candidates*2)*T:=Nat.mul_le_mul_left _ (pow_ _ raw)
         _=_:=by ring) pos
  let U:=(c).selectorWork
  have visited:=scan_area (a).fields _ (visit U (U+12) 7 (Layout.finalWork (a).candidates 7) (a).candidates) T receiver pos
  have node:=dict_area (DescentResetNodeBooks.volume v.nodes v.nodeBits (a).lanes) (v.nodes+1) T
    (Nat.mul_le_mul_left _ (pow_ _ nodes)) pos
  have write:=scan_area v.nodeNames _ (1+v.nodes*18) T receiver pos
  dsimp only [U] at visited
  rw [show v.nodes+1+1=v.nodes+2 by omega] at node
  unfold sheetLookups lookupFactor pointerBill DescentResetNodeBooks.invoice
  unfold dictionaryCharge at kept ptr node ⊢
  simp only [DescentResetNodeBooks.rows,Nat.add_mul]
  omega

end DescentDatedAddressBook.ResetOutput
end
end Hierarchy

end OAI
