import OAI.Hierarchy.DescentOperandStateBanks
import OAI.Hierarchy.DescentPackedOperand
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Turning a real resolved operand and first-use priorAlias into the next date's short pointer -/
namespace Hierarchy.DescentOperandStateBanks
open DescentSIMDLookup DescentPackedOperand ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- Consecutive lanes in a retained p-word are described independently of the
cable or private word to which they refer. -/
structure Span where
  start : ℕ
  stride : ℕ
  count : ℕ

/-- The three classes of references read by the next receiver. The private tag
covers both newly captured cables and the donor's inherited private words. -/
inductive Pointer where
  | privateWord (priorAlias : ℕ)
  | cable (peer serial chunk : ℕ)
  | pin (port chunk : ℕ)
  deriving DecidableEq

def Pointer.header : Pointer → Fin 4 → ℕ
  | .privateWord priorAlias => ![0,0,priorAlias,0]
  | .cable peer serial chunk => ![1,peer,serial,chunk]
  | .pin port chunk => ![2,0,port,chunk]

def Pointer.fields (p : Pointer) (range : Span) : Field → ℕ :=
  fun j => if live : j.val<4 then p.header ⟨j.val,live⟩ else
    if j.val=4 then range.start else if j.val=5 then range.stride else range.count

def Pointer.ofKey (priorAlias : ℕ) : Key → Pointer
  | .carried _ _ | .first _ _ _ _ | .second _ _ _ _ => .privateWord priorAlias
  | .cable peer name chunk => .cable peer name chunk
  | .pin name chunk => .pin name chunk

/-- The existing private renamer stores the least occurrence plus one. The
prior operand for the next stage uses the zero-based occurrence. -/
def component (tag peer name chunk priorAlias : ℕ) (f : Fin 4) :=
  if tag=3 then Pointer.header (.cable peer name chunk) f
  else if tag=4 then Pointer.header (.pin name chunk) f
  else Pointer.header (.privateWord (priorAlias-1)) f

theorem component_key (x : Key) (priorAlias : ℕ) (f : Fin 4) :
    component (x.fields 0) (x.fields 2) (x.fields 3) (x.fields 4) priorAlias f =
      (Pointer.ofKey (priorAlias-1) x).header f := by
  cases x <;> rfl

/-- This two-input native lookup examines only one argument and its authenticated
first-occurrence digit. Arbitrary bit patterns wrap inside the output cell. -/
def stateTable (k b coeff : ℕ) (f : Fin 4) (key : Cell (outputWidth k)) (priorAlias : Cell b) : Cell coeff :=
  let field (j : ℕ) := digit (k+4) j key.val
  ⟨component (field 0) (field 2) (field 3) (field 4) priorAlias.val f % 2^coeff,
    Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem stateTable_zero (k b coeff : ℕ) (f : Fin 4) : stateTable k b coeff f 0 0=0 := by
  apply Fin.ext
  fin_cases f <;> simp [stateTable,digit,component,Pointer.header]

theorem stateTable_key {k b coeff : ℕ} (x : Fragment k) (priorAlias : Cell b) (f : Fin 4)
    (room : ((Pointer.ofKey (priorAlias.val-1) (resolve x)).header f)<2^coeff) :
    (stateTable k b coeff f (word x) priorAlias).val=(Pointer.ofKey (priorAlias.val-1) (resolve x)).header f := by
  have digitAt (j : Fin 5) := word_read x j
  have tag : digit (k+4) 0 (word x).val=(resolve x).fields 0 :=digitAt 0
  have peer : digit (k+4) 2 (word x).val=(resolve x).fields 2 :=digitAt 2
  have serial : digit (k+4) 3 (word x).val=(resolve x).fields 3 :=digitAt 3
  have chunk : digit (k+4) 4 (word x).val=(resolve x).fields 4 :=digitAt 4
  change component (digit (k+4) 0 _) (digit (k+4) 2 _) (digit (k+4) 3 _)
    (digit (k+4) 4 _) _ _ % _=_
  rw [tag,peer,serial,chunk,component_key,Nat.mod_eq_of_lt room]

variable {k b coeff hosts groups M w : ℕ}

/-- Four pages are computed from the actually occupied argument and priorAlias arrays.
Later pages for start, stride and count can be copied directly alongside them. -/
theorem field_run (tables : DescentPackedZip.Tables) (key priorAlias : Bank) (out : ℕ) (f : Fin 4)
    (room : DescentPackedZip.Fits tables (.lookup key .row) (.lookup priorAlias .row)
      (outputWidth k) b M out w)
    (space : out+hosts*chunks groups M<2^w) (m : Memory w)
    (keys : Fin hosts→Fin groups→Cell (outputWidth k)) (aliases : Fin hosts→Fin groups→Cell b)
    (keyCap : hosts*chunks groups M≤key.size) (aliasCap : hosts*chunks groups M≤priorAlias.size)
    (keyRead : ∀i : Row hosts groups M,m (key.base+(row hosts groups M i).val)=((data keys i).val:Word w))
    (aliasRead : ∀i : Row hosts groups M,m (priorAlias.base+(row hosts groups M i).val)=((data aliases i).val:Word w))
    (dictionary : DescentPackedZip.Static tables (stateTable k b coeff f) M m) :
    let step := tables.read (.lookup key .row) (.lookup priorAlias .row)
    let after := image out (hosts*chunks groups M) step m
    (scan w out (hosts*chunks groups M) step).Exec m after (4+54*(hosts*chunks groups M)) ∧
    (∀p : Row hosts groups M,after (out+(row hosts groups M p).val)=
      ((data (fun h g=>stateTable k b coeff f (keys h g) (aliases h g)) p).val:Word w)) ∧
    (∀i,i<out ∨ out+hosts*chunks groups M ≤ i → after i=m i) ∧
    CheapCode (scan w out (hosts*chunks groups M) step) := by
  intro step after
  have bound : step.Fits w out := by
    simp [step,DescentPackedZip.Tables.read,Expr.Fits,room.apply,room.shift,room.left.1,room.right.1]
  have got := DescentPackedZip.read_data tables (.lookup key .row) (.lookup priorAlias .row) out room
    (stateTable k b coeff f) (stateTable_zero k b coeff f) m dictionary keys aliases
    (DescentPackedZip.source_column key out room.left.1 m keys keyCap keyRead)
    (DescentPackedZip.source_column priorAlias out room.right.1 m aliases aliasCap aliasRead)
  refine ⟨?_,fun p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row hosts groups M p)).trans (got p),
    fun i hi=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ hi,scan_cheap w _ _ _⟩
  rw [show 4+54*(hosts*chunks groups M)=4+(hosts*chunks groups M)*(2*step.work+4) by
    change 4+54*(hosts*chunks groups M)=4+hosts*chunks groups M*(2*25+4);omega]
  intro P R C machine
  exact scan_exec out _ step m bound space machine

end
end Hierarchy.DescentOperandStateBanks

end OAI
