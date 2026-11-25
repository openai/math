import OAI.Computability.BorderVNP.CellPacketGeometrySignedFields
import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReports

/-! # Actual bit-major field report pins and opaque original-site pointers

The shared terminal frame computes the private and supplied extents and all
opaque source pointers. Transposing the two count-address pins makes digit
the outer physical loop, while the report directory still groups bits by
field value. The skipped owner has zero private wires and no reports.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.FiniteFields

open Crossing Packing Packing.Inherited FrozenTape CellSparse Packet CellAddresses CellAddressPhysical
open CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork FinalReports FiniteEvaluator
open private zero_value from OAI.Computability.BorderVNP.PackedWordCircuit
open RoutingISA
open scoped Classical BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 3500

variable {a m n C k w d entries : ℕ} {σ O : Type} [Fintype σ]

/-- Input pin of a scalar address in the shared digit-major address frame. -/
def transpose {g digits : ℕ} : Spare.Field C g digits (Fin entries) → Spare.Field C digits g (Fin entries)
  | .inl none => .inl none
  | .inl (some (.inl c)) => .inl (some (.inl c))
  | .inl (some (.inr (c,v,j))) => .inl (some (.inr (c,j,v)))
  | .inr i => .inr i

/-- The immutable private-wire pin of a physical owner, or the hole's literal zero. -/
abbrev priv (g digits : ℕ) : Fin (C+1) → Spare.Field C g digits (Fin entries) := Spare.priv

/-- One vector of little-endian count addresses per actual scalar ID; the hole has none. -/
abbrev rep (g digits : ℕ) : Fin (C+1) → List (List (Spare.Field C g digits (Fin entries))) := Spare.reports

/-- Native absolute pointer for the one-copy opaque description. -/
def pointerField (g digits : ℕ) (i : Fin entries) : Spare.Field C g digits (Fin entries) := .inr i

variable (F : Fields a m n C d k w σ) (boxes : Fin a → List (Source.Box O)) (entry : Fin entries → Fin a)
    (arena stride gap desc g digits : ℕ)

/-- The fully shared finite word frame, computing opaque pointers and
bit-major count addresses from the actual terminal geometry bank. -/
noncomputable def frame : Frame σ (Spare.Field C g digits (Fin entries) × Fin w) :=
  (SignedFields.frame F boxes entry arena stride gap desc digits g).select (fun p => (transpose p.1,p.2))

/-- The transposed bit selection costs no additional gates. -/
theorem frame_cubic (R W : ℕ) (rows : 1+CellAddressCircuit.count a m n C ≤ R) (originals : C+entries+1 ≤ R)
    (widths : d≤W ∧ k≤W ∧ w≤W ∧ Nat.clog 2 R≤W) :
    (frame F boxes entry arena stride gap desc g digits).size ≤
      8000*R*(W+1)^3+(C+C*digits*g)*w*(100*(w+1))+2 :=
  SignedFields.frame_cubic F boxes entry arena stride gap desc digits g R W rows originals widths

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (state : N.Site → Site)
    (sid : N.Site ↪ Fin a) (edges : N.Edge ↪ Fin m) (ports : P ↪ Fin n)
    {x : σ → Bool} (physical : Represents N cell (fun v => (state v).size) sid edges ports F x)
    (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c < 2^w)

/-- Numeric operand value decoded from the physically emitted word. -/
noncomputable def operand (p : Spare.Field C g digits (Fin entries)) :=
  value (fun b => (frame F boxes entry arena stride gap desc g digits).eval x (p,b))
local notation3 "args" => operand F boxes entry arena stride gap desc g digits (x:=x)
local notation3 "privateN" c => guessedSize N cell c+siteSize N cell c (fun v => (state v).size)
local notation3 "baseN" c => (privateN c)+suppliedSize N cell c

include physical sizeFit in
/-- The true private wire count from the terminal marker column. -/
theorem private_read (c : Fin C) : args ((priv g digits) c.castSucc)=privateN c := by
  simpa only [operand,priv,Spare.priv,Fin.lastCases_castSucc,frame,Frame.select_eval,transpose,SignedFields.frame_eval,
    Spare.fields_eval,Sum.elim_inl,Option.elim_some] using
    FinalReports.private_value (g:=digits) (digits:=g) N cell _ sid edges ports F physical sizeFit c

include physical sizeFit in
/-- The emitted count bit for scalar v at binary place j lives at true
private size plus supplied size plus j times the alphabet size plus v. -/
theorem address_read (c : Fin C) (v : Fin g) (j : Fin digits)
    (room : (baseN c)+j.val*g+v.val < 2^w) :
    args (.inl (some (.inr (c,v,j))))=(baseN c)+j.val*g+v.val := by
  simpa only [operand,frame,Frame.select_eval,transpose,SignedFields.frame_eval,Spare.fields_eval,Sum.elim_inl,Option.elim_some] using
    FinalReports.address_value N cell _ sid edges ports F physical sizeFit c j v room

include physical sizeFit in
/-- Every one-copy source pointer is the actual private-placement address
in its retained host's receiving arena. -/
theorem pointer_read (host : Fin entries → N.Site) (hosts : ∀ i, entry i=sid (host i))
    (old : ℕ → ℕ) (owners : ∀ i, old i.val=(cell (host i)).val) (hd : desc < 2^w)
    (room : ∀ c : Fin C, (∑ i : Fin entries, if cell (host i)=c then desc else 0) < 2^w)
    (i : Fin entries) (limit : arena+stride*(cell (host i)).val+suppliedSize N cell (cell (host i))+gap+
      PrivatePlacement.prefixCounts old desc i.val (cell (host i)).val < 2^w) :
    args (pointerField g digits i)=arena+stride*(cell (host i)).val+suppliedSize N cell (cell (host i))+gap+
      PrivatePlacement.prefixCounts old desc i.val (cell (host i)).val := by
  simpa only [operand,frame,Frame.select_eval,pointerField,transpose] using
    SignedFields.pointer_read F boxes entry arena stride gap desc digits g N cell state sid edges ports x physical sizeFit
      host hosts old owners hd room i limit

variable {cap h t : ℕ} {R B U V : Type} (S : Schema R B) (L : Schema U V)
    (sh : ∀ r, (S.tags r).length ≤ cap) (lh : ∀ r, (L.tags r).length ≤ cap)
    (sx : Pins R B h → Bool) (ly : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)
local notation3 "G₀" => History.directory S L boxes sh lh (priv g digits) (rep g digits) args sx ly cells off box

private theorem countPins_major {g digits : ℕ} (get : Spare.Field C g digits (Fin entries) → ℕ) (c : Fin C)
    (base : ℕ) (atBit : ∀ (v : Fin g) (j : Fin digits), get (.inl (some (.inr (c,v,j))))=base+j.val*g+v.val) :
    (countPins (g:=g) (digits:=digits) c).map (List.map fun p => get (.inl (some p)))=Reports.fields base g digits := by
  simp only [countPins,Reports.fields,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext v
  apply congrArg List.ofFn
  funext j
  have h := atBit v j
  simpa [Nat.mul_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

private theorem address_fit {base digits g bound : ℕ} (room : base+digits*g ≤ bound) (j : Fin digits) (v : Fin g) :
    base+j.val*g+v.val < bound := by
  have before := Nat.mul_le_mul_right g (show j.val+1 ≤ digits from j.isLt)
  rw [Nat.add_mul,Nat.one_mul] at before
  have pos := v.isLt
  omega

private theorem directory_from_fields (get : Spare.Field C g digits (Fin entries) → ℕ) (c : Fin C) (work base : ℕ)
    (privateWord : get ((priv g digits) c.castSucc)=work)
    (bits : ∀ (v : Fin g) (j : Fin digits), get (.inl (some (.inr (c,v,j))))=base+j.val*g+v.val) :
    let D := History.directory S L boxes sh lh (priv g digits) (rep g digits) get sx ly cells off box
    D.privateWires c.castSucc=work ∧ D.reports c.castSucc=Reports.fields base g digits := by
  intro D
  have given := Spare.directory_real (C:=C) (g:=g) (digits:=digits) (E:=Fin entries) S L boxes sh lh sx ly cells off box get c
  simp only [priv,Spare.priv,Fin.lastCases_castSucc] at privateWord
  exact ⟨given.1.trans privateWord,given.2.trans (countPins_major get c base bits)⟩

include physical sizeFit in
/-- Private width and bit-major report words in the real physical cell entry. -/
theorem directory_real (c : Fin C) (room : (baseN c)+digits*g ≤ 2^w) :
    (G₀).privateWires c.castSucc= (privateN c) ∧ (G₀).reports c.castSucc=Reports.fields (baseN c) g digits := by
  exact directory_from_fields boxes g digits S L sh lh sx ly cells off box args c (privateN c) (baseN c)
    (private_read F boxes entry arena stride gap desc g digits N cell state sid edges ports physical sizeFit c)
    (fun v j => address_read F boxes entry arena stride gap desc g digits N cell state sid edges ports physical sizeFit c v j
      (address_fit room j v))

/-- Native directory fields of the inactive sentinel. -/
theorem directory_hole :
    (G₀).privateWires (Fin.last C)=0 ∧ (G₀).reports (Fin.last C)=[] := by
  obtain ⟨size,empty⟩ := Spare.directory_spare S L boxes sh lh sx ly cells off box args
  refine ⟨size.trans ?_,empty⟩
  simp only [operand,frame,Frame.select_eval,transpose,SignedFields.frame_eval,Spare.fields_eval,Sum.elim_inl,Option.elim_none,zero_value]

/-- The exact sparse source volume, charging the opaque slot words, the
real cells' count addresses and one empty directory entry. -/
theorem sourceVolume_eq :
    History.sourceVolume S L boxes (rep (C:=C) (entries:=entries) g digits)=
      1+a+C+S.rows.length+History.tagWords S+L.rows.length+History.tagWords L+
      (C+C*g*digits+1+entries)+(∑ i, (boxes i).length)+(∑ i, (SiteWords.boxWords (boxes i)).length)+
      (C*(1+g*(1+digits))+1) := by
  simpa only [rep,Fintype.card_fin] using
    (Spare.sourceVolume_eq (C:=C) (g:=g) (digits:=digits) (E:=Fin entries) S L boxes)

end CellPacketGeometry.History.Native.FiniteFields

end BorderVNP
end Computability
end OAI
