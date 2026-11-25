import OAI.Hierarchy.DescentResetOrdinalSource
import OAI.Hierarchy.DescentDatedIssuedOperands

namespace OAI
/-! Only a fetched, nonzero contribution to an existing positive field needs a sum bound. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentPackedZip DescentSIMDLookup DescentOperandCandidateLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

theorem requestCandidate_some {n bits : ℕ} (q : Cell bits) (bounded : q.val≤n) (j : Fin n) :
    requestCandidate q bounded=some j ↔ q.val=j.val+1 :=by
  unfold requestCandidate
  split
  · rename_i zero
    simp [zero]
  · rename_i nonzero
    simp only [Option.some.injEq,Fin.ext_iff]
    omega

variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "C" => (v).setup
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "plan" => (v).linkedRankInputs u.sectors ((v).sheetsStart b)
local notation "rendered" => (v).renderFromRanks plan b
set_option hygiene false in
local notation "i" => (v).operandOrdinal (s) f arg x n
set_option hygiene false in
local notation "entry" => u.operandEntry ok m
set_option hygiene false in
local notation "pick" => fun h g=>requestCandidate (q h g) (bounded h g)

private theorem zero_source {H G M bits w : ℕ} (m : Memory w) :
    Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0 : Cell bits)) M m :=by
  intro p
  change 0=(((finFunctionFinEquiv (fun j : Fin M=>
    if _ : p.2.val*M+j.val<G then (0 : Cell bits) else 0)).val:ℕ):Word w)
  simp

/-- No ranked field enters columns three to six, even if the issued query was nonzero. -/
def OrdinalRead.ofKept
    (f : Fin 7) (arg : Fin (C).retained.args) (x : Fin (A).blocks) (n : Fin (C).retained.nodes)
    (ok : u.Ready) (m : Memory w) (small : 2*(A).candidates<2^(A).queryBits)
    (q : Fin (A).hosts→Fin (A).groups→Cell (A).queryBits)
    (kept : Fin (A).hosts→Fin (A).groups→Cell (s).coeff)
    (queryRead : Source ((s).query i) q (A).lanes entry)
    (keptRead : Source ((s).kept i) kept (A).lanes entry)
    (bounded : ∀h g,(q h g).val≤2*(A).candidates)
    (inert : 3≤f.val) : OrdinalRead u ok small m i :=by
  have noPointer : ResetOutput.pointerField f=none :=by
    fin_cases f <;> simp_all [ResetOutput.pointerField]
  refine ⟨pick,fun _ _ _=>0,kept,?_,keptRead,?_,?_⟩
  · simpa only [requestCandidate_code] using queryRead
  · intro j
    have index := (v).operandIndex_ordinal (s) f arg x n
    have neutral : (v).previous (s) rendered b i j = .lit 0 := by
      unfold ResetOutput.previous
      rw [index]
      simp only [noPointer, Option.elim_none]
    rw [neutral]
    exact zero_source entry
  · intro h g
    cases e : requestCandidate (q h g) (bounded h g) <;>
      simp [DescentOperandCandidateLookup.selected,e]

set_option hygiene false in
local notation "addend" j:arg h:arg g:arg => (((raw j h g).val : Cell (s).coeff).val)

/-- All seven returned pages, requiring arithmetic only for the three pointer projections
where a true requested value and the kept word are both positive. -/
def OrdinalRead.ofIssued
    (f : Fin 7) (arg : Fin (C).retained.args) (x : Fin (A).blocks) (n : Fin (C).retained.nodes)
    (ok : u.Ready) (m : Memory w) (small : 2*(A).candidates<2^(A).queryBits)
    (q : Fin (A).hosts→Fin (A).groups→Cell (A).queryBits)
    (kept : Fin (A).hosts→Fin (A).groups→Cell (s).coeff)
    (queryRead : Source ((s).query i) q (A).lanes entry)
    (keptRead : Source ((s).kept i) kept (A).lanes entry)
    (bounded : ∀h g,(q h g).val≤2*(A).candidates)
    (raw : Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Cell (A).signedBits)
    (fetched : ∀j, Source ((v).previous (s) rendered b i j) (raw j) (A).lanes entry)
    (both : f.val<3 → ∀h g j, (q h g).val=j.val+1 →
      0<(kept h g).val → 0<addend j h g → (kept h g).val+addend j h g<2^(s).coeff) :
    OrdinalRead u ok small m i :=by
  by_cases ptr : f.val<3
  · refine ⟨pick,raw,kept,?_,keptRead,fetched,?_⟩
    · simpa only [requestCandidate_code] using queryRead
    · intro h g
      cases chosen : requestCandidate (q h g) (bounded h g) with
      | none => simp [DescentOperandCandidateLookup.selected,chosen]
      | some j =>
        simp only [DescentOperandCandidateLookup.selected,chosen,Option.elim_some]
        have normal := (requestCandidate_some (q h g) (bounded h g) j).mp chosen
        by_cases old : (kept h g).val=0
        · simpa [old] using (((raw j h g).val : Cell (s).coeff)).isLt
        by_cases fresh : addend j h g=0
        · simp [fresh]
        exact both ptr h g j normal (Nat.pos_of_ne_zero old) (Nat.pos_of_ne_zero fresh)
  · exact OrdinalRead.ofKept u f arg x n ok m small q kept queryRead keptRead bounded (Nat.le_of_not_gt ptr)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
