import OAI.Hierarchy.ProtocolRAMHistogram
import OAI.Hierarchy.ProbeCatalogue
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Addressing the certified packet catalogue by a rounded local price vector -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open ThreeFlat.Diagonal.MotifOuterTerms
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Fin.CommRing BigOperators Classical

variable {w radix d : ℕ}

theorem eval_menuKey (m : Memory w) (r : Word w) (xs : Fin d → Expr) (v : Fin d → Fin radix)
    (digits : ∀ i, (xs i).eval m r = ((v i).val : Word w)) :
    (menuKey radix (List.ofFn xs)).eval m r = ((finFunctionFinEquiv v).val : Word w) := by
  induction d with
  | zero => simp [menuKey,Expr.eval]
  | succ d ih =>
    rw [List.ofFn_succ,menuKey,Expr.eval,eval_scale,digits,
      ih (fun i => xs i.succ) (fun i => v i.succ) (fun i => digits i.succ)]
    simp only [RowOp.opcode,BinaryOp.eval,←Nat.cast_mul,←Nat.cast_add]
    apply congrArg (fun z : ℕ => (z : Word w))
    rw [finFunctionFinEquiv_apply,finFunctionFinEquiv_apply,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Exactly radix^d words of immutable advice describe the recommendation on every
rounded quote vector. The number of coordinates d is the bounded local format. -/
def menuAdvice (table : Bank) (code : (Fin d → Fin radix) → ℕ) (m : Memory w) : Memory w :=
  fillSegment table.base (radix^d) (fun a =>
    if h : a-table.base < radix^d then (code (finFunctionFinEquiv.symm ⟨a-table.base,h⟩) : Word w)
    else 0) m

theorem read_menuAdvice (table : Bank) (code : (Fin d → Fin radix) → ℕ) (m : Memory w)
    (v : Fin d → Fin radix) (room : radix^d ≤ 2^w) (capacity : radix^d ≤ table.size) :
    table.read (menuAdvice table code m) ((finFunctionFinEquiv v).val : Word w) = (code v : Word w) := by
  let p := finFunctionFinEquiv v
  have val : p.val < radix^d := p.isLt
  change table.read (menuAdvice table code m) (p.val : Word w) = _
  have inside : table.base ≤ table.base+p.val ∧ table.base+p.val < table.base+radix^d := by omega
  simp only [Bank.read,Fin.val_cast_of_lt (val.trans_le room),Nat.mod_eq_of_lt (val.trans_le capacity),
    menuAdvice,fillSegment,ite_eq_left inside,Nat.add_sub_cancel_left,dite_eq_left val]
  exact congrArg (fun z=>(code z:Word w)) (finFunctionFinEquiv.symm_apply_apply v)

theorem menu_lookup_word (table : Bank) (code : (Fin d → Fin radix) → ℕ) (m : Memory w)
    (r : Word w) (xs : Fin d → Expr) (v : Fin d → Fin radix) (room : radix^d≤2^w)
    (capacity : radix^d≤table.size)
    (quoted : ∀ i, (xs i).eval (menuAdvice table code m) r = ((v i).val:Word w)) :
    (menuLookup table radix (List.ofFn xs)).eval (menuAdvice table code m) r = (code v:Word w) := by
  simp only [menuLookup,Expr.eval,eval_menuKey _ _ _ _ quoted,read_menuAdvice table code m v room capacity]

/-- Code zero is reserved for passing tests. Positive codes identify actual packets
from the finite discrepancy catalogue. Every selected packet has positive demand
stocks and the common saving for every admissible histogram. -/
theorem certified_codes {k : ℕ} {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
    [Nonempty (Fin k)] (edge : E → Chord k) (req : A → E) (conn : Probe.Connected edge)
    (P : Set (E → ℝ)) (compact : IsCompact P) (nonneg : ∀ p∈P, ∀ e, 0≤p e)
    {ε : ℝ} (pos : 0<ε) (tree : ℝ) (treePos : 0≤tree) (N : ℕ)
    (price : (Fin d → Fin radix) → E → ℝ) (legal : ∀ x, price x ∈ P) :
    let X := {p : E → ℝ // p ∈ P ∧ ε ≤ Probe.discrepancy F edge req p}
    ∃ (S : Finset X) (pkt : (j : S) → Probe.Packet F edge
      (fun a : Probe.PositiveDemand req j.val.val => req a.val)) (γ : ℝ)
      (code : (Fin d → Fin radix) → ℕ), 0<γ ∧ (∀ j,N<(pkt j).width) ∧
      (∀ x, code x=0 ↔ Probe.discrepancy F edge req (price x)<ε) ∧
      ∀ x, ε≤Probe.discrepancy F edge req (price x) → ∃ j : S,
        code x = (Fintype.equivFin S j).val+1 ∧
        (∀ a : Probe.PositiveDemand req j.val.val, γ ≤ price x (req a.val)) ∧
        ∀ t (h : Histogram (Fin (pkt j).terms) t),
          (∑ e, (histWidth (pkt j).count h e : ℝ)*price x e) + t*(tree*(pkt j).selectorBits) ≤
          t*((pkt j).width*((∑ a : Probe.PositiveDemand req j.val.val, price x (req a.val))-γ)) := by
  classical
  obtain ⟨S,pkt,γ,positive,wide,choose⟩ := Probe.discrepancy_catalogue
    (F:=F) edge req conn P compact nonneg pos tree treePos N
  let code (x : Fin d → Fin radix) : ℕ :=
    if h : ε ≤ Probe.discrepancy F edge req (price x) then
      (Fintype.equivFin S ((choose ⟨price x,legal x,h⟩).choose)).val+1 else 0
  refine ⟨S,pkt,γ,code,positive,wide,?_,?_⟩
  · intro x
    by_cases h : ε≤Probe.discrepancy F edge req (price x)
    · simp [code,h,not_lt_of_ge h]
    · simp [code,h,lt_of_not_ge h]
  · intro x failed
    let p := choose ⟨price x,legal x,failed⟩
    exact ⟨p.choose,by simp [code,failed],p.choose_spec⟩

/-- Give each of the fixed number of advised packets its own physical selector block.
Only the unique recommended block can be active. This allows each packet to use
its own integer number of simultaneous copies. -/
def singleMenu (code : (Fin d → Fin radix) → ℕ) (j : ℕ) (x : Fin d → Fin radix) : ℕ :=
  if code x=j+1 then j+1 else 0

theorem singleMenu_active (code : (Fin d → Fin radix) → ℕ) (x : Fin d → Fin radix) (j : ℕ) :
    singleMenu code j x ≠ 0 ↔ code x=j+1 := by
  simp [singleMenu]

/-- The common finite catalogue coefficient and gate-slot budget. It works even if
some packet alphabet is empty or the catalogue contains no failing price vectors. -/
def coefficientCap {J E : Type*} [Fintype J] [Fintype E] (arity : J → ℕ)
    (count : ∀ j,Fin (arity j)→E→ℕ) : ℕ :=
  ∑ j, ∑ i, ∑ e, count j i e

theorem le_coefficientCap {J E : Type*} [Fintype J] [Fintype E] (arity : J → ℕ)
    (count : ∀ j,Fin (arity j)→E→ℕ) (j : J) (i : Fin (arity j)) (e : E) :
    count j i e ≤ coefficientCap arity count :=
  (Finset.single_le_sum (fun x _ => Nat.zero_le (count j i x)) (Finset.mem_univ e)).trans <|
    (Finset.single_le_sum (fun y _ => Nat.zero_le (∑x,count j y x)) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun z _ => Nat.zero_le (∑y,∑x,count z y x)) (Finset.mem_univ j))


end Hierarchy.ProtocolRAM

end OAI
