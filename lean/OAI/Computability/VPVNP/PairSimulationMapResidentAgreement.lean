import OAI.Computability.VPVNP.PairSimulationMapPortScan
import OAI.Computability.VPVNP.PairSimulationMapPortAgreement
import OAI.Computability.VPVNP.PairSimulationMapTagBits

/-!
# Agreement of all selector tags on the resident incident fields

The scan's directory contains one selector-start pointer per source and
target incidence of the party. Each pointer skips that port's own payload.
All comparisons read the single original anchor field. The successful exit
is exactly the agreement condition of the grouped motif entry.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapResidentAgreement

open MotifSelector MotifEntry MapPortAgreement PrimedInputRAM
open BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {J E : Type*} {u b w : ℕ} {G : Supply J E} {v : E → ℕ} {party : J}

/-- The underlying supply edge of either port. -/
def edge : Port G party → E
  | .inl e => e.val
  | .inr e => e.val

/-- The original bit field at one port, including its own payload. -/
def field (x : Half G (fun e => Fin (v e + u * b) → Bool) party) :
    (t : Port G party) → Fin (v (edge t) + u * b) → Bool
  | .inl e => x.1 e.val e.property
  | .inr e => x.2 e.val e.property

variable [DecidableEq J]

/-- The incidence selected by the motif interpreter for its reference field.
If the anchor is a self-loop the source incidence supplies the reference. -/
def anchorPort (G : Supply J E) (party : J) : Port G party :=
  if h : party = G.src (G.anchor party) then .inl ⟨G.anchor party,h⟩
  else .inr ⟨G.anchor party, ((G.anchor_incident party).resolve_left fun he ↦ h he.symm).symm⟩

omit [DecidableEq J] in
theorem read_port (x : Half G (fun e => Fin (v e + u * b) → Bool) party) (t : Port G party) :
    portTag (mapHalf G (fun _ ↦ readTag) x) t = readTag (field x t) := by
  cases t <;> rfl

theorem read_anchor (x : Half G (fun e => Fin (v e + u * b) → Bool) party) :
    anchor G party (mapHalf G (fun _ ↦ readTag) x) = readTag (field x (anchorPort G party)) := by
  unfold anchor anchorPort
  split
  · rename_i h
    rw [dite_eq_left h]
    rfl
  · rename_i h
    rw [dite_eq_right h]
    rfl

/-- The first selector cell is located immediately after the port's payload. -/
def selectorStart (v : E → ℕ) (base : Port G party → BurstRAM.Word w) (t : Port G party) :
    BurstRAM.Word w := base t + (v (edge t) : BurstRAM.Word w)

variable [Fintype E]

/-- The input fields and pointer table needed by the native checker. Bits
on two halves of a self-loop can differ and all the fields may be malformed. -/
structure Resident (order : Fin (Fintype.card E) ≃ E)
    (x : Half G (fun e => Fin (v e + u * b) → Bool) party) (base : Port G party → BurstRAM.Word w)
    (mem : BurstRAM.Word w → BurstRAM.Word w) (dir : BurstRAM.Word w) : Prop where
  pointers : ∀ i : Fin (ports G party order).length,
    mem (dir + (i.val : BurstRAM.Word w)) = selectorStart v base ((ports G party order).get i)
  cells : ∀ t : Port G party, ∀ i : Fin (v (edge t) + u * b),
    mem (base t + (i.val : BurstRAM.Word w)) = encodeBit w (field x t i)

/-- The pointer-based word predicate, directly on the original resident
bits, is equivalent to the agreement test on the decoded selectors. -/
theorem agrees_iff (order : Fin (Fintype.card E) ≃ E)
    (x : Half G (fun e => Fin (v e + u * b) → Bool) party) (base : Port G party → BurstRAM.Word w)
    (mem : BurstRAM.Word w → BurstRAM.Word w) (dir : BurstRAM.Word w)
    (hres : Resident order x base mem dir) (hlen : u * b < 2 ^ w) :
    MapPortScan.Agrees mem dir (selectorStart v base (anchorPort G party))
      (ports G party order).length (u * b) ↔
      consistent G party (mapHalf G (fun _ ↦ readTag) x) := by
  let t₀ := anchorPort G party
  have cell (t : Port G party) (i : Fin (u * b)) :
      mem (selectorStart v base t + (i.val : BurstRAM.Word w)) =
        encodeBit w (field x t (Fin.natAdd (v (edge t)) i)) := by
    simpa [selectorStart, add_assoc] using hres.cells t (Fin.natAdd (v (edge t)) i)
  have hh (t : Port G party) : (∀ j : Fin (u * b),
      mem (selectorStart v base t + (j.val : BurstRAM.Word w)) =
        mem (selectorStart v base t₀ + (j.val : BurstRAM.Word w))) ↔
      ∀ i : Fin u, readTag (field x t) i = readTag (field x t₀) i := by
    rw [MapConsistency.readTag_eq_iff_suffix]
    simp_rw [cell]
    constructor
    · intro h i
      have hw : 0 < w := by
        by_contra! hz
        have hwz := Nat.eq_zero_of_le_zero hz
        have hn : u * b < 1 := by simpa only [hwz, pow_zero] using hlen
        have hi := i.isLt
        omega
      apply Bool.eq_iff_iff.mpr
      rw [← encodeBit_eq_one hw, ← encodeBit_eq_one hw, h i]
    · exact fun h i ↦ congrArg _ (h i)
  rw [consistent_iff_ports]
  simp_rw [read_port, read_anchor]
  constructor
  · intro h t
    obtain ⟨i, he⟩ := List.mem_iff_get.mp (mem_ports G party order t)
    apply (hh t).mp
    simpa only [hres.pointers i, he, t₀] using h i
  · intro h i
    simpa only [hres.pointers i, t₀] using (hh ((ports G party order).get i)).mpr (h _)

/-- The machine reads each port's pointer, scans its raw bits, and sends
every inconsistent input to the rejecting continuation. -/
theorem native {p r k : ℕ} {M : Machine w p r k} {pc inner : Fin 7 → Fin p}
    {reg : Fin 11 ↪ Fin r} {yes no : Fin p} (hl : MapPortScan.Linked M pc inner reg yes no)
    (order : Fin (Fintype.card E) ≃ E) (x : Half G (fun e => Fin (v e + u * b) → Bool) party)
    (base : Port G party → BurstRAM.Word w) (dir : BurstRAM.Word w) (c : Config w p r)
    (hc : c.pc = pc 0) (hdir : c.reg (reg 7) = dir)
    (hend : c.reg (reg 8) = dir + ((ports G party order).length : BurstRAM.Word w))
    (ha : c.reg (reg 9) = selectorStart v base (anchorPort G party))
    (hw : c.reg (reg 10) = ((u * b : ℕ) : BurstRAM.Word w))
    (h1 : c.reg (reg 3) = 1) (hzero : c.reg (reg 4) = 0)
    (hres : Resident order x base c.privateMem dir)
    (hn : (ports G party order).length < 2 ^ w) (hlen : u * b < 2 ^ w) :
    ∃ out, Prefix M c (List.replicate ((7*(u * b)+6)*(ports G party order).length+3) .tick) out ∧
      out.pc = (if consistent G party (mapHalf G (fun _ ↦ readTag) x) then yes else no) ∧
      (∀ a, MapPortScan.Preserved reg a → out.reg a = c.reg a) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  obtain ⟨out, pre, ho, frame, hm, hp⟩ :=
    MapPortScan.run hl _ _ dir _ c hc hdir hend ha hw hn hlen h1
  refine ⟨out, pre, ?_, frame, hm, hp⟩
  simpa only [hzero, true_and, agrees_iff order x base _ dir hres hlen] using ho

end PairSimulation.MapResidentAgreement

end VPVNP
end Computability
end OAI
