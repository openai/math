import OAI.Computability.VPVNP.PairSimulationMapConsistency
import OAI.Computability.VPVNP.PairSimulationPrivateFields
import OAI.Computability.VPVNP.DegreeRefreshMotif

/-!
# Testing the two diagonal ties in a refresh kernel

At a port the outgoing old half is compared to its outgoing external
segment, and the incoming external segment to the incoming old half. The
widths of these two comparisons can differ. Both use the same discrepancy
mask, so success means every bit of both ties agrees.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshDiagonal

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Embed the seven bit-comparison loop registers into the ten registers of the two-sided
diagonal test. -/
def loopRegs (reg : Fin 10 ↪ Fin r) : Fin 7 ↪ Fin r := (Fin.castLEEmb (by decide)).trans reg

/-- Registers 0,1,2 give the first left cursor, exclusive left end and
right cursor. Registers 7,8,9 give the second triple. -/
def control (pc first second : Fin 7 → Fin p) (reg : Fin 10 ↪ Fin r) (yes no : Fin p) :
    Fin 7 → Instr w p r k :=
  ![.constant (reg 3) 1 (pc 1), .constant (reg 4) 0 (first 0),
    .copy (reg 0) (reg 7) (pc 3), .copy (reg 1) (reg 8) (pc 4),
    .copy (reg 2) (reg 9) (second 0), .constant (reg 5) 0 (pc 6),
    .jumpEq (reg 4) (reg 5) yes no]

/-- The installed control code links the two comparison scans to their return labels before
branching on the accumulated mismatch flag. -/
structure Linked (M : Machine w p r k) (pc first second : Fin 7 → Fin p)
    (reg : Fin 10 ↪ Fin r) (yes no : Fin p) : Prop where
  head : ∀ j, M.code (pc j) = control pc first second reg yes no j
  firstScan : MapConsistency.Linked M first (loopRegs reg) (pc 2)
  secondScan : MapConsistency.Linked M second (loopRegs reg) (pc 5)

variable {M : Machine w p r k} {pc first second : Fin 7 → Fin p} {reg : Fin 10 ↪ Fin r}
variable {yes no : Fin p}

private theorem step_at (h : Linked M pc first second reg yes no) (j : Fin 7) (c : Config w p r)
    (hc : c.pc = pc j) :
    M.program.step c = (control pc first second reg yes no j).run M.publicData c := by
  simp [Machine.program, hc, h.head j]

/-- Private starts of the two old halves and their corresponding external
segments. The lengths belong to the original, independent half-wires. -/
structure Pointers (w : ℕ) where
  /-- Private start address of the old outgoing half-word. -/
  oldOut : Word w
  /-- Private start address of the outgoing segment against which the old outgoing half is
  checked. -/
  externalOut : Word w
  /-- Private start address of the old incoming half-word. -/
  oldIn : Word w
  /-- Private start address of the incoming segment against which the old incoming half is
  checked. -/
  externalIn : Word w

/-- Register layout at entry to the two diagonal scans. -/
def Pointers.Ready (a : Pointers w) (reg : Fin 10 ↪ Fin r) (c : Config w p r)
    (outWidth inWidth : ℕ) : Prop :=
  (c.reg (reg 0) = a.oldOut ∧ c.reg (reg 1) = a.oldOut + (outWidth : Word w) ∧
    c.reg (reg 2) = a.externalOut) ∧
  (c.reg (reg 7) = a.oldIn ∧ c.reg (reg 8) = a.oldIn + (inWidth : Word w) ∧
    c.reg (reg 9) = a.externalIn)

/-- A pair of equally long bit fields in private memory. -/
structure Tie (w n : ℕ) where
  /-- Private read cursor for the original half-word in this diagonal tie. -/
  left : Word w
  /-- Private read cursor for the segment paired with that half-word. -/
  right : Word w
  /-- The independent bits of the original half-word that the comparison must read. -/
  oldBits : Fin n → Bool
  /-- Bits of the selected segment that are compared with the corresponding old half-word. -/
  segmentBits : Fin n → Bool

/-- Both private ranges contain the encoded bits specified for this tie, in increasing bit
order. -/
def Tie.resident {n : ℕ} (b : Tie w n) (mem : Word w → Word w) : Prop :=
  (∀ j, mem (b.left + (j.val : Word w)) = PrivateFields.bitValue w (b.oldBits j)) ∧
  ∀ j, mem (b.right + (j.val : Word w)) = PrivateFields.bitValue w (b.segmentBits j)

private theorem bit_agrees {n : ℕ} (x y : Fin n → Bool) (hn : n < 2^w) :
    (∀ j, PrivateFields.bitValue w (x j) = PrivateFields.bitValue w (y j)) ↔ x = y := by
  constructor
  · intro h
    funext j
    have hw : 1 < 2^w := by have := j.isLt; omega
    have hone : (1 : Word w) ≠ 0 := by
      intro e
      have hv := congrArg Fin.val e
      change 1 % (2^w) = 0 at hv
      rw [Nat.mod_eq_of_lt hw] at hv
      omega
    have he := h j
    cases hx : x j <;> cases hy : y j <;> simp_all [PrivateFields.bitValue]
  · rintro rfl; exact fun _ ↦ rfl

/-- Execute both comparisons, even if the first one fails. The input may
contain any independent old and new halves, including empty fields. -/
theorem compare (h : Linked M pc first second reg yes no)
    {n₁ n₂ : ℕ} (a : Tie w n₁) (b : Tie w n₂) (c : Config w p r) (hc : c.pc = pc 0)
    (ha : c.reg (reg 0) = a.left ∧ c.reg (reg 1) = a.left + (n₁ : Word w) ∧ c.reg (reg 2) = a.right)
    (hb : c.reg (reg 7) = b.left ∧ c.reg (reg 8) = b.left + (n₂ : Word w) ∧ c.reg (reg 9) = b.right)
    (hm₁ : a.resident c.privateMem) (hm₂ : b.resident c.privateMem)
    (hn₁ : n₁ < 2^w) (hn₂ : n₂ < 2^w) :
    ∃ out, Prefix M c (List.replicate (7*(n₁+n₂)+9) .tick) out ∧
      out.pc = (if a.oldBits = a.segmentBits ∧ b.oldBits = b.segmentBits then yes else no) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      ∀ j, j ∉ Set.range reg → out.reg j = c.reg j := by
  classical
  let c₁ := c.put (pc 1) (reg 3) 1
  let a₀ := c₁.put (first 0) (reg 4) 0
  have e₀ : M.program.step c = .localStep c₁ := step_at h 0 c hc
  have e₁ : M.program.step c₁ = .localStep a₀ := step_at h 1 c₁ rfl
  have start : Prefix M c (List.replicate 2 .tick) a₀ := .tick e₀ (.tick e₁ (.nil _))
  obtain ⟨mid, sa, pm, _, _, maskA, keepA, memA, stateA⟩ := MapConsistency.compareArrays h.firstScan
    (fun j ↦ PrivateFields.bitValue w (a.oldBits j)) (fun j ↦ PrivateFields.bitValue w (a.segmentBits j))
    a.left a.right a₀ rfl
    (by simpa [a₀,c₁,Config.put,loopRegs] using ha.1)
    (by simpa [a₀,c₁,Config.put,loopRegs] using ha.2.1)
    (by simpa [a₀,c₁,Config.put,loopRegs] using ha.2.2)
    (by simp [a₀,c₁,Config.put,loopRegs]) hn₁ hm₁.1 hm₁.2
  have hm : mid.reg (reg 4) = 0 ↔ a.oldBits = a.segmentBits := by
    simpa [a₀,c₁,Config.put,loopRegs,bit_agrees a.oldBits a.segmentBits hn₁] using maskA
  have keep (j : Fin 10) (hj : j = 3 ∨ 7 ≤ j.val) : mid.reg (reg j) = a₀.reg (reg j) := by
    apply keepA
    all_goals
      intro he
      have hv := congrArg Fin.val (reg.injective he)
      norm_num [Fin.castLEEmb] at hv
      rcases hj with rfl | hj <;> omega
  have h7 : mid.reg (reg 7) = b.left := by rw [keep 7 (by decide)]; simpa [a₀,c₁,Config.put] using hb.1
  have h8 : mid.reg (reg 8) = b.left + (n₂ : Word w) := by rw [keep 8 (by decide)]; simpa [a₀,c₁,Config.put] using hb.2.1
  have h9 : mid.reg (reg 9) = b.right := by rw [keep 9 (by decide)]; simpa [a₀,c₁,Config.put] using hb.2.2
  let c₂ := mid.put (pc 3) (reg 0) (mid.reg (reg 7))
  let c₃ := c₂.put (pc 4) (reg 1) (c₂.reg (reg 8))
  let b₀ := c₃.put (second 0) (reg 2) (c₃.reg (reg 9))
  have e₂ : M.program.step mid = .localStep c₂ := step_at h 2 mid pm
  have e₃ : M.program.step c₂ = .localStep c₃ := step_at h 3 c₂ rfl
  have e₄ : M.program.step c₃ = .localStep b₀ := step_at h 4 c₃ rfl
  have reload : Prefix M mid (List.replicate 3 .tick) b₀ := .tick e₂ (.tick e₃ (.tick e₄ (.nil _)))
  have hm₂' : b.resident b₀.privateMem := by
    change b.resident mid.privateMem
    rw [memA]
    exact hm₂
  obtain ⟨fin, sb, pf, _, _, maskB, keepB, memB, stateB⟩ := MapConsistency.compareArrays h.secondScan
    (fun j ↦ PrivateFields.bitValue w (b.oldBits j)) (fun j ↦ PrivateFields.bitValue w (b.segmentBits j))
    b.left b.right b₀ rfl (by simp [b₀,c₃,c₂,Config.put,loopRegs,h7])
    (by simp [b₀,c₃,c₂,Config.put,loopRegs,h8]) (by simp [b₀,c₃,c₂,Config.put,loopRegs,h9])
    (by simp [b₀,c₃,c₂,a₀,c₁,Config.put,loopRegs,keep 3 (by decide)]) hn₂ hm₂'.1 hm₂'.2
  have hm' : fin.reg (reg 4) = 0 ↔ a.oldBits = a.segmentBits ∧ b.oldBits = b.segmentBits := by
    simpa [b₀,c₃,c₂,Config.put,loopRegs,hm,bit_agrees b.oldBits b.segmentBits hn₂] using maskB
  let t := fin.put (pc 6) (reg 5) 0
  let out := {t with pc := if a.oldBits = a.segmentBits ∧ b.oldBits = b.segmentBits then yes else no}
  have e₅ : M.program.step fin = .localStep t := step_at h 5 fin pf
  have e₆ : M.program.step t = .localStep out := by
    rw [step_at h 6 t rfl]
    simp [control, Instr.run, t, Config.put, out, hm']
  have finish : Prefix M fin (List.replicate 2 .tick) out := .tick e₅ (.tick e₆ (.nil _))
  refine ⟨out, ?_, rfl, memB.trans memA, stateB.trans stateA, ?_⟩
  · convert (((start.append sa).append reload).append sb).append finish using 1
    simp only [← List.replicate_add]
    congr 1
    omega
  · intro j hj
    have hn (k : Fin 10) : j ≠ reg k := fun he ↦ hj ⟨k, he.symm⟩
    have hb' := keepB j (hn 0) (hn 2) (hn 4) (hn 5) (hn 6)
    have ha' := keepA j (hn 0) (hn 2) (hn 4) (hn 5) (hn 6)
    simpa [out,t,b₀,c₃,c₂,a₀,c₁,Config.put,hn] using hb'.trans
      ((by simp [b₀,c₃,c₂,Config.put,hn] : b₀.reg j = mid.reg j).trans ha')

/-- The concrete instruction layout. The first two labels are the accepting
and rejecting exits. The three seven-instruction blocks are control and the
two private array comparisons. -/
def label (block : Fin 3) (j : Fin 7) : Fin 23 := (finProdFinEquiv (block, j)).natAdd 2

/-- Resizable 23-instruction diagonal test with two seven-instruction bit scans and distinct
accept and reject exits. -/
def table : Template 23 10 0 where
  literalWidth := 1
  entry := label 0 0
  code := Fin.addCases (m := 2) (n := 21) (fun i ↦ if i.val = 0 then .accept else .reject)
    fun q ↦
      let z : Fin 3 × Fin 7 := finProdFinEquiv.symm q
      let reg := Function.Embedding.refl (Fin 10)
      if z.1 = 0 then control (label 0) (label 1) (label 2) reg 0 1 z.2
      else if z.1 = 1 then MapConsistency.instruction (label 1) (loopRegs reg) (label 0 2) z.2
      else MapConsistency.instruction (label 2) (loopRegs reg) (label 0 5) z.2

theorem table_linked (w : ℕ) : Linked (table.instantiate w Fin.elim0)
    (label 0) (label 1) (label 2) (Function.Embedding.refl (Fin 10)) 0 1 := by
  constructor
  · intro j
    fin_cases j <;> rfl
  · intro j
    fin_cases j <;> rfl
  · intro j
    fin_cases j <;> rfl

open Compression.Refresh in
/-- Specialize the physical comparison to the two actual diagonal demand
coordinates of the refresh kernel. The ordinary port map is entered exactly
when the integer diagonal multiplier is one. -/
theorem compare_portDiagonal {B : Type*} [Fintype B] {d : ℕ}
    (t : Equiv.Perm (Arc B d)) (width : Arc B d → ℕ) (v : B) (i : Fin d)
    (x : (oldNetwork ℤ t width).Basis (v, i)) (z : PortSegments t width v i)
    (outOld outExternal inOld inExternal : BurstRAM.Word w)
    (h : Linked M pc first second reg yes no) (c : Config w p r) (hc : c.pc = pc 0)
    (hout : c.reg (reg 0) = outOld ∧ c.reg (reg 1) = outOld + (width ((v,i),i) : BurstRAM.Word w) ∧
      c.reg (reg 2) = outExternal)
    (hin : c.reg (reg 7) = inOld ∧ c.reg (reg 8) = inOld + (width (t.symm ((v,i),i)) : BurstRAM.Word w) ∧
      c.reg (reg 9) = inExternal)
    (ho : (Tie.mk outOld outExternal (x.1 ((v,i),i) rfl) (z.1 i)).resident c.privateMem)
    (hi : (Tie.mk inOld inExternal (incomingHalf t width v i i x) (z.2 i)).resident c.privateMem)
    (h₁ : width ((v,i),i) < 2^w) (h₂ : width (t.symm ((v,i),i)) < 2^w) :
    ∃ out, Prefix M c (List.replicate (7*(width ((v,i),i)+width (t.symm ((v,i),i)))+9) .tick) out ∧
      out.pc = (if portDiagonal t width v i x z = (1 : ℤ) then yes else no) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      ∀ j, j ∉ Set.range reg → out.reg j = c.reg j := by
  obtain ⟨out, path, dest, keep⟩ := compare h _ _ c hc hout hin ho hi h₁ h₂
  refine ⟨out, path, ?_, keep⟩
  have hd : portDiagonal t width v i x z = (1 : ℤ) ↔ x.1 ((v,i),i) rfl = z.1 i ∧
      incomingHalf t width v i i x = z.2 i := by
    unfold portDiagonal segmentTest
    rw [eq_comm (a := z.2 i) (b := incomingHalf t width v i i x)]
    split_ifs <;> simp_all
  simpa only [hd] using dest

end PairSimulation.RefreshDiagonal

end VPVNP
end Computability
end OAI
