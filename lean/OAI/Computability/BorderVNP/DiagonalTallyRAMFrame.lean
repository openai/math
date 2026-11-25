import OAI.Computability.BorderVNP.DiagonalTallyRAMCode

/-! # The ten public frame words of the tally stage -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM

/-- The fixed directory positions supplying the tally kernels. -/
structure Frame extends TotalsFrame where
  /-- Base of this team's local count array. -/
  localBase : ℕ
  /-- Start of the sparse coordinate/increment record stream. -/
  records : ℕ
  /-- Number of sparse records. -/
  count : ℕ
  /-- First input bit of the subtotal part of the common prefix. -/
  rawBits : ℕ
  /-- Number of this team in the common team order. -/
  team : ℕ
  /-- Number of binary places in each broadcast subtotal. -/
  width : ℕ

/-- Public argument zero identifies the directory. Its ten physical words encode
the addresses and dimensions used by all four fixed fragments. -/
def Frame.resident (f : Frame) {w : ℕ} (pub : Arg → Word w) (m : Memory w) : Prop :=
  let a := (pub 0).val
  (m (a+32)).val = f.localBase ∧ (m (a+33)).val = f.dim ∧ (m (a+34)).val = f.records ∧
  (m (a+35)).val = f.count ∧ (m (a+36)).val = f.rawBits ∧ (m (a+37)).val = f.claims ∧
  (m (a+38)).val = f.teams ∧ (m (a+39)).val = f.team ∧ (m (a+40)).val = f.width ∧
  (m (a+41)).val = f.totals

/-- Sufficient word-address space for the finite directory and every array cursor,
including the one-past-the-end cursor used in a terminating test. -/
def Frame.addressesFit (f : Frame) (w base : ℕ) : Prop :=
  base+41 < 2^w ∧ f.localBase+f.dim < 2^w ∧ f.records+2*f.count < 2^w ∧
    f.rawBits+(f.teams*f.dim)*f.width < 2^w ∧
    f.claims+f.teams*f.dim+f.dim < 2^w ∧ f.totals+f.dim < 2^w ∧
    f.team < f.teams ∧ f.teams < 2^w ∧ f.width ≤ w

private theorem fit_index (f : Frame) {w a : ℕ} (hf : f.addressesFit w a) :
    f.team*f.dim < 2^w ∧ f.claims+f.team*f.dim < 2^w ∧
      f.claims+f.team*f.dim+f.dim < 2^w := by
  obtain ⟨_,_,_,_,hc,_,ht,_,_⟩ := hf
  have hh := Nat.mul_le_mul_right f.dim ht.le
  omega

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (m : Memory w)
  (s : Bank w) (f : Frame)

private abbrev safe (c : Code) (w : ℕ) (pub : Arg → Word w) (m : Memory w) (s : Bank w) :=
  c.safeReadOnly w (readings pub) (readings m) (readings s)

private abbrev result (c : Code) {w : ℕ} (pub : Arg → Word w) (m : Memory w) (s : Bank w) :=
  c.evalNat (readings pub) (readings m) (readings s)

set_option maxRecDepth 3000 in
private theorem scatterSetup_spec (hr : f.resident pub m) (hf : f.addressesFit w (pub 0).val) :
    safe scatterSetup w pub m s ∧
    let t := result scatterSetup pub m s
    t 48 = f.localBase ∧ t 49 = f.dim ∧ t 50 = f.records ∧ t 51 = f.records+2*f.count ∧ t 63 = 1 := by
  obtain ⟨h32,h33,h34,h35,_,_,_,_,_,_⟩ := hr
  obtain ⟨hdir,_,hstop,_,_,_,_,_,_⟩ := hf
  have hw : w ≠ 0 := by intro hw; subst w; simp at hdir
  simp [safe,result,scatterSetup,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,
    addressOpFits,addressOp,readings,Function.update,h32,h33,h34,h35]; omega

/-- Read the directory, calculate the record end pointer, and load the scatter ABI. -/
theorem scatterSetup_runs (hr : f.resident pub m) (hf : f.addressesFit w (pub 0).val) :
    ∃ es t, Runs pub mac scatterSetup s m es t m ∧ traceCost es ≤ scatterSetup.slots ∧
      DiagonalTallyScatter.Loaded t f.localBase f.dim f.records (f.records+2*f.count) := by
  obtain ⟨safe, he⟩ := scatterSetup_spec pub m s f hr hf
  obtain ⟨es,t,r,c,ht⟩ := Code.runReadOnly scatterSetup pub mac m s safe
  refine ⟨es,t,r,c,?_⟩
  change readings t 48 = _ ∧ readings t 49 = _ ∧ readings t 50 = _ ∧ readings t 51 = _ ∧
    readings t 63 = _
  rw [ht]
  exact he

set_option maxRecDepth 3000 in
private theorem packSetup_spec (hr : f.resident pub m) (hf : f.addressesFit w (pub 0).val) :
    safe packSetup w pub m s ∧
    let t := result packSetup pub m s
    t 50 = f.rawBits ∧ t 51 = f.teams*f.dim ∧ t 52 = f.width ∧ t 53 = f.claims ∧ t 63 = 1 := by
  obtain ⟨_,h33,_,_,h36,h37,h38,_,h40,_⟩ := hr
  obtain ⟨hdir,_,_,_,hclaim,_,_,_,_⟩ := hf
  have hw : w ≠ 0 := by intro hw; subst w; simp at hdir
  simp [safe,result,packSetup,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,
    addressOpFits,addressOp,readings,Function.update,h33,h36,h37,h38,h40]; omega

/-- Read the input and output cursors and the fixed-length broadcast encoding. -/
theorem packSetup_runs (hr : f.resident pub m) (hf : f.addressesFit w (pub 0).val) :
    ∃ es t, Runs pub mac packSetup s m es t m ∧ traceCost es ≤ packSetup.slots ∧
      (t 50).val = f.rawBits ∧ (t 51).val = f.teams*f.dim ∧ (t 52).val = f.width ∧
      (t 53).val = f.claims ∧ (t 63).val = 1 := by
  obtain ⟨safe, he⟩ := packSetup_spec pub m s f hr hf
  obtain ⟨es,t,r,c,ht⟩ := Code.runReadOnly packSetup pub mac m s safe
  dsimp only [result] at he
  rw [← ht] at he
  exact ⟨es,t,r,c,he⟩

set_option maxRecDepth 3000 in
private theorem verifySetup_spec (hr : f.resident pub m) (hf : f.addressesFit w (pub 0).val) :
    safe verifySetup w pub m s ∧
    let t := result verifySetup pub m s
    t 48 = f.localBase ∧ t 49 = f.localBase+f.dim ∧ t 50 = f.claims+f.team*f.dim ∧ t 63 = 1 := by
  obtain ⟨h32,h33,_,_,_,h37,_,h39,_,_⟩ := hr
  have h := fit_index f hf
  obtain ⟨hdir,hlocal,_,_,_,_,_,_,_⟩ := hf
  have hw : w ≠ 0 := by intro hw; subst w; simp at hdir
  simp [safe,result,verifySetup,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,
    addressOpFits,addressOp,readings,Function.update,h32,h33,h37,h39]; omega

private theorem eq_word_of_val {n : ℕ} {v : Word w} (h : v.val = n) : v = word w n := by
  subst n
  exact Fin.ext (word_val _ _ v.isLt).symm

/-- The local verifier is positioned on the exact row selected by its public team number. -/
theorem verifySetup_runs (hr : f.resident pub m) (hf : f.addressesFit w (pub 0).val) :
    ∃ es t, Runs pub mac verifySetup s m es t m ∧ traceCost es ≤ verifySetup.slots ∧
      t 48 = word w f.localBase ∧ t 49 = word w (f.localBase+f.dim) ∧
      t 50 = word w (f.claims+f.team*f.dim) ∧ t 63 = 1 := by
  obtain ⟨safe, he⟩ := verifySetup_spec pub m s f hr hf
  obtain ⟨es,t,r,c,ht⟩ := Code.runReadOnly verifySetup pub mac m s safe
  dsimp only [result] at he
  rw [← ht] at he
  exact ⟨es,t,r,c, eq_word_of_val he.1, eq_word_of_val he.2.1,
    eq_word_of_val he.2.2.1, eq_word_of_val he.2.2.2⟩

set_option maxRecDepth 3000 in
private theorem aggregateSetup_spec (hr : f.resident pub m) (hf : f.addressesFit w (pub 0).val) :
    safe aggregateSetup w pub m s ∧
    let t := result aggregateSetup pub m s
    t 49 = f.dim ∧ t 50 = f.teams ∧ t 58 = f.totals ∧ t 59 = f.claims ∧ t 63 = 1 ∧ t 56 = 0 := by
  obtain ⟨_,h33,_,_,_,h37,h38,_,_,h41⟩ := hr
  obtain ⟨hdir,_,_,_,_,_,_,_,_⟩ := hf
  have hw : w ≠ 0 := by intro hw; subst w; simp at hdir
  simp [safe,result,aggregateSetup,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,
    addressOpFits,addressOp,readings,Function.update,h33,h37,h38,h41]; omega

/-- The aggregation reads every team in the same order and stores into the public output bank. -/
theorem aggregateSetup_runs (hr : f.resident pub m) (hf : f.addressesFit w (pub 0).val) :
    ∃ es t, Runs pub mac aggregateSetup s m es t m ∧ traceCost es ≤ aggregateSetup.slots ∧
      f.toTotalsFrame.loaded t ∧ t 56 = 0 := by
  obtain ⟨safe, he⟩ := aggregateSetup_spec pub m s f hr hf
  obtain ⟨es,t,r,c,ht⟩ := Code.runReadOnly aggregateSetup pub mac m s safe
  dsimp only [result] at he
  rw [← ht] at he
  exact ⟨es,t,r,c, ⟨eq_word_of_val he.1, eq_word_of_val he.2.1, eq_word_of_val he.2.2.1,
    eq_word_of_val he.2.2.2.1, eq_word_of_val he.2.2.2.2.1⟩, eq_word_of_val he.2.2.2.2.2⟩

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
