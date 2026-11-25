import OAI.Computability.BorderVNP.DiagonalResidueRAMFrame
import OAI.Computability.BorderVNP.RoutingISADeterministic

/-! # Native check of the team's claimed subtotal row

Each check reads the claimed broadcast word and the independently accumulated local
counter. It advances both pointers exactly once on equality and rejects on disagreement.
Neither the instruction table nor the number of registers depends on the array length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- The current local word and the corresponding proposed broadcast word. -/
def readPair : Code := .block [.load 54 48, .load 55 50]

/-- Advance the local and broadcast cursors. Register 63 holds one. -/
def advancePair : Code := .block [.binary .add 48 48 63, .binary .add 50 50 63]

/-- One pair of word probes, followed by the equality guard. -/
def checkPair : Code := .seq readPair (.ifEq 54 55 advancePair .reject)

/-- Compare a contiguous local counter array to the team's row in the shared broadcast.
Registers 48,49 are the start and end of the local array, and 50 is the broadcast cursor. -/
def verifyRow : Code := .whileLt 48 49 checkPair

private theorem readPair_effect (s : Bank w) (m : Memory w) :
    let e := effect false s m readPair
    e.bank 54 = m (s 48).val ∧ e.bank 55 = m (s 50).val ∧
    e.bank 48 = s 48 ∧ e.bank 49 = s 49 ∧ e.bank 50 = s 50 ∧ e.bank 63 = s 63 ∧
    e.mem = m ∧ TraceOK e.trace [] 2 := by
  simp [readPair, effect, Code.block, TraceOK, Function.update]

private theorem advancePair_effect (s : Bank w) (m : Memory w) :
    let e := effect false s m advancePair
    e.bank 48 = s 48 + s 63 ∧ e.bank 49 = s 49 ∧ e.bank 50 = s 50 + s 63 ∧
    e.bank 63 = s 63 ∧ e.mem = m ∧ TraceOK e.trace [] 2 := by
  simp [advancePair, effect, Code.block, BinaryOp.eval, TraceOK, tick, Function.update]

private theorem checkPair_runs (s : Bank w) (m : Memory w) (hc : m (s 48).val = m (s 50).val) :
    ∃ es t, Runs pub macros checkPair s m es t m ∧ TraceOK es [] 5 ∧
      t 48 = s 48+s 63 ∧ t 49 = s 49 ∧ t 50 = s 50+s 63 ∧ t 63 = s 63 := by
  let e := effect false s m readPair
  let a := effect false e.bank m advancePair
  obtain ⟨h54,h55,h48,h49,h50,h63,hem,hTrace⟩ := readPair_effect s m
  obtain ⟨ha48,ha49,ha50,ha63,ham,haTrace⟩ := advancePair_effect e.bank m
  change e.mem = m at hem
  change a.mem = m at ham
  have read := effect_runs pub macros false s m readPair (by decide)
  change Runs pub macros readPair s m e.trace e.bank e.mem at read
  rw [hem] at read
  have inc := effect_runs pub macros false e.bank m advancePair (by decide)
  change Runs pub macros advancePair e.bank m a.trace a.bank a.mem at inc
  rw [ham] at inc
  have heq : e.bank 54 = e.bank 55 := h54.trans (hc.trans h55.symm)
  refine ⟨_,_, .seq read (.ifEq (by simpa only [heq, ite_true] using inc)), ?_, ?_⟩
  · simpa using hTrace.append haTrace.cons_tick
  · exact ⟨ha48.trans (congrArg₂ (·+·) h48 h63), ha49.trans h49,
      ha50.trans (congrArg₂ (·+·) h50 h63), ha63.trans h63⟩

/-- Equal arrays give an actual native returning path. Six ticks per coordinate suffice,
plus the final loop test. The check performs no guesses or stores. -/
theorem verifyRow_runs (len localAddr claimAddr : ℕ) (s : Bank w) (m : Memory w)
    (hlocal : localAddr+len < 2^w) (hclaim : claimAddr+len < 2^w)
    (hs : s 48 = word w localAddr) (he : s 49 = word w (localAddr+len))
    (hclaimreg : s 50 = word w claimAddr) (hone : s 63 = 1)
    (hmatch : ∀ i < len, m (localAddr+i) = m (claimAddr+i)) :
    ∃ es t, Runs pub macros verifyRow s m es t m ∧ TraceOK es [] (6*len+1) ∧
      t 48 = word w (localAddr+len) ∧ t 49 = s 49 ∧ t 50 = word w (claimAddr+len) ∧ t 63 = 1 := by
  induction len generalizing s localAddr claimAddr with
  | zero =>
    refine ⟨_,_, .whileDone (by rw [hs,he]; simp), ?_, ?_⟩
    · simp [TraceOK, tick]
    · exact ⟨hs, rfl, hclaimreg, hone⟩
  | succ len ih =>
    have hguard : s 48 < s 49 := by
      change (s 48).val < (s 49).val
      rw [hs,he,word_val _ _ (by omega),word_val _ _ hlocal]; omega
    have hm : m (s 48).val = m (s 50).val := by
      rw [hs,hclaimreg,word_val _ _ (by omega),word_val _ _ (by omega)]
      simpa using hmatch 0 (by omega)
    obtain ⟨es,t,hr,ht,h48,h49,h50,h63⟩ := checkPair_runs (pub := pub) (macros := macros) s m hm
    have h48' : t 48 = word w (localAddr+1) := by rw [h48,hs,hone,word_add,word_one]
    have h50' : t 50 = word w (claimAddr+1) := by rw [h50,hclaimreg,hone,word_add,word_one]
    obtain ⟨tail,z,hr',ht',hz48,hz49,hz50,hz63⟩ :=
      ih (localAddr+1) (claimAddr+1) t (by omega) (by omega) h48'
        (by rw [h49,he]; congr 1; omega) h50' (h63.trans hone)
        (fun i hi => by simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hmatch (i+1) (by omega))
    refine ⟨_,_,.whileStep hguard hr hr', ?_, ?_⟩
    · rw [show 6*(len+1)+1 = (5+(6*len+1))+1 by omega]
      exact (ht.append ht').cons_tick
    · refine ⟨?_, hz49.trans h49, ?_, hz63⟩
      · rw [hz48]; congr 1; omega
      · rw [hz50]; congr 1; omega

private theorem checkPair_necessary {s t : Bank w} {m mt : Memory w} {es}
    (hr : Runs pub macros checkPair s m es t mt) : m (s 48).val = m (s 50).val := by
  unfold checkPair at hr
  cases hr with
  | atom ha _ _ => cases ha
  | seq pre post =>
    let e := effect false s m readPair
    have he := effect_runs pub macros false s m readPair (by decide)
    obtain ⟨_, hbank, _⟩ := he.unique_of_deterministic (by decide) pre
    rw [← hbank] at post
    cases post with
    | atom ha _ _ => cases ha
    | ifEq run =>
      obtain ⟨h54,h55,_⟩ := readPair_effect s m
      by_contra hbad
      have hne : e.bank 54 ≠ e.bank 55 := fun eq => hbad (h54.symm.trans (eq.trans h55))
      rw [ite_eq_right hne] at run
      cases run with | atom ha _ _ => cases ha

/-- A normally returning check forces equality at every physical word.
The assertion holds for arbitrary claimed words and every genuine trace. -/
theorem verifyRow_sound (len localAddr claimAddr : ℕ) (s : Bank w) (m : Memory w)
    (hlocal : localAddr+len < 2^w) (hclaim : claimAddr+len < 2^w)
    (hs : s 48 = word w localAddr) (he : s 49 = word w (localAddr+len))
    (hclaimreg : s 50 = word w claimAddr) (hone : s 63 = 1)
    {t mt es} (hr : Runs pub macros verifyRow s m es t mt) :
    ∀ i < len, m (localAddr+i) = m (claimAddr+i) := by
  induction len generalizing s localAddr claimAddr es with
  | zero => exact fun i hi => (Nat.not_lt_zero i hi).elim
  | succ len ih =>
    have hguard : s 48 < s 49 := by
      change (s 48).val < (s 49).val
      rw [hs,he,word_val _ _ (by omega),word_val _ _ hlocal]; omega
    unfold verifyRow at hr
    cases hr with
    | atom ha _ _ => cases ha
    | whileDone hg => contradiction
    | whileStep _ step loop =>
      have hm := checkPair_necessary step
      obtain ⟨fs,v,run,_,h48,h49,h50,h63⟩ := checkPair_runs (pub := pub) (macros := macros) s m hm
      obtain ⟨_, rfl, rfl⟩ := run.unique_of_deterministic (by decide) step
      intro i hi
      cases i with
      | zero => simpa [hs, hclaimreg, word_val _ _ (show localAddr < 2^w by omega),
          word_val _ _ (show claimAddr < 2^w by omega)] using hm
      | succ i =>
        have hx := ih (localAddr+1) (claimAddr+1) v (by omega) (by omega)
          (by rw [h48,hs,hone,word_add,word_one]) (by rw [h49,he]; congr 1; omega)
          (by rw [h50,hclaimreg,hone,word_add,word_one]) (h63.trans hone) loop i (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hx

/-- Every row check has at most one execution, including the old words at all probes. -/
theorem verifyRow_unique {s t u : Bank w} {m mt mu : Memory w} {es fs}
    (a : Runs pub macros verifyRow s m es t mt) (b : Runs pub macros verifyRow s m fs u mu) :
    es = fs ∧ t = u ∧ mt = mu := a.unique_of_deterministic (by decide) b

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
