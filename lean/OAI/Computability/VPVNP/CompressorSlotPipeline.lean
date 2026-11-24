import OAI.Computability.VPVNP.CompressorSlotNetwork
import OAI.Computability.VPVNP.CompressorSlotOwnerRuns
import OAI.Computability.VPVNP.CompressorSlotFrames

/-!
# The four physical passes that construct the next slot matching

Generate the genuine and dummy owner fields in two contiguous portions of
one directory. Feed that directory to the bounded append pass, then invert
the real incidence rows. Each pass reads the actual post-memory of its
predecessor. All four cursor ranges and both address bounds are explicit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotSchedule

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SlotOwners

variable {E : Type*} [Fintype E] {A B w : ℕ} (D : Directory E A B)

/-- The selected input records determine the two portions of the owner array.
All four genuine inputs and the cyclic successor table precede the scratch
space allocated at `base`. -/
structure OwnerInput (g : Fin 8 → Word w) (p : Fin 3 → Word w) (mem : Memory w)
    (base genuineCount dummyCount : ℕ) : Prop where
  total : genuineCount+dummyCount=A
  startGenuine : (g 7).val=base
  startDummy : (p 2).val=base+genuineCount
  genuineSources : ∀ i < genuineCount, ∀ a ∈ genuineInputs g mem (Fin.ofNat _ i), a.val < base
  dummySource : ∀ i < dummyCount, (p 1 + SlotOwners.dummySource p (Fin.ofNat _ i)).val < base
  genuineValue : ∀ i < genuineCount, genuineOwner g mem (Fin.ofNat _ i) = D.wordOwner (Fin.ofNat _ i)
  dummyValue : ∀ i < dummyCount, dummyOwner p mem (Fin.ofNat _ i) = D.wordOwner (Fin.ofNat _ (genuineCount+i))

omit [Fintype E] in
/-- The genuine and dummy worker scans produce the complete selected owner table
and preserve every address outside that contiguous table. The execution reports
also give the two end cursors and exact cost for the enclosing schedule. -/
theorem owner_table_run {base ng nd : ℕ} (g : Fin 8 → Word w) (p : Fin 3 → Word w)
    (mem : Memory w) (input : OwnerInput D g p mem base ng nd) (fit : base+A ≤ 2^w) :
    ∃ gs ds,
      let mid := after mem (eventLog gs)
      let final := after mid (eventLog ds)
      FilledRun ((template genuine 0).instantiate w g).program 49 5 48 ng (g 7)
        (fun i => genuineOwner g mem (Fin.ofNat _ i)) mem gs ∧
      FilledRun ((template dummy 0).instantiate w p).program 20 2 19 nd (p 2)
        (fun i => dummyOwner p mem (Fin.ofNat _ i)) mid ds ∧
      (∀ i : Word w, i.val < A → final (base+i.val) = D.wordOwner i) ∧
      (∀ addr, addr < base ∨ base+A ≤ addr → final addr = mem addr) ∧
      RAMBuckets.cost Report.probes (gs++ds) = 6*ng+3*nd := by
  obtain ⟨total, hgbase, hdbase, hgsrc, hdsrc, hgval, hdval⟩ := input
  obtain ⟨gs, ds, hg, hdm, hG, hFrame, hGenCost⟩ := owner_runs g p mem ng nd
    (by omega) (by omega) (fun i hi a ha ↦ Or.inl (hgbase ▸ hgsrc i hi a ha))
    (fun i hi ↦ Or.inl (hgbase ▸ hdsrc i hi))
  let m₂ := after (after mem (eventLog gs)) (eventLog ds)
  have init (i : Word w) (hi : i.val < A) : m₂ (base+i.val) = D.wordOwner i := by
    have he : Fin.ofNat (2^w) i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    by_cases h : i.val < ng
    · have h₁ := hG i.val h
      rw [hgbase] at h₁
      exact h₁.trans ((hgval i.val h).trans (congrArg D.wordOwner he))
    · let k := i.val-ng
      have hk : k < nd := by dsimp [k]; omega
      have hj : ng+k = i.val := Nat.add_sub_of_le (by omega)
      have h₂ := hdm.filled k hk
      rw [hdbase, Nat.add_assoc, hj] at h₂
      exact h₂.trans (by simpa only [hj,he] using hdval k hk)
  have genFrame (a : ℕ) (ha : a < base ∨ base+A ≤ a) : m₂ a = mem a :=
    hFrame a (by omega)
  exact ⟨gs,ds,hg,hdm,init,genFrame,hGenCost⟩

/-- Full native scan on the selected role, subdivision and successor records.
The final tables are usable by the two-read endpoint query. Their allocation
and all auxiliary singleton rows leave addresses outside the scratch region
unchanged. -/
theorem run {base deg genuineCount dummyCount : ℕ} (g : Fin 8 → Word w) (p : Fin 3 → Word w)
    (mem : Memory w) (input : OwnerInput D g p mem base genuineCount dummyCount)
    (hdeg : 0 < deg) (hdw : deg < 2^w) (hc : ∀ b, Fintype.card {e // D.owner e = b} = deg)
    (hfit : base+A+(B+A)+(B+A)*deg+A < 2^w) (hzero : ∀ u : Word w, u.val < B+A → mem (base+A+u.val) = 0) :
    let ownerM := ((template genuine 0).instantiate w g).program
    let dummyM := ((template dummy 0).instantiate w p).program
    let fill := parameters w base A B deg
    let scatter := scatterParameters w base A B deg
    let fillM := ((template collectPreimage 3).instantiate w fill).program
    let scatterM := ((template SlotScatter.visit 0).instantiate w scatter).program
    let rows := base+A+(B+A)
    let inverse := rows+(B+A)*deg
    ∃ gs ds fs ss,
      let m₁ := after mem (eventLog gs)
      let m₂ := after m₁ (eventLog ds)
      let m₃ := after m₂ (eventLog fs)
      let m₄ := after m₃ (eventLog ss)
      runSegment ownerM 49 (some 0) mem (List.replicate genuineCount []) = some gs ∧
      runSegment dummyM 20 (some 0) m₁ (List.replicate dummyCount []) = some ds ∧
      runSegment fillM 23 (some 0) m₂ (List.replicate A []) = some fs ∧
      runSegment scatterM 10 (some 0) m₃ (List.replicate (B*deg) []) = some ss ∧
      Tables D deg rows inverse hc m₄ ∧
      endState (some 0) gs = some (Fin.ofNat _ genuineCount) ∧
      endState (some 0) ds = some (Fin.ofNat _ dummyCount) ∧
      endState (some 0) fs = some (Fin.ofNat _ A) ∧ endState (some 0) ss = some (Fin.ofNat _ (B*deg)) ∧
      (∀ a, a < base ∨ inverse+A ≤ a → m₄ a = mem a) ∧
      RAMBuckets.cost Report.probes (gs++ds++fs++ss) = 6*genuineCount+3*dummyCount+5*A+3*(B*deg) ∧
      (∀ r ∈ gs, r.events.length=48) ∧ (∀ r ∈ ds, r.events.length=19) ∧
      (∀ r ∈ fs, r.events.length=22) ∧ ∀ r ∈ ss, r.events.length=9 := by
  intro ownerM dummyM fill scatter fillM scatterM rows inverse
  obtain ⟨gs,ds,hg,hdm,init,genFrame,hGenCost⟩ := owner_table_run D g p mem input (by omega)
  let m₂ := after (after mem (eventLog gs)) (eventLog ds)
  have zero (u : Word w) (hu : u.val < B+A) : m₂ (base+A+u.val) = 0 :=
    (genFrame _ (.inr (Nat.le_add_right _ _))).trans (hzero _ hu)
  obtain ⟨fs, ss, hr, hs, ht, hfc, hsc, hsFrame, _, _, cost, hfwork, hswork⟩ :=
    build_tables D hdeg hdw hc hfit m₂ init zero
  refine ⟨gs,ds,fs,ss,hg.executed,hdm.executed,hr,hs,ht,hg.cursor,hdm.cursor,hfc,hsc,?_,?_,
    fun r h ↦ (hg.calls r h).2,fun r h ↦ (hdm.calls r h).2,hfwork,hswork⟩
  · intro a ha
    exact (hsFrame a (by omega)).trans (genFrame a (by omega))
  · rw [RAMBuckets.cost_append,RAMBuckets.cost_append,hGenCost]; omega

end CompressorRecords.SlotSchedule

end VPVNP
end Computability
end OAI
