import OAI.Computability.BorderVNP.RoutingISACallRow
import OAI.Computability.BorderVNP.RoutingISACallTrace

/-!
# Complete native execution of the owned-cell directory

The fixed assembly loop realizes each accepted private path at each owned cell once.
Its directory and argument words are fetched from live shared memory. Conversely,
a returned loop determines one array of admitted private outcomes and leaves memory
unchanged. Burst interval overflow and private routine rejection are both enforced
by the physical call instruction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private theorem fitRow {f : Frame} (space : f.base + 3*f.count ≤ 2^w) {i : ℕ} (hi : i < f.count) :
    f.address i + 2 < 2^w := by unfold Frame.address; omega

private theorem guard_iff {f : Frame} {i : ℕ} {s : Bank w} (ready : f.Ready i s) :
    s 6 < s 5 ↔ i < f.count := by
  change (s 6).val < (s 5).val ↔ _
  rw [ready.2.2.2.2.2.2, ready.2.2.2.2.2.1]

private theorem loop_run {f : Frame} {i : ℕ} {s : Bank w} {m : Memory w}
    (space : f.base + 3*f.count ≤ 2^w) (ready : f.Ready i s) {xs : List (Option Outcome)}
    (len : i + xs.length = f.count) (valid : f.Admitted m macros i xs) :
    ∃ t, Runs pub macros (.whileLt 6 5 body) s m (f.scanTrace m i xs) t m ∧
      f.Ready f.count t := by
  induction xs generalizing i s with
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at len
    exact ⟨s,.whileDone (fun h => (guard_iff ready).1 h |>.ne len),len ▸ ready⟩
  | cons x xs ih =>
    simp only [List.length_cons] at len
    have more : i < f.count := by omega
    obtain ⟨rowValid,tailValid⟩ := valid
    obtain ⟨gs,u,r,hu,he⟩ := row_run (pub := pub) ready (fitRow space more) more rowValid
    obtain ⟨t,tail,ht⟩ := ih hu (by omega) tailValid
    refine ⟨t,?_,ht⟩
    rw [Frame.scanTrace, ← he, List.cons_append]
    exact .whileStep ((guard_iff ready).2 more) r tail

private theorem loop_decode {f : Frame} {i n : ℕ} {s : Bank w} {m : Memory w}
    (space : f.base + 3*f.count ≤ 2^w) (ready : f.Ready i s) (len : i+n=f.count)
    {es t mt} (run : Runs pub macros (.whileLt 6 5 body) s m es t mt) :
    ∃ xs : List (Option Outcome), xs.length = n ∧ f.Admitted m macros i xs ∧
      es = f.scanTrace m i xs ∧ f.Ready f.count t ∧ mt = m := by
  induction n generalizing i s es with
  | zero =>
    simp only [Nat.add_zero] at len
    obtain ⟨he,ht,hm⟩ := while_last run (fun h => (guard_iff ready).1 h |>.ne len)
    exact ⟨[],rfl,trivial,he,ht ▸ len ▸ ready,hm⟩
  | succ n ih =>
    have more : i < f.count := by omega
    obtain ⟨gs,u,mu,hs,rfl,r,tail⟩ := while_next run ((guard_iff ready).2 more)
    obtain ⟨x,hx,hu,hmu,he⟩ := row_decode ready (fitRow space more) more r
    subst mu
    obtain ⟨xs,hlen,hvalid,htail,ht,hm⟩ := ih hu (by omega) tail
    refine ⟨x::xs,by simp [hlen],⟨hx,hvalid⟩,?_,ht,hm⟩
    rw [Frame.scanTrace, ← he, ← htail, List.cons_append]

/-- The physical loop executes any admissible choice of cell macro paths, preserving
memory, and stops with its cursor at the true row count. -/
theorem directory_run {s : Bank w} {m : Memory w}
    (frameFit : (pub 0).val + 15 < 2^w)
    (space : (Frame.ofMemory pub m).base + 3*(Frame.ofMemory pub m).count ≤ 2^w)
    {xs : List (Option Outcome)} (len : xs.length = (Frame.ofMemory pub m).count)
    (valid : (Frame.ofMemory pub m).Admitted m macros 0 xs) :
    ∃ t, Runs pub macros callOwnedCells s m
        (setupTrace pub m ++ (Frame.ofMemory pub m).scanTrace m 0 xs) t m ∧
      (Frame.ofMemory pub m).Ready (Frame.ofMemory pub m).count t := by
  obtain ⟨u,start,hu⟩ := setup_run (s := s) (macros := macros) (m := m) frameFit
  obtain ⟨t,tail,ht⟩ := loop_run (pub := pub) space hu (by simpa only [Nat.zero_add] using len) valid
  exact ⟨t,start.seq tail,ht⟩

/-- Every successful native directory history decodes into one outcome per row.
A different team cannot call an unowned cell or supply guesses on its behalf. -/
theorem directory_decode {s : Bank w} {m : Memory w}
    (frameFit : (pub 0).val + 15 < 2^w)
    (space : (Frame.ofMemory pub m).base + 3*(Frame.ofMemory pub m).count ≤ 2^w)
    {es t mt} (run : Runs pub macros callOwnedCells s m es t mt) :
    ∃ xs : List (Option Outcome), xs.length = (Frame.ofMemory pub m).count ∧
      (Frame.ofMemory pub m).Admitted m macros 0 xs ∧
      es = setupTrace pub m ++ (Frame.ofMemory pub m).scanTrace m 0 xs ∧
      (Frame.ofMemory pub m).Ready (Frame.ofMemory pub m).count t ∧ mt = m := by
  obtain ⟨_,_,_,_,rfl,first,next⟩ := seq_split run
  obtain ⟨u,start,hu⟩ := setup_run (s := s) (macros := macros) (m := m) frameFit
  obtain ⟨rfl,rfl,rfl⟩ := start.unique_of_deterministic (by decide) first
  obtain ⟨xs,len,valid,rfl,ht,hm⟩ := loop_decode space hu (Nat.zero_add _) next
  exact ⟨xs,len,valid,rfl,ht,hm⟩

/-- Native accepting traces of the compiled table correspond one-to-one to the exact
private path outcomes at its owned cells. The input choice tape, fetched addresses,
old words, signs, and chronological order are all retained by the correspondence. -/
theorem execute_directory_iff {s : Bank w} {m : Memory w}
    (frameFit : (pub 0).val + 15 < 2^w)
    (space : (Frame.ofMemory pub m).base + 3*(Frame.ofMemory pub m).count ≤ 2^w)
    {bits es} :
    TeamRAM.execute (callOwnedCells.program.fetch pub macros) ⟨0,s⟩ m bits = some es ↔
      es.map TeamRAM.Event.choices = bits ∧ ∃! xs : List (Option Outcome),
        xs.length = (Frame.ofMemory pub m).count ∧
        (Frame.ofMemory pub m).Admitted m macros 0 xs ∧
        es = setupTrace pub m ++ (Frame.ofMemory pub m).scanTrace m 0 xs := by
  rw [Code.execute_iff_runs (by decide : callOwnedCells.withoutAccept = true)]
  constructor
  · rintro ⟨⟨t,mt,run⟩,hb⟩
    obtain ⟨xs,len,valid,he,_,_⟩ := directory_decode frameFit space run
    refine ⟨hb,xs,⟨len,valid,he⟩,?_⟩
    rintro ys ⟨ly,vy,hy⟩
    exact Frame.scanTrace_inj _ _ _ vy valid (ly.trans len.symm)
      (List.append_cancel_left (hy.symm.trans he))
  · rintro ⟨hb,xs,⟨len,valid,rfl⟩,_⟩
    obtain ⟨t,run,_⟩ := directory_run (s := s) frameFit space len valid
    exact ⟨⟨t,m,run⟩,hb⟩

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
