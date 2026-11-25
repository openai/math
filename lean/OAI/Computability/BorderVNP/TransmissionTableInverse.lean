import OAI.Computability.BorderVNP.TransmissionInverseRow

/-! # Recovering the permitted bit assignment from a returning transmission program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ}

/-- Every returning physical traversal determines a permitted assignment to its
locally shared wires. Arithmetic safety and the directory contents are input conditions;
the comparison with each remote sender's source word follows from the return. -/
theorem table_sound (rows : ℕ → Range w) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w)
    (table : ∀ bits : ℕ → ℕ → Bool, ∀ i < (directoryFrame pub m 13).val,
      rangeAt (tableMemory rows (directoryFrame pub m 0) pub m bits i)
        (cursorAt (directoryFrame pub m 12) 7 i) (cursorAt (directoryFrame pub m 20) 1 i) = rows i)
    (safe : ∀ bits : ℕ → ℕ → Bool, ∀ i < (directoryFrame pub m 13).val,
      (rows i).arithmeticSafe (directoryFrame pub m 0) pub
        (tableMemory rows (directoryFrame pub m 0) pub m bits i))
    {es t mt} (run : Runs pub macros transmitRanges s m es t mt) :
    ∃ bits : ℕ → ℕ → Bool,
      (∀ i < (directoryFrame pub m 13).val, (rows i).allowed (directoryFrame pub m 0) pub
        (tableMemory rows (directoryFrame pub m 0) pub m bits i) (bits i)) ∧
      mt = tableMemory rows (directoryFrame pub m 0) pub m bits (directoryFrame pub m 13).val ∧
      es.flatMap TeamRAM.Event.choices = tableChoiceBits rows (directoryFrame pub m 0) bits
        (directoryFrame pub m 13).val := by
  let self := directoryFrame pub m 0
  let base := directoryFrame pub m 12
  let count := directoryFrame pub m 13
  let ord := directoryFrame pub m 20
  let M := tableMemory rows self pub m
  let choices := tableChoiceBits rows self
  let Inv (bs : List Bool) (t : Bank w) (mt : Memory w) :=
    ∃ i ≤ count.val, ∃ bits : ℕ → ℕ → Bool, AtRow self base count ord i t ∧
      mt = M bits i ∧ bs = choices bits i ∧ ∀ j < i, (rows j).allowed self pub (M bits j) (bits j)
  have next {bs a ma fs b mb} (h : Inv bs a ma) (guard : a 5 < a 4)
      (r : Runs pub macros step a ma fs b mb) : Inv (bs ++ fs.flatMap TeamRAM.Event.choices) b mb := by
    obtain ⟨i, _, bits, frame, rfl, rfl, before⟩ := h
    have hi : i < count.val := by
      change (a 5).val < (a 4).val at guard
      rwa [frame.index, frame.bound] at guard
    obtain ⟨rowBits, ok, hm, hb, frame', _⟩ := directory_step_sound frame hi (table bits i hi) (safe bits i hi) r
    let bits' := Function.update bits i rowBits
    have previous {j : ℕ} (hj : j ≤ i) : M bits' j = M bits j :=
      tableMemory_congr rows self pub m (fun k hk => Function.update_of_ne (by omega : k ≠ i) ..)
    have stream : choices bits' i = choices bits i :=
      tableChoiceBits_congr rows self (fun k hk => Function.update_of_ne (Nat.ne_of_lt hk) ..)
    have current : bits' i = rowBits := Function.update_self ..
    refine ⟨i+1, hi, bits', frame', ?_, ?_, ?_⟩
    · change mb = (rows i).apply self pub (M bits' i) (bits' i)
      rw [previous le_rfl, current, hm]
    · change choices bits i ++ fs.flatMap TeamRAM.Event.choices =
        choices bits' i ++ (rows i).choiceBits self (bits' i)
      rw [stream, current, hb]
    · intro j hj
      rw [previous (by omega)]
      by_cases he : j = i
      · subst j; rwa [current]
      · rw [show bits' j = bits j from Function.update_of_ne he ..]
        exact before j (by omega)
  change Runs _ _ (.seq setup (.whileLt 5 4 step)) _ _ _ _ _ at run
  cases run with
  | atom ha => cases ha
  | @seq _ _ _ _ fs a ma gs _ _ rs loop =>
    obtain ⟨es,u,rs',_,hself,h1,h0,h5,h3,h4,h6⟩ := setup_runs pub macros s m
    obtain ⟨_,ha,hm⟩ := rs'.unique_of_deterministic (by decide) rs
    subst a; subst ma
    have frame : AtRow self base count ord 0 u :=
      ⟨hself,h1,h0,by simpa [cursorAt,base] using h3,h4,by simp [h5],by simpa [cursorAt,ord] using h6⟩
    have init : Inv [] u m := ⟨0, Nat.zero_le _, fun _ _ => false, frame, rfl, rfl, by simp⟩
    obtain ⟨⟨i, hle, bits, frame', hmt, hstream, permitted⟩, hexit⟩ :=
      loop.while_choices_invariant 5 4 step Inv next rfl [] init
    have heq : i = count.val := by
      change ¬(t 5).val < (t 4).val at hexit
      rw [frame'.index, frame'.bound] at hexit
      omega
    subst i
    refine ⟨bits, permitted, hmt, ?_⟩
    rw [List.flatMap_append, Pins.noChoices rs (by decide)]
    exact hstream

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
