import OAI.Computability.BorderVNP.TransmissionRowSafety
import OAI.Computability.BorderVNP.TransmissionTableChoices
import OAI.Computability.BorderVNP.TransmissionInverseDispatch

/-! # Physical choice multiplicities and acceptance tests for one directory row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open private ready_of_allowed from OAI.Computability.BorderVNP.TransmissionProgram

variable {w : ℕ}

private theorem choiceBits_eq {row : Range w} {s : Bank w} {self : Word w} {role : Option Role}
    {bits : ℕ → Bool} (hr : rangeBank s = row) (sel : row.selected self = some role) :
    row.choiceBits self bits = optionBits role (s 11).val bits := by
  have hw : row.width = s 11 := (congrArg Range.width hr).symm
  cases role with
  | none => simp [Range.choiceBits, sel, optionBits]
  | some mode => simp [Range.choiceBits, sel, optionBits, Role.prefixBits, hw]

/-- A prescribed permitted row assignment executes with exactly its ordered choice list. -/
theorem directory_step_bits {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {m : Memory w} {s : Bank w} {self base count ord : Word w} {i : ℕ} {r : Range w}
    (hs : AtRow self base count ord i s) (hi : i < count.val)
    (table : rangeAt m (cursorAt base 7 i) (cursorAt ord 1 i) = r)
    (bits : ℕ → Bool) (ok : r.allowed self pub m bits) :
    ∃ es t, Runs pub macros step s m es t (r.apply self pub m bits) ∧
      es.flatMap TeamRAM.Event.choices = r.choiceBits self bits ∧
      AtRow self base count ord (i+1) t ∧ traceCost es ≤ 19 + decision.depth + r.teamCost self := by
  obtain ⟨es,a,load,hc,ha,ha3,ha6,hoff,hkeep⟩ := loadRange_runs pub macros s m hs.one hs.zero
  have hr : rangeBank a = r := by rwa [hs.baseAddr, hs.ordinal, table] at ha
  have ateam := (hkeep 0 (by decide) (by decide)).trans hs.team
  have aone := (hkeep 1 (by decide) (by decide)).trans hs.one
  have azero := (hkeep 2 (by decide) (by decide)).trans hs.zero
  obtain ⟨role,sel,hready⟩ := ready_of_allowed ok hr ateam aone azero
  obtain ⟨fs,b,dispatch,bs,low,hf⟩ := Decision.run_bits pub macros a m bits
    ((Range.role_eq hr ateam aone azero).trans sel) aone hoff hready
  rw [decision_code, Range.finished_eq hr ateam aone azero sel] at dispatch
  let t := Function.update b 5 (b 5 + b 1)
  have inc : Runs pub macros (.binary .add 5 5 1) b (r.apply self pub m bits) [tick w] t
      (r.apply self pub m bits) := Runs.localStep _ rfl rfl
  refine ⟨_,t,load.seq (dispatch.seq inc),?_,?_,?_⟩
  · have hb := Pins.noChoices load (by decide)
    simp only [List.flatMap_append, hb, bs, tick, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil]
    exact (choiceBits_eq hr sel).symm
  · have same (j : Reg) (hj : j.val < 16) (h5 : j ≠ 5) : t j = a j :=
      (Function.update_of_ne h5 ..).trans (low j hj)
    refine ⟨(same 0 (by decide) (by decide)).trans ateam, (same 1 (by decide) (by decide)).trans aone,
      (same 2 (by decide) (by decide)).trans azero, ?_, ?_, ?_, ?_⟩
    · rw [same 3 (by decide) (by decide), ha3, hs.baseAddr]
      simp only [cursorAt, add_nsmul, one_nsmul, add_assoc]
    · exact (same 4 (by decide) (by decide)).trans ((hkeep 4 (by decide) (by decide)).trans hs.bound)
    · have h5 := hkeep 5 (by decide) (by decide)
      have hfit : i+1 < 2^w := (Nat.succ_le_of_lt hi).trans_lt count.isLt
      simp only [t,Function.update_self,low 5 (by decide),low 1 (by decide),aone,h5,
        Fin.val_add, hs.index]
      have hw : 1 < 2^w := by omega
      simp [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hfit]
    · rw [same 6 (by decide) (by decide), ha6, hs.ordinal]
      simp only [cursorAt, add_nsmul, one_nsmul, add_assoc]
  · have hp : r.teamCost self = payloadCost role (a 11).val := by
      rw [Range.teamCost, sel, ← congrArg Range.width hr]
      rfl
    rw [cost_append,cost_append,hc,hp]
    change 17 + (traceCost fs + 1) ≤ _
    omega

private theorem row_assignment {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {m : Memory w} {s : Bank w} {self base count ord : Word w} {i : ℕ} {row : Range w}
    (hs : AtRow self base count ord i s)
    (table : rangeAt m (cursorAt base 7 i) (cursorAt ord 1 i) = row)
    (safe : row.arithmeticSafe self pub m) {es t mt} (r : Runs pub macros step s m es t mt) :
    ∃ bits : ℕ → Bool, row.allowed self pub m bits ∧
      es.flatMap TeamRAM.Event.choices = row.choiceBits self bits := by
  change Runs _ _ (.seq loadRange (.seq dispatch (.binary .add 5 5 1))) _ _ _ _ _ at r
  cases r with
  | atom ha => cases ha
  | @seq _ _ _ _ ls a ma rs _ _ load tail =>
    obtain ⟨fs,u,ref,_,hr,_,_,hoff,hlow⟩ := loadRange_runs pub macros s m hs.one hs.zero
    obtain ⟨etr,eb,em⟩ := ref.unique_of_deterministic (by decide) load
    subst a; subst ma
    have hrow : rangeBank u = row := by rwa [hs.baseAddr,hs.ordinal,table] at hr
    have hteam := (hlow 0 (by decide) (by decide)).trans hs.team
    have h1 := (hlow 1 (by decide) (by decide)).trans hs.one
    have h0 := (hlow 2 (by decide) (by decide)).trans hs.zero
    cases tail with
    | atom ha => cases ha
    | @seq _ _ _ _ gs v mv is _ _ dispatchRun inc =>
      rw [← decision_code] at dispatchRun
      obtain ⟨role,bits,sel,ok,_,bs,_,_⟩ := Decision.sound decision pub macros u m h1 hoff
        (Range.safeScan safe hrow hteam h1 h0) dispatchRun
      have selected := (Range.role_eq hrow hteam h1 h0).symm.trans sel
      refine ⟨bits,Range.allowed_of_ready safe hrow hteam h1 h0 selected ok,?_⟩
      rw [choiceBits_eq hrow selected]
      simp only [List.flatMap_append, Pins.noChoices load (by decide), Pins.noChoices inc (by decide),
        List.nil_append, List.append_nil,bs]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- The entire transmission row uses the native instruction table. -/
theorem directory_step_native : ∀ pc, step.program.tag pc = .native := by decide

/-- Every returned directory row decodes a permitted assignment, including the actual
sender comparison. Its trace, register advance, memory and cost agree with replay of
that assignment. -/
theorem directory_step_sound {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {m : Memory w} {s : Bank w} {self base count ord : Word w} {i : ℕ} {row : Range w}
    (hs : AtRow self base count ord i s) (hi : i < count.val)
    (table : rangeAt m (cursorAt base 7 i) (cursorAt ord 1 i) = row)
    (safe : row.arithmeticSafe self pub m) {es t mt} (r : Runs pub macros step s m es t mt) :
    ∃ bits : ℕ → Bool, row.allowed self pub m bits ∧ mt = row.apply self pub m bits ∧
      es.flatMap TeamRAM.Event.choices = row.choiceBits self bits ∧
      AtRow self base count ord (i+1) t ∧ traceCost es ≤ 19 + decision.depth + row.teamCost self := by
  obtain ⟨bits,ok,bs⟩ := row_assignment hs table safe r
  obtain ⟨fs,u,rr,bf,hr,hc⟩ := directory_step_bits (macros := macros) hs hi table bits ok
  have he : fs.flatMap TeamRAM.Event.choices ++ [] = es.flatMap TeamRAM.Event.choices ++ [] := by rw [bf,bs]
  obtain ⟨et,eb,em⟩ := DiagonalResidueRAM.unique_returns directory_step_native rr r he
  exact ⟨bits,ok,em.symm,bs,eb ▸ hr,et ▸ hc⟩

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
