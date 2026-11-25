import OAI.Computability.BorderVNP.DiagonalResidueRAMReplay
import OAI.Computability.BorderVNP.RoutingISADeterministic

/-! # Exact native path multiplicity of the advised residue-entry circuit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM VPVNP.BooleanTranscript RoutingISA

variable {w u v k : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
variable (base advice : ℕ) (c : Circuit (Fin u ⊕ Fin v) k) (x : Fin u → Bool)
variable (s : Bank w) (m : Memory w)
variable (hf : (frame base advice c).fits w) (hs : (frame base advice c).loaded s)
variable (hx : queryLoaded m base x) (ha : hasAdvice m base advice c)

include hf hs hx ha in
private theorem eval_cover {es t mt} (r : Runs pub macros evaluate s m es t mt) :
    ∃ y : Fin v → Bool, TraceOK es (List.ofFn y) (6*v+14*k+11) ∧
      t 42 = wordBit w (c.eval (Sum.elim x y)) ∧ t 38 = 1 := by
  let read := es.flatMap TeamRAM.Event.choices
  let stream := read ++ List.replicate v false
  have hlen : v ≤ stream.length := by simp [stream]
  let y (i : Fin v) := stream[i.val]'(i.isLt.trans_le hlen)
  have cut : List.ofFn y = stream.take v := by
    apply List.ext_getElem (by simp [hlen])
    intro i _ _
    simp [y]
  obtain ⟨z,mz,⟨fs,rr,tr⟩,hbit,hone⟩ :=
    evaluate_checked pub macros base advice c x y s m hf hs hx ha
  have ht : es.flatMap TeamRAM.Event.choices ++ List.replicate v false =
      fs.flatMap TeamRAM.Event.choices ++ stream.drop v := by
    rw [tr.2.1,cut,List.take_append_drop]
  obtain ⟨rfl,rfl,rfl⟩ := unique_returns (c := evaluate) (by decide) r rr ht
  exact ⟨y,tr,hbit,hone⟩

include hf hs hx ha in
/-- Every native accepting trace comes from one accepting verifier witness;
its signed weight is positive and its exact tick count is independent of the
witness. The result covers every native tape, including malformed blocks. -/
theorem reader_complete {tape es} (ok : TeamRAM.execute (machine.fetch pub macros)
    ⟨0,s⟩ m tape = some es) :
    ∃ y : Fin v → Bool, c.eval (Sum.elim x y) = true ∧ TraceOK es (List.ofFn y) (ticks k v) := by
  obtain ⟨⟨z,mz,run⟩,_⟩ := (Code.execute_iff_runs (c := reader) (by decide)).mp ok
  change Runs pub macros (.seq evaluate (.ifEq 42 38 .nop .reject)) s m es z mz at run
  cases run with
  | atom h => contradiction
  | @seq _ _ _ _ ds t mt fs _ _ ev guard =>
    obtain ⟨y,tr,hbit,hone⟩ := eval_cover pub macros base advice c x s m hf hs hx ha ev
    have equal : t 42 = t 38 := by
      by_contra hn
      cases guard with
      | atom h => contradiction
      | ifEq branch =>
        rw [ite_eq_right hn] at branch
        cases branch with
        | atom h => contradiction
    have bit : c.eval (Sum.elim x y) = true := by
      cases he : c.eval (Sum.elim x y) with
      | true => rfl
      | false =>
        have bound := hf.1.trans_lt ((Nat.le_add_right advice _).trans_lt hf.2)
        change base + 2 + u + v + k < 2^w at bound
        have hh : 1 < 2^w := by omega
        rw [hbit,hone,he] at equal
        have h₀ : (wordBit w false).val = 0 := wordBit_val hh false
        have h₁ : (1 : Word w).val = 1 := word_val w 1 hh
        exact False.elim (by rw [equal,h₁] at h₀; contradiction)
    have good : Runs pub macros (.ifEq 42 38 .nop .reject) t mt [tick w,tick w] t mt :=
      .ifEq (by rw [ite_eq_left equal]; exact Runs.localStep mt rfl rfl)
    obtain ⟨rfl,rfl,rfl⟩ := good.unique_of_deterministic (by decide) guard
    have endTrace : TraceOK [tick w,tick w] [] 2 := by simp [TraceOK,tick]
    exact ⟨y,bit,by simpa [ticks,Nat.add_assoc] using tr.append endTrace⟩

/-- The actual accepting event lists, including every shared load, store
and private binary guess. -/
def Paths (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) :=
  {es : List (TeamRAM.Event w) //
    TeamRAM.execute (machine.fetch pub macros) ⟨0,s⟩ m (es.map TeamRAM.Event.choices) = some es}

/-- The accepted native event traces are in bijection with the accepting
Boolean witnesses, even when different branch choices coincide later. -/
noncomputable def witnessEquiv : {y : Fin v → Bool // c.eval (Sum.elim x y) = true} ≃ Paths pub macros s m := by
  classical
  let path (y : {y : Fin v → Bool // c.eval (Sum.elim x y) = true}) :=
    reader_accepts pub macros base advice c x y.val s m hf hs hx ha y.property
  let f (y : {y : Fin v → Bool // c.eval (Sum.elim x y) = true}) : Paths pub macros s m :=
    ⟨(path y).choose,(path y).choose_spec.1⟩
  have ht (y) : TraceOK (f y).val (List.ofFn y.val) (ticks k v) := (path y).choose_spec.2
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b h
    have hb := (ht a).2.1.symm.trans ((congrArg (fun z : Paths pub macros s m =>
      z.val.flatMap TeamRAM.Event.choices) h).trans (ht b).2.1)
    exact Subtype.ext (List.ofFn_injective hb)
  · intro p
    obtain ⟨y,hy,tr⟩ := reader_complete pub macros base advice c x s m hf hs hx ha p.property
    let a : {y : Fin v → Bool // c.eval (Sum.elim x y) = true} := ⟨y,hy⟩
    refine ⟨a,Subtype.ext ?_⟩
    obtain ⟨⟨z,mz,h₁⟩,_⟩ := (Code.execute_iff_runs (c := reader) (by decide)).mp (f a).property
    obtain ⟨⟨z',mz',h₂⟩,_⟩ := (Code.execute_iff_runs (c := reader) (by decide)).mp p.property
    exact (unique_returns (c := reader) (by decide) h₁ h₂ (tail := []) (tail' := [])
      (by rw [(ht a).2.1,tr.2.1])).1

include hf hs hx ha in
/-- The number of native positive-weight accepting paths is the integer sum
of the bit verifier over its Boolean witnesses. -/
theorem native_count :
    (Nat.card (Paths pub macros s m) : ℤ) =
      ∑ y : Fin v → Bool, if c.eval (Sum.elim x y) then (1 : ℤ) else 0 := by
  classical
  let e := witnessEquiv pub macros base advice c x s m hf hs hx ha
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Finset.sum_boole,
    ← Fintype.card_subtype]

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
