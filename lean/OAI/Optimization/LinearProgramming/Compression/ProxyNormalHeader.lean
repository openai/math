import OAI.Optimization.LinearProgramming.Compression.ProxyCacheCounters
import OAI.Optimization.LinearProgramming.Compression.ProxyInputMove
import OAI.Optimization.LinearProgramming.Compression.ParameterRAM

/-! Normal numerical entry point for the online service's isolated cache and bit solver. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM GeneratorTable

/-- All natural numbers counted during the two scalar-to-address transfers fit
the checked size envelope of the parameter initializer itself. -/
theorem proxyParameter_nat_safe (p : Polynomial ℕ) (N H : ℕ) (hH : parameterBits p N ≤ H)
    (j : ℕ) (hj : j ≤ parameterCounterCap p N) : ratBits (j:ℚ) ≤ H := by
  have hs := parameter_nat_bits j
  unfold parameterBits at hH
  omega

theorem proxyParameter_exponents_safe (p : Polynomial ℕ) (N H : ℕ) (hH : parameterBits p N ≤ H)
    (j : ℕ) (hj : j ≤ max (p.eval N) (100*(N+1)^3+7)) : ratBits (j:ℚ) ≤ H := by
  apply proxyParameter_nat_safe p N H hH
  apply hj.trans
  apply max_le <;> unfold parameterCounterCap <;> simp only [parameterGridExponent_eval] <;> omega

private def normalRememberPlan : List AddressSet := [.read 4 0,.read 5 1,.read 6 2,.read 7 3]
private def normalPublishPlan : List AddressSet :=
  [.read 90 4,.read 91 5,.read 92 6,.read 93 7,
   .read 102 4,.read 103 5,.read 104 6,.read 105 7,.read 4 2,.next 0 5,.read 3 5,.fix 60 0] ++
    List.replicate 8 (.next 3 3)

/-- Preserve the normal scalar input before borrowing the low bank. Evaluate the
fixed parameter polynomials at the supplied dimension and publish the cache operands
and the four driver metadata words. -/
def normalProxyHeader (cs : List ℕ) : Block :=
  .seq moveProxyInputBlock <|
  .seq (addressPlan normalRememberPlan) <|
  .seq (parameterBlockFromCoefficients cs) <|
  .seq (addressPlan normalPublishPlan) proxyExponentCounters

def normalProxyHeaderSteps (cs : List ℕ) (N g : ℕ) : ℕ :=
  (7*g+15) + (4 + (parameterStepsFromCoefficients cs N +
    (20 + ((4*parameterCoefficientValue cs N+4)+(4*(100*(N+1)^3+7)+4)))))

/-- The source vector is physically disjoint from the initializer's scalar workspace.
The bit driver's dimension, generator count, membership bit and rank occupy addresses
90 through 93 at entry and 102 through 105 throughout subsequent signed queries. -/
structure NormalProxyHeader {K : Type*} (N g member rank fuel : ℕ) (s t : Memory K) : Prop where
  count : t.index 0 = g+1
  cutoff : t.index 1 = fuel
  precision : t.index 2 = 100*(N+1)^3+7
  base : t.index 3 = g+8
  protectedEnd : t.index 4 = (8+(100*(N+1)^3+7)+1)+fuel+1
  cacheCounter : t.index 60 = 0
  dimension : t.index 90 = N
  generators : t.index 91 = g
  membership : t.index 92 = member
  position : t.index 93 = rank
  stableDimension : t.index 102 = N
  stableGenerators : t.index 103 = g
  stableMembership : t.index 104 = member
  stablePosition : t.index 105 = rank
  values : ∀ i ≤ g, t.data (g+8+i) = s.data i

private theorem rememberLayout {K : Type*} (s : Memory K) :
    let t := applyPlan normalRememberPlan s
    t.index 0 = s.index 0 ∧ t.index 4 = s.index 0 ∧ t.index 5 = s.index 1 ∧
      t.index 6 = s.index 2 ∧ t.index 7 = s.index 3 ∧ t.data = s.data := by
  simp [normalRememberPlan,applyPlan,AddressSet.apply]

private theorem publishLayout {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (hs : s.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) (addressPlan normalPublishPlan) s 20 t ∧
    t.index 0 = s.index 5+1 ∧ t.index 3 = s.index 5+8 ∧ t.index 4 = s.index 2 ∧
      t.index 60 = 0 ∧ t.index 90 = s.index 4 ∧ t.index 91 = s.index 5 ∧
      t.index 92 = s.index 6 ∧ t.index 93 = s.index 7 ∧
      t.index 102 = s.index 4 ∧ t.index 103 = s.index 5 ∧ t.index 104 = s.index 6 ∧
      t.index 105 = s.index 7 ∧ t.data = s.data := by
  let t := applyPlan normalPublishPlan s
  have actions : Block.Eval (Memory.AllData P) (addressPlan normalPublishPlan) s 20 t :=
    addressPlan_spec (fun f => ∀ j, P (f j)) _ s hs
  refine ⟨t,actions,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,applyPlan_data _ _⟩
  all_goals simp [t,normalPublishPlan,applyPlan,AddressSet.apply]

/-- The normal metadata compiler runs directly on arbitrary field-valued magnitudes.
Only its integer counters and powers of two need a scalar-policy premise. -/
theorem normalProxyHeader_generic {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (cs : List ℕ) (p : Polynomial ℕ) (heval : ∀ n, parameterCoefficientValue cs n = p.eval n)
    (N g member rank : ℕ) (s : Memory K) (P : K → Prop)
    (hn : s.index 0 = N) (hg : s.index 1 = g) (hm : s.index 2 = member) (hrank : s.index 3 = rank)
    (hs : s.AllData P) (hNat : ∀ j≤parameterCounterCap p N, P (j:K))
    (hPow : ∀ j≤parameterCounterCap p N, P ((2:K)^j)) :
    ∃ t, Block.Eval (Memory.AllData P) (normalProxyHeader cs) s (normalProxyHeaderSteps cs N g) t ∧
      NormalProxyHeader N g member rank (p.eval N) s t := by
  let fuel := p.eval N
  let prec := 100*(N+1)^3+7
  obtain ⟨a,ea,copied,_,ai,_⟩ := moveProxyInputBlock_spec P s g hg hs
  have keep (i : ℕ) (hi : i < 4) : a.index i = s.index i :=
    ai i (by omega) (by omega) (by omega) (by omega)
  let b := applyPlan normalRememberPlan a
  have eb : Block.Eval (Memory.AllData P) (addressPlan normalRememberPlan) a 4 b :=
    addressPlan_spec (fun f => ∀ j, P (f j)) _ a ea.safe_end
  obtain ⟨b0,b4,b5,b6,b7,bdata⟩ := rememberLayout a
  have bn : b.index 0 = N := b0.trans ((keep 0 (by decide)).trans hn)
  obtain ⟨c,ec,pars,fr⟩ := parameterBlockFromCoefficients_generic cs p heval b N bn P eb.safe_end hNat hPow
  have ci (i : ℕ) (hlo : 4 ≤ i) (hi : i < 8) : c.index i = b.index i :=
    fr.addresses i (by omega) (by omega) (by omega) (Or.inl hi)
  have c4 : c.index 4 = N := (ci 4 (by decide) (by decide)).trans (b4.trans ((keep 0 (by decide)).trans hn))
  have c5 : c.index 5 = g := (ci 5 (by decide) (by decide)).trans (b5.trans ((keep 1 (by decide)).trans hg))
  have c6 : c.index 6 = member := (ci 6 (by decide) (by decide)).trans (b6.trans ((keep 2 (by decide)).trans hm))
  have c7 : c.index 7 = rank := (ci 7 (by decide) (by decide)).trans (b7.trans ((keep 3 (by decide)).trans hrank))
  obtain ⟨d,ed,d0,d3,d4,d60,d90,d91,d92,d93,d102,d103,d104,d105,dd⟩ :=
    publishLayout P c ec.safe_end
  have h1 : P 1 := by simpa only [Nat.cast_one] using hNat 1 (by unfold parameterCounterCap; omega)
  have val (j : ℕ) (hj : j≤max fuel prec) : P (j:K) := by
    apply hNat j (hj.trans _)
    apply max_le <;> dsimp [fuel,prec,parameterCounterCap] <;> simp only [parameterGridExponent_eval] <;> omega
  obtain ⟨t,et,t1,t2,ti,td⟩ := proxyExponentCounters_spec P d fuel prec
    ((congrFun dd 4).trans pars.cutoffExponent) ((congrFun dd 3).trans pars.gridExponent)
    ed.safe_end h1 val
  refine ⟨t,?_,?_⟩
  · simpa only [normalProxyHeader,normalProxyHeaderSteps,heval N] using ea.seq (eb.seq (ec.seq (ed.seq et)))
  · constructor
    · exact (ti 0 (by decide) (by decide)).trans (d0.trans (congrArg (·+1) c5))
    · exact t1
    · exact t2
    · exact (ti 3 (by decide) (by decide)).trans (d3.trans (congrArg (·+8) c5))
    · exact (ti 4 (by decide) (by decide)).trans (d4.trans (by simpa only [parameterGridExponent_eval] using pars.tapeEnd))
    · exact (ti 60 (by decide) (by decide)).trans d60
    · exact (ti 90 (by decide) (by decide)).trans (d90.trans c4)
    · exact (ti 91 (by decide) (by decide)).trans (d91.trans c5)
    · exact (ti 92 (by decide) (by decide)).trans (d92.trans c6)
    · exact (ti 93 (by decide) (by decide)).trans (d93.trans c7)
    · exact (ti 102 (by decide) (by decide)).trans (d102.trans c4)
    · exact (ti 103 (by decide) (by decide)).trans (d103.trans c5)
    · exact (ti 104 (by decide) (by decide)).trans (d104.trans c6)
    · exact (ti 105 (by decide) (by decide)).trans (d105.trans c7)
    · intro i hi
      exact (td _ (by omega) (by omega)).trans ((congrFun dd _).trans
        ((fr.scalarsFromSeven _ (by omega)).trans ((congrFun bdata _).trans (copied i hi))))

theorem normalProxyHeader_spec (cs : List ℕ) (p : Polynomial ℕ)
    (heval : ∀ n, parameterCoefficientValue cs n = p.eval n)
    (N g member rank H : ℕ) (s : Memory ℚ)
    (hn : s.index 0 = N) (hg : s.index 1 = g) (hm : s.index 2 = member) (hrank : s.index 3 = rank)
    (hH : parameterBits p N ≤ H) (hs : s.AllData (fun q => ratBits q ≤ H)) :
    ∃ t, Block.Eval (Memory.AllData fun q => ratBits q ≤ H)
      (normalProxyHeader cs) s (normalProxyHeaderSteps cs N g) t ∧
      NormalProxyHeader N g member rank (p.eval N) s t := by
  apply normalProxyHeader_generic cs p heval N g member rank s (fun x => ratBits x≤H) hn hg hm hrank hs
  · exact proxyParameter_nat_safe p N H hH
  · intro j hj
    exact (parameter_pow_bits j).trans (by unfold parameterBits at hH; omega)

/-- Standard entry interface. The caller can supply its ordinary `List.ofFn` tape, and
all exponents and metadata are obtained inside the finite program. -/
theorem normalProxyHeader_on_input (cs : List ℕ) (p : Polynomial ℕ)
    (heval : ∀ n, parameterCoefficientValue cs n = p.eval n)
    (N g rank B H : ℕ) (member : Bool) (mag : Fin (g+1) → ℚ)
    (hmag : ∀ i, ratBits (mag i) ≤ B) (hB : B ≤ H) (hH : parameterBits p N ≤ H) :
    let s := (start [N,g,member.toNat,rank] (List.ofFn mag)).memory
    ∃ t, Block.Eval (Memory.AllData fun q => ratBits q ≤ H)
        (normalProxyHeader cs) s (normalProxyHeaderSteps cs N g) t ∧
      NormalProxyHeader N g member.toNat rank (p.eval N) s t ∧
      ∀ i : Fin (g+1), t.data (g+8+i.val) = mag i := by
  intro s
  have input (i : Fin (g+1)) : s.data i.val = mag i := by
    change ((List.ofFn mag)[i.val]?).getD 0 = mag i
    rw [List.getElem?_ofFn, dite_eq_left i.isLt]
    rfl
  have safe : s.AllData (fun q => ratBits q ≤ H) := by
    intro i
    by_cases hi : i < g+1
    · rw [input ⟨i,hi⟩]
      exact (hmag ⟨i,hi⟩).trans hB
    · change ratBits ((List.ofFn mag)[i]?.getD 0) ≤ H
      rw [List.getElem?_eq_none (by simpa using (Nat.le_of_not_gt hi)),Option.getD_none]
      rw [show ratBits 0 = 3 by decide]
      exact (show 3 ≤ ratBits (mag 0) by unfold ratBits; omega).trans ((hmag 0).trans hB)
  obtain ⟨t,ev,ok⟩ := normalProxyHeader_spec cs p heval N g member.toNat rank H s
    (by simp [s,State.memory,start]) (by simp [s,State.memory,start])
    (by simp [s,State.memory,start]) (by simp [s,State.memory,start]) hH safe
  exact ⟨t,ev,ok,fun i => (ok.values i.val (by omega)).trans (input i)⟩

/-- Starting from just the dimension, generator metadata, and actual magnitudes, the same
finite program constructs both precision words and preserves every input value at its
published address. No restriction on the field values is required. -/
theorem normalProxyHeader_on_input_field {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (cs : List ℕ) (p : Polynomial ℕ) (heval : ∀ n, parameterCoefficientValue cs n=p.eval n)
    (N g rank : ℕ) (member : Bool) (mag : Fin (g+1) → K) :
    let s := (start [N,g,member.toNat,rank] (List.ofFn mag)).memory
    ∃ t, Block.Eval (Memory.AllData fun _ : K => True) (normalProxyHeader cs) s
      (normalProxyHeaderSteps cs N g) t ∧ NormalProxyHeader N g member.toNat rank (p.eval N) s t ∧
      ∀ i : Fin (g+1), t.data (g+8+i.val)=mag i := by
  intro s
  obtain ⟨t,run,h⟩ := normalProxyHeader_generic cs p heval N g member.toNat rank s (fun _ => True)
    rfl rfl rfl rfl (fun _ => True.intro) (fun _ _ => True.intro) (fun _ _ => True.intro)
  refine ⟨t,run,h,?_⟩
  intro i
  rw [h.values i (by omega)]
  change ((List.ofFn mag)[i.val]?).getD 0 = mag i
  rw [List.getElem?_ofFn, dite_eq_left i.isLt]
  rfl

end Compression
end LinearProgramming
end Optimization
end OAI
