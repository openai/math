import OAI.Computability.MultitapeWeakETH.TracePaths

/-! # The fixed-machine coarse trace lemma for timely successful paths -/

namespace OAI.Computability.MultitapeWeakETH

open PhysicalBlocks
open scoped Classical
noncomputable section

variable {M : Machine} {n T : ℕ}

private abbrev Seed (M : Machine) (T : ℕ) := Fin (T+1) → M.Choice

private def extend (s : Seed M T) (t : ℕ) : M.Choice := s ⟨min t T,by omega⟩

private theorem timely_path (s : Seed M T) (x y out : Word n) :
    timely M T s x y out ↔
      let p := frozenRun M (extend s) (initial M x y) (T+1)
      Accept p ∧ writes M (config p) out := by
  rw [timely_frozen_iff]
  change (∃ cfg, frozenRun M (extend s) (initial M x y) (T+1) = .halted cfg ∧ _) ↔ _
  cases h : frozenRun M (extend s) (initial M x y) (T+1) with
  | running p => simp [Accept,stopped]
  | halted p => simp [Accept,stopped,config]

private def Permits (mode : Option (Seed M T)) (s : Seed M T) :=
  ∀ f, mode = some f → s = f

private def admitted (mode : Option (Seed M T)) (t : ℕ) (c : M.Choice) :=
  ∀ f, mode = some f → c = extend f t

private def Eligible (mode : Option (Seed M T)) (x y : Word n) :=
  ∃ s out, Permits mode s ∧ timely M T s x y out ∧ 100 * errors out (lowProduct x y) ≤ n

private theorem select_mode (ret : retained M n T) :
    ∃ mode : Option (Seed M T), (mode.isSome = true ∨ Sound M) ∧
      threshold n ≤ density (Eligible mode : Word n → Word n → Prop) := by
  rcases ret with ⟨s,good⟩ | ⟨sound,good⟩
  · refine ⟨some s,Or.inl rfl,?_⟩
    have eq : (Eligible (some s) : Word n → Word n → Prop) =
        fun x y => ∃ out, timely M T s x y out ∧ 100*errors out (lowProduct x y) ≤ n := by
      funext x y
      apply propext
      constructor
      · rintro ⟨r,out,permit,ok,err⟩
        exact ⟨out,permit s rfl ▸ ok,err⟩
      · rintro ⟨out,ok,err⟩
        exact ⟨s,out,by simp [Permits],ok,err⟩
    rwa [eq]
  · refine ⟨none,Or.inr sound,?_⟩
    have eq (x y : Word n) : Eligible (M:=M) (T:=T) none x y ↔ ∃ s out, timely M T s x y out := by
      constructor
      · rintro ⟨s,out,_,valid,_⟩
        exact ⟨s,out,valid⟩
      · rintro ⟨s,out,valid⟩
        exact ⟨s,out,by simp [Permits],valid,by simp [sound n T s x y out valid,errors]⟩
    have events := funext (fun x => funext (fun y => propext (eq x y)))
    rwa [events]

private theorem unique_output {mode : Option (Seed M T)} (single : mode.isSome = true ∨ Sound M)
    {s r : Seed M T} (hs : Permits mode s) (hr : Permits mode r) {x y a d : Word n}
    (ha : timely M T s x y a) (hd : timely M T r x y d) : a = d := by
  rcases single with fixed | sound
  · cases mode with
    | none => simp at fixed
    | some f =>
      have same : r = s := (hr f rfl).trans (hs f rfl).symm
      subst r
      have aBits := ((timely_path s x y a).mp ha).2
      have dBits := ((timely_path s x y d).mp hd).2
      exact funext fun i => M.bit_injective ((aBits i).symm.trans (dBits i))
  · exact (sound _ _ _ _ _ _ ha).trans (sound _ _ _ _ _ _ hd).symm

private theorem admitted_path {mode : Option (Seed M T)} (s : Seed M T) (hs : Permits mode s) :
    ∀ t, admitted mode t (extend s t) :=
  fun t f h => congrArg (fun seed => extend seed t) (hs f h)

private theorem seed_of_path {mode : Option (Seed M T)} {x y out : Word n} (coins : ℕ → M.Choice)
    (ok : ∀ t, admitted mode t (coins t))
    (acc : Accept (frozenRun M coins (initial M x y) (T+1)))
    (writes : writes M (config (frozenRun M coins (initial M x y) (T+1))) out) :
    ∃ s, Permits mode s ∧ timely M T s x y out := by
  let s : Seed M T := fun i => coins i.val
  have agree t (ht : t < T+1) : extend s t = coins t := by simp [s,extend,min_eq_left (by omega : t ≤ T)]
  refine ⟨s,fun f h => funext (fun i => ?_), (timely_path s x y out).mpr ?_⟩
  · simpa [s,extend,min_eq_left (Nat.le_of_lt_succ i.isLt)] using ok i.val f h
  · rw [prefix_coins _ _ agree]
    exact ⟨acc,writes⟩

private theorem density_fiber {h e : ℕ} (event : Word n → Word n → Prop)
    (record : Word n × Word n → TraceCode h e) :
    ∃ code, ∀ good : Word n → Word n → Prop,
      (∀ x y, event x y → record (x,y) = code → good x y) →
      density event ≤ (3:ℝ)^(h*e) * density good := by
  let inputs := Finset.univ.filter (fun xy : Word n × Word n => event xy.1 xy.2)
  obtain ⟨code,best⟩ := most_frequent_trace inputs record
  refine ⟨code,fun good keep => ?_⟩
  have inclus : inputs.filter (fun xy => record xy = code) ⊆
      Finset.univ.filter (fun xy : Word n × Word n => good xy.1 xy.2) := by
    intro xy mem
    obtain ⟨input,recorded⟩ := Finset.mem_filter.mp mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,keep _ _ (Finset.mem_filter.mp input).2 recorded⟩
  have bound := best.trans (Nat.mul_le_mul_left _ (Finset.card_le_card inclus))
  unfold density
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by exact_mod_cast bound) (Nat.cast_nonneg _)

private theorem trace_loss {b : ℕ} (hb : 0 < b) (heads T : ℕ) (a : ℕ) (ha : 2*heads ≤ a) :
    (3:ℝ)^(heads * epochs T b) ≤ (2:ℝ) ^ ((a:ℝ)*(1+(T:ℝ)/b)) := by
  have div : ((T/b:ℕ):ℝ) ≤ (T:ℝ)/b :=
    (le_div_iff₀ (by exact_mod_cast hb)).mpr (by exact_mod_cast Nat.div_mul_le_self T b)
  calc
    _ ≤ (2^2:ℝ)^(heads * epochs T b) := by gcongr; norm_num
    _ = (2:ℝ)^((2*(heads * epochs T b):ℕ):ℝ) := by rw [Real.rpow_natCast]; exact (pow_mul ..).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have c : (2:ℝ)*heads ≤ a := by exact_mod_cast ha
      simp only [epochs,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = (2*(heads:ℝ))*(((T/b:ℕ):ℝ)+1) := by ring
        _ ≤ _ := by rw [add_comm (1:ℝ)]; gcongr

local instance (M : Machine) : Fintype M.Tapes := @Fintype.ofFinite _ M.tapesFinite

/-- Lemma 2.3, with binary wire alphabets and the finite controller of the
physical machine. Both machine-dependent constants are uniform in n and T. -/
theorem coarseTraceBound : CoarseTraceBound := by
  intro M
  let heads := Fintype.card M.Tapes
  let A := 3+2*heads
  refine ⟨degreeFactor M,A,by dsimp [A]; omega,0,fun n _ T ret => ?_⟩
  let b := n.sqrt+1
  have hb : 0 < b := Nat.succ_pos _
  obtain ⟨mode,single,thresholdOk⟩ := select_mode ret
  let event := Eligible mode (n:=n)
  let seed (xy : Word n × Word n) : Seed M T :=
    if he : event xy.1 xy.2 then he.choose else Classical.choice inferInstance
  let record (xy : Word n × Word n) := traceOf M hb T (extend (seed xy)) (initial M xy.1 xy.2)
  obtain ⟨code,keep⟩ := density_fiber event record
  let start i := ((initial M (n:=n) (fun _ => false) (fun _ => false)).tape i).pos
  let base := bases M start code
  let G := traceNetwork M n b T base
  obtain ⟨tables,sem⟩ := exists_trace_tables (n:=n) hb T base (admitted mode)
  have good : density event ≤ (3:ℝ)^(heads * epochs T b) * density (G.Good tables) := by
    apply keep
    intro x y he follows
    let s := seed (x,y)
    have spec : ∃ out, Permits mode s ∧ timely M T s x y out ∧ 100*errors out (lowProduct x y) ≤ n := by
      simpa only [s,seed,dite_eq_left he] using he.choose_spec
    obtain ⟨out,permit,timelyOut,acc⟩ := spec
    have hs : (fun i => ((initial M x y).tape i).pos) = start :=
      funext ((initial_controller M x y (fun _ => false) (fun _ => false)).2)
    have fits : Follows b T base (extend s) (initial M x y) := by
      intro j hj
      have facts := traceOf_fits M hb T (extend s) (initial M x y) hj
      change record (x,y) = code at follows
      change traceOf M hb T (extend s) (initial M x y) = code at follows
      rwa [hs,follows] at facts
    obtain ⟨accept,write⟩ := (timely_path s x y out).mp timelyOut
    refine ⟨out,(sem x y out).mpr (history_of_path hb base _ x y out _ (admitted_path s permit)
      fits accept write),fun other hother => ?_,acc⟩
    have initFits := fits 0 (Nat.zero_le _)
    simp only [RunAt,cut,Nat.zero_mul,Nat.zero_min,frozenRun] at initFits
    obtain ⟨f,ok,ha,hw⟩ := path_of_history hb base _ ⟨extend s,admitted_path s permit⟩ x y other initFits
      ((sem x y other).mp hother)
    obtain ⟨r,hr,same⟩ := seed_of_path f ok ha hw
    exact unique_output single hr permit same timelyOut
  refine ⟨G,traceNetwork_bounded ..,?_,tables,?_⟩
  · have size : G.vertices*b ≤ A*(b+T+n) :=
      (traceNetwork_size M n b T base).trans (Nat.mul_le_mul_right _ (by dsimp [A]; omega))
    exact_mod_cast size
  · have bound := thresholdOk.trans good
    have large := trace_loss hb heads T A (by dsimp [A]; omega)
    have pos : (0:ℝ) ≤ density (G.Good tables) := by unfold density; positivity
    rw [Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    apply (div_le_iff₀ (by positivity)).mpr
    rw [mul_comm]
    exact bound.trans (mul_le_mul_of_nonneg_right large pos)

end
end OAI.Computability.MultitapeWeakETH
