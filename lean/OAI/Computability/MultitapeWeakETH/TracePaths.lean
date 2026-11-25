import OAI.Computability.MultitapeWeakETH.PhysicalHistory

/-! # Concatenating local witnesses into a single timely path -/

namespace OAI.Computability.MultitapeWeakETH.PhysicalBlocks

open scoped Classical
noncomputable section

variable {M : Machine} {n b T : ℕ}

theorem prefix_coins {f g : ℕ → M.Choice} (p : Config M) (t : ℕ)
    (same : ∀ i < t, f i = g i) : frozenRun M f p t = frozenRun M g p t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [frozenRun,same t (by omega),ih (fun i hi => same i (by omega))]

private theorem segment_coins {f g : ℕ → M.Choice} (p : Phase M) (start len : ℕ)
    (same : ∀ i ≥ start, f i = g i) : segment f start p len = segment g start p len := by
  induction len with
  | zero => rfl
  | succ t ih => simp [segment,ih,same (start+t) (by omega)]

theorem splice_epoch (f g : ℕ → M.Choice) (p : Config M) {a d : ℕ} (h : a ≤ d) :
    frozenRun M (fun t => if t < a then f t else g t) p d =
      segment g a (frozenRun M f p a) (d-a) := by
  let joined t := if t < a then f t else g t
  have atA : frozenRun M joined p a = frozenRun M f p a :=
    prefix_coins _ _ (fun i hi => by simp [joined,hi])
  have resume := frozenRun_segment joined p a (d-a)
  rw [Nat.add_sub_of_le h,atA] at resume
  exact resume.symm.trans (segment_coins _ _ _ (fun i hi => by simp [joined,Nat.not_lt.mpr hi]))

def RunAt (coins : ℕ → M.Choice) (p : Config M) (T b j : ℕ) := frozenRun M coins p (cut T b j)

def Follows (b T : ℕ) (base : ℕ → M.Tapes → ℤ) (coins : ℕ → M.Choice) (p : Config M) :=
  ∀ j ≤ epochs T b, Fits (b:=b) (base j) (RunAt coins p T b j)

theorem history_of_path (hb : 0 < b) (base : ℕ → M.Tapes → ℤ) (allowed : ℕ → M.Choice → Prop)
    (x y out : Word n) (coins : ℕ → M.Choice) (ok : ∀ t, allowed t (coins t))
    (fits : Follows b T base coins (initial M x y))
    (accept : Accept (frozenRun M coins (initial M x y) (T+1)))
    (result : writes M (config (frozenRun M coins (initial M x y) (T+1))) out) :
    History hb T base allowed x y out := by
  let m := n ⌈/⌉ b
  let e := epochs T b
  let phase j := RunAt coins (initial M x y) T b j
  let mem (t : ℕ) : Memory M b := if t < m then store hb (.running (initial M (loadedPrefix x b t) y))
    else store hb (phase (min (t-m) e))
  have load (j : ℕ) (hj : j ≤ m) : mem j = store hb (.running (initial M (loadedPrefix x b j) y)) := by
    rcases lt_or_eq_of_le hj with h | rfl
    · simp [mem,h]
    · simp [mem,phase,RunAt,cut,frozenRun,m,prefix_all hb]
  have during (j : ℕ) (hj : j ≤ e) : mem (m+j) = store hb (phase j) := by
    simp [mem,min_eq_left hj,Nat.not_lt.mpr (Nat.le_add_right m j)]
  have endPhase : phase e = frozenRun M coins (initial M x y) (T+1) := by simp [phase,RunAt,e,cut_final T hb]
  have ended (j : ℕ) : mem (m+e+j) = store hb (phase e) := by
    simp only [mem,Nat.add_assoc,Nat.not_lt.mpr (Nat.le_add_right ..),ite_false,Nat.add_sub_cancel_left,
      min_eq_right (Nat.le_add_right e j)]
  apply (history_iff_stages hb T base allowed x y out).mpr
  refine ⟨mem,?_,?_,?_,?_⟩
  · simpa only [prefix_zero] using load 0 (Nat.zero_le _)
  · intro j hj k
    rw [load _ (by omega),load _ (by omega),prefix_succ]
  · intro j hj
    have forward := (cut_succ T b j).1
    have len : cut T b (j+1) - cut T b j ≤ b := by have := (cut_succ T b j).2; omega
    have segmentEq : segment coins (cut T b j) (phase j) (cut T b (j+1)-cut T b j) = phase (j+1) := by
      simp only [phase,RunAt,frozenRun_segment,Nat.add_sub_of_le forward]
    have after : Fits (b:=b) (base (j+1)) (phase (j+1)) := fits _ (by omega)
    have unchanged := (realize_epoch hb (fits j hj.le) (fits j hj.le) (fun _ _ => rfl) coins
      (cut T b j) _ len (segmentEq.symm ▸ after)).2.2
    change EpochStep hb T base allowed j (mem (m+j)) (mem (m+(j+1))) ∧ _
    rw [during j hj.le,during (j+1) (by omega)]
    refine ⟨⟨phase j,coins,ok,fits j hj.le,segmentEq.symm ▸ after,?_,?_⟩,?_⟩
    · intro last
      rw [segmentEq]
      change j+1=e at last
      rw [last,endPhase]
      exact accept
    · intro k _
      exact ⟨rfl,congrArg (fun p => store hb p k) segmentEq⟩
    · intro k hk
      change mem (m+(j+1)) k = store hb (phase j) k
      rw [during _ (by omega)]
      exact (congrArg (fun p => store hb p k) segmentEq.symm).trans (unchanged k hk)
  · intro j hj
    change mem (m+e+(j+1)) = mem (m+e+j) ∧ _
    rw [ended,ended]
    exact ⟨rfl,fun i _ => by simpa only [endPhase,readCell_store] using result i⟩

/-- Local nondeterministic epoch witnesses need only agree on their boundary
registers. Splicing their choices gives one run on the original initial tapes. -/
theorem path_of_history (hb : 0 < b) (base : ℕ → M.Tapes → ℤ) (allowed : ℕ → M.Choice → Prop)
    (canChoose : ∃ f : ℕ → M.Choice, ∀ t, allowed t (f t)) (x y out : Word n)
    (fitsInit : Fits (b:=b) (base 0) (.running (initial M x y)))
    (h : History hb T base allowed x y out) :
    ∃ coins : ℕ → M.Choice, (∀ t, allowed t (coins t)) ∧
      Accept (frozenRun M coins (initial M x y) (T+1)) ∧
      writes M (config (frozenRun M coins (initial M x y) (T+1))) out := by
  obtain ⟨mem,st⟩ := (history_iff_stages hb T base allowed x y out).mp h
  let m := n ⌈/⌉ b
  let e := epochs T b
  let p := initial M x y
  have trace (j : ℕ) (hj : j ≤ e) :
      ∃ f : ℕ → M.Choice, (∀ t, allowed t (f t)) ∧
        let phase := RunAt f p T b j
        Fits (b:=b) (base j) phase ∧ store hb phase = mem (m+j) ∧ (j = e → Accept phase) := by
    induction j with
    | zero =>
      obtain ⟨f,ok⟩ := canChoose
      refine ⟨f,ok,?_,?_,?_⟩
      · simpa [RunAt,cut,frozenRun,p] using fitsInit
      · simpa [RunAt,cut,frozenRun,p,m] using st.loaded.symm
      · simp [e,epochs]
    | succ j ih =>
      have lt : j < e := by omega
      obtain ⟨f,ok,atJ,values,_⟩ := ih lt.le
      obtain ⟨⟨w,g,allowedG,fw,endW,acceptW,io⟩,outside⟩ := st.epoch j lt
      let a := cut T b j
      let d := cut T b (j+1)
      let joined t := if t < a then f t else g t
      have clock := cut_succ T b j
      have len : d-a ≤ b := by dsimp [a,d]; omega
      let actual := RunAt f p T b j
      have done : RunAt joined p T b (j+1) = segment g a actual (d-a) := splice_epoch f g p clock.1
      obtain ⟨fitsEnd,matched,untouched⟩ := realize_epoch hb fw atJ
        (fun k hk => ((io k hk).1).trans (congrFun values.symm k)) g a (d-a) len endW
      refine ⟨joined,fun t => by by_cases ht : t < a <;> simp [joined,ht,ok,allowedG],?_,?_,?_⟩
      · rwa [done]
      · rw [done]
        funext k
        by_cases hk : k ∈ epochKeys M (base j)
        · exact (matched k hk).symm.trans (io k hk).2
        · exact (untouched k hk).trans ((congrFun values k).trans (outside k hk).symm)
      · intro last
        rw [done]
        exact accept_of_controller hb (matched none (Finset.mem_insert_self ..)) (acceptW last)
  obtain ⟨f,ok,_,values,accept⟩ := trace e le_rfl
  have endEq : RunAt f p T b e = frozenRun M f (initial M x y) (T+1) := by
    simp [RunAt,e,p,cut_final T hb]
  refine ⟨f,ok,endEq ▸ accept rfl,fun i => ?_⟩
  have reads := st.written i
  change readCell hb (mem (m+e)) M.output _ = _ at reads
  rwa [← values,endEq,readCell_store] at reads

end
end OAI.Computability.MultitapeWeakETH.PhysicalBlocks
