import OAI.Computability.BorderVNP.DiagonalTallyScatter
import OAI.Computability.BorderVNP.RoutingISAInverse

/-! # Correctness and trace uniqueness of the native tally scatter loop -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyScatter

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA
open DiagonalResidueRAM (word word_val word_add TraceOK)

variable {w : ℕ}

private theorem recordsAt_congr (m m' : Memory w) (rs : List (ℕ × ℕ)) (p : ℕ)
    (h : RecordsAt m p rs) (he : ∀ a, p ≤ a → a < p+2*rs.length → m' a = m a) :
    RecordsAt m' p rs := by
  induction rs generalizing p with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨a,b,ht⟩ := h
    have hp := he p le_rfl (by simp)
    have hp' := he (p+1) (by omega) (by simp; omega)
    refine ⟨hp ▸ a, hp' ▸ b, ih (p+2) ht (fun j hj hbound => he j (by omega) ?_)⟩
    simp only [List.length_cons] at *
    omega

private theorem word_val_self (a : Word w) : word w a.val = a :=
  Fin.ext (word_val w a.val a.isLt)

private theorem after_cons (base i v p : ℕ) (m : Memory w) (rs : List (ℕ × ℕ))
    (hv : (m (p+1)).val = v) :
    after base rs (Function.update m (base+i) (m (base+i) + m (p+1))) = after base ((i,v)::rs) m := by
  have he : word w v = m (p+1) := hv ▸ word_val_self _
  funext a
  by_cases h : a = base+i
  · subst a
    simp [after, incrementAt, he, add_assoc]
  · simp [after, incrementAt, h, Ne.symm h]

/-- When the natural sum fits the word, reading the final physical tally returns
the integer subtotal without reduction modulo the word width. -/
theorem after_val (base a : ℕ) (rs : List (ℕ × ℕ)) (m : Memory w)
    (h : (m a).val + incrementAt base a rs < 2^w) :
    (after base rs m a).val = (m a).val + incrementAt base a rs := by
  have hi : incrementAt base a rs < 2^w := by omega
  simp only [after, Fin.val_add, word_val w _ hi, Nat.mod_eq_of_lt h]

/-- At tally coordinate `i` the increment is exactly the sum of every record
targeting that coordinate, including repeated visits. -/
theorem incrementAt_coordinate (base i : ℕ) (rs : List (ℕ × ℕ)) :
    incrementAt base (base+i) rs = ((rs.filter (fun r => decide (r.1 = i))).map Prod.snd).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : r.1 = i <;> simp [incrementAt, h, ih]

/-- The final memory equals the initial memory plus all increments at each address.
The only ticks other than the thirteen ticks per record are the final loop test. -/
theorem loop_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (rs : List (ℕ × ℕ)) {base dim p stop : ℕ}
    (hs : Loaded s base dim p stop) (hend : p+2*rs.length = stop)
    (hbase : base+dim ≤ 2^w) (hsep : Separate base dim p stop) (hr : RecordsAt m p rs)
    (hcoords : ∀ r ∈ rs, r.1 < dim) (htally : ∀ a, (m a).val + incrementAt base a rs < 2^w) :
    ∃ es t, Runs pub mac (.whileLt 50 51 body) s m es t (after base rs m) ∧
      Loaded t base dim stop stop ∧ Preserved s t ∧ TraceOK es [] (13*rs.length+1) := by
  induction rs generalizing s m p with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hend
    subst stop
    have he : s 50 = s 51 := Fin.ext (hs.2.2.1.trans hs.2.2.2.1.symm)
    have hm : after base [] m = m := by ext; simp [after,incrementAt]
    rw [hm]
    refine ⟨_, s, .whileDone (by simp [he]), hs, (fun _ _ _ _ _ _ _ => rfl), ?_⟩
    simp [TraceOK,tick]
  | cons r rs ih =>
    obtain ⟨i,v⟩ := r
    have hh : p+2+2*rs.length = stop := by simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hend
    have hi := hcoords (i,v) (List.mem_cons_self)
    change i < dim at hi
    have hguard : s 50 < s 51 := by
      change (s 50).val < (s 51).val
      rw [hs.2.2.1,hs.2.2.2.1]; omega
    obtain ⟨hcoord,hinc,hrest⟩ := hr
    have hv : (m (base+i)).val + v < 2^w := by
      have h := htally (base+i)
      simp [incrementAt] at h
      omega
    obtain ⟨es,t,hbody,hloaded,hpres,htrace⟩ := body_runs pub mac s m hs (by omega) hi (by omega)
      hv hcoord hinc
    let m' := Function.update m (base+i) (m (base+i)+m (p+1))
    have hdis := hsep i hi
    have hr' : RecordsAt m' (p+2) rs := recordsAt_congr m m' rs _ hrest (fun a ha hb => by
      have : a ≠ base+i := by omega
      simp [m',this])
    have hs' : Separate base dim (p+2) stop := by
      intro j hj
      have h := hsep j hj
      omega
    have ht' (a : ℕ) : (m' a).val + incrementAt base a rs < 2^w := by
      have h := htally a
      by_cases ha : a = base+i
      · subst a
        have hadd : (m (base+i)+m (p+1)).val = (m (base+i)).val + v := by
          rw [Fin.val_add, Nat.mod_eq_of_lt (by omega),hinc]
        simpa [m',hadd,incrementAt,Nat.add_assoc] using h
      · simpa [m',incrementAt,ha,Ne.symm ha] using h
    obtain ⟨fs,z,hloop,hz,hpz,hfz⟩ := ih t m' hloaded hh hs' hr' (fun j hj => hcoords _ (.tail _ hj)) ht'
    have run := Runs.whileStep hguard hbody hloop
    change Runs pub mac (.whileLt 50 51 body) s m _ z (after base rs m') at run
    rw [show after base rs m' = after base ((i,v)::rs) m from after_cons base i v p m rs hinc] at run
    refine ⟨_, z, run, hz, hpres.trans hpz, ?_⟩
    have he : 12+(13*rs.length+1)+1 = 13*((i,v)::rs).length+1 := by simp; omega
    simpa only [he, List.nil_append] using (htrace.append hfz).cons_tick

/-- The complete fragment returns after exactly `13 * rs.length + 3` native ticks.
Every address is updated by its natural subtotal, all private choices are empty and
all signs are positive. -/
theorem scatter_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (rs : List (ℕ × ℕ)) {base dim p stop : ℕ} (hs : Loaded s base dim p stop)
    (hend : p+2*rs.length = stop) (hbase : base+dim ≤ 2^w) (hsep : Separate base dim p stop)
    (hr : RecordsAt m p rs) (hcoords : ∀ r ∈ rs, r.1 < dim)
    (htally : ∀ a, (m a).val + incrementAt base a rs < 2^w) :
    ∃ es t, Runs pub mac scatter s m es t (after base rs m) ∧ Loaded t base dim stop stop ∧
      Preserved s t ∧ TraceOK es [] (13*rs.length+3) := by
  obtain ⟨es,t,run,hz,hpres,htrace⟩ := loop_runs pub mac s m rs hs hend hbase hsep hr hcoords htally
  have he : t 50 = t 51 := Fin.ext (hz.2.2.1.trans hz.2.2.2.1.symm)
  let mt := after base rs m
  have tail : Runs pub mac (.ifEq 50 51 .nop .reject) t mt [tick w,tick w] t mt :=
    .ifEq (by rw [ite_eq_left he]; exact Runs.localStep _ rfl rfl)
  have ht : TraceOK [tick w,tick w] [] 2 := by simp [TraceOK,tick]
  exact ⟨_,t,.seq run tail,hz,hpres,by simpa [Nat.add_assoc] using htrace.append ht⟩

/-- The emitted native table accepts exactly one trace and its choice tape for a
valid scatter execution. This uses the inverse instruction decoding theorem. -/
theorem scatter_execute_iff {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m es t mt}
    (h : Runs pub mac scatter s m es t mt) (bits : List (List Bool)) (fs : List (TeamRAM.Event w)) :
    TeamRAM.execute (scatter.program.fetch pub mac) ⟨0,s⟩ m bits = some fs ↔
      fs = es ∧ bits = es.map TeamRAM.Event.choices := by
  rw [Code.execute_iff_runs (c := scatter) (by decide)]
  constructor
  · rintro ⟨⟨z,mz,run⟩,rfl⟩
    obtain ⟨rfl,_,_⟩ := h.unique_of_deterministic (by decide) run
    exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨⟨t,mt,h⟩,rfl⟩

end DiagonalTallyScatter

end BorderVNP
end Computability
end OAI
