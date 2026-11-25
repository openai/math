import OAI.Computability.NearSquareRoot.ScheduleProgramLoad
import OAI.Computability.NearSquareRoot.ScheduleUniversalRun
import OAI.Computability.NearSquareRoot.ShortWordSpace

/-!
# Space of a finite ROM interpretation

A fixed program of length `L` takes at most `K=4(L+1)` physical transitions
between simulated boundaries. Only the selected transition moves data heads, so
the exact original data cover suffices. Both ROM heads lie between zero and `L`
at boundaries. Expanding this interval by `K` covers each ROM head throughout.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal
open IntegerMultiplication
variable {A I : Type} {m : ℕ}

/-- A set of tape-address pairs covering every prefix of an exact duration. -/
private def covered {A Q I : Type} (machine : TM.Rule A Q I) (x : TM.Config A Q I)
    (t : ℕ) (cells : Finset (I × ℤ)) :=
  ∀ k ≤ t, ∀ z, Trace (TM.advance machine) x k z → ∀ i, (i,(z.tape i).pos) ∈ cells

private theorem covered_append {A Q I : Type} {m : TM.Rule A Q I}
    {x y : TM.Config A Q I} {s t : ℕ} {V : Finset (I × ℤ)}
    (r : Trace (TM.advance m) x s y) (a : covered m x s V) (b : covered m y t V) :
    covered m x (s+t) V := by
  intro k hk z hz i
  by_cases le : k ≤ s
  · exact a k le z hz i
  obtain ⟨v,hv,tail⟩ := trace_split hz (k := s) (by omega)
  obtain rfl := trace_endpoint_unique hv r
  exact b _ (by omega) _ tail i

private noncomputable def enlarged (C : Finset (I × ℤ)) (L K : ℕ) :
    Finset (Index I × ℤ) := by
  classical
  let data := C.image (fun p : I × ℤ => ((Sum.inl p.1 : Index I),p.2))
  let rom := (Finset.univ (α := Bool) ×ˢ Finset.Icc (-(K : ℤ)) (L + K : ℤ)).image
    (fun p : Bool × ℤ => ((Sum.inr p.1 : Index I),p.2))
  exact data ∪ rom

private theorem enlarged_card (C : Finset (I × ℤ)) (L K : ℕ) :
    (enlarged C L K).card ≤ C.card + 2*(L+2*K+1) := by
  classical
  unfold enlarged
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le
    (Finset.card_image_le.trans ?_))
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool, Int.card_Icc]
  omega

private theorem enlarged_data (C : Finset (I × ℤ)) (L K : ℕ) (i : I) (v : ℤ)
    (hv : (i,v) ∈ C) :
    ((Sum.inl i : Index I),v) ∈ enlarged C L K := by
  classical
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨(i,v),hv,rfl⟩

private theorem enlarged_rom (C : Finset (I × ℤ)) (L K : ℕ) (b : Bool) (v : ℤ)
    (h : -(K : ℤ) ≤ v ∧ v ≤ (L : ℤ) + K) :
    ((Sum.inr b : Index I),v) ∈ enlarged C L K := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨(b,v),Finset.mem_product.mpr
    ⟨Finset.mem_univ _,Finset.mem_Icc.mpr h⟩,rfl⟩

variable [Finite A] [Finite I]
variable (blank : A) (machine : TM.Rule A (Fin m) I) (rs : List (I → A))

private theorem covered_segment (c : TM.Config A (Fin m) I) (b : Bool)
    (cells : Finset (I × ℤ)) {u K : ℕ} (budget : u ≤ K)
    (bank : ∀ k ≤ u, ∀ z, Trace (TM.advance (rule blank)) (ready machine rs b c) k z →
      ∀ i : I, (i,(z.tape (.inl i)).pos) ∈ cells) :
    covered (rule blank) (ready machine rs b c) u (enlarged cells (program machine rs).length K) := by
  intro k hk z tr j
  obtain ⟨l,h⟩ := head_excursion tr j
  cases j with
  | inl i =>
    exact enlarged_data cells _ K i _ (bank k hk z tr i)
  | inr j =>
    change (if j = b then (rowAddress machine rs c.pc : ℤ) else 0) - k ≤ _ at l
    change _ ≤ (if j = b then (rowAddress machine rs c.pc : ℤ) else 0) + k at h
    have bound := rowAddress_le machine rs c.pc
    apply enlarged_rom
    by_cases e : j = b
    · subst j
      simp only [ite_true] at l h
      omega
    · simp only [ite_eq_right e] at l h
      omega

variable (complete : ∀ r, r ∈ rs)
include complete

private theorem covered_interpret {c z : TM.Config A (Fin m) I} {t : ℕ} (b : Bool)
    (tr : Trace (TM.advance machine) c t z) (halt : TM.advance machine z = none)
    {cells : Finset (I × ℤ)} (cover : covered machine c t cells) :
    let L := (program machine rs).length
    let K := 4*(L+1)
    ∃ u finish, u ≤ K*(t+1) ∧ Trace (TM.advance (rule blank)) (ready machine rs b c) u finish ∧
      TM.advance (rule blank) finish = none ∧ (∀ i, finish.tape (.inl i) = dataCell (z.tape i)) ∧
      covered (rule blank) (ready machine rs b c) u (enlarged cells L K) := by
  induction tr generalizing b with
  | nil x =>
    obtain ⟨u,finish,ht,h₁,h₂,h₃⟩ := interpret_halt_bank blank machine rs complete halt b
    have hb : u ≤ 4*((program machine rs).length + 1) := by omega
    refine ⟨u,finish,by simpa using hb,h₁.trace,h₂,h₃,
      covered_segment blank machine rs x b cells hb ?_⟩
    intro k hk v sub i
    rw [h₁.throughout k hk v sub i]
    exact cover 0 (by omega) x (.nil x) i
  | @cons x y z n step _ ih =>
    have cover' : covered machine y n cells := fun k hk a h i =>
      cover (1+k) (by omega) a (.cons step h) i
    obtain ⟨v,hv,seg⟩ := interpret_step_banks blank machine rs complete step b
    have hfront := covered_segment blank machine rs x b cells hv (fun k hk z sub i => by
      rcases seg.throughout k hk z sub with old | new
      · rw [old i]; exact cover 0 (by omega) x (.nil _) i
      · rw [new i]; exact cover' 0 (by omega) y (.nil _) i)
    obtain ⟨w,finish,hw,rest,hh,hdata,hspace⟩ := ih (!b) halt cover'
    refine ⟨v+w,finish,?_,seg.trace.trans rest,hh,hdata,covered_append seg.trace hfront hspace⟩
    dsimp only at *
    rw [show 1+n+1 = (n+1)+1 by omega,Nat.mul_add_one]
    omega

/-- Physical common-machine simulation, including the halt check, on truly
blank-padded ROM tapes. The space charge counts distinct tape/address pairs. -/
theorem interpret_loaded_halting_space_sharp {c z : TM.Config A (Fin m) I} {t S : ℕ} (b : Bool)
    (tr : Trace (TM.advance machine) c t z) (halt : TM.advance machine z = none)
    (space : VisitsAtMost machine c t S) :
    let code := program machine rs
    let K := 4*(code.length+1)
    let start := loadedConf blank code c.tape b .seek (rowAddress machine rs c.pc) 0
    ∃ u finish, u ≤ K*(t+1) ∧ Trace (TM.advance (rule blank)) start u finish ∧
      TM.advance (rule blank) finish = none ∧ (∀ i, finish.tape (.inl i) = dataCell (z.tape i)) ∧
      VisitsAtMost (rule blank) start u (S + 2*(code.length+2*K+1)) := by
  obtain ⟨cells,card,cover⟩ := space
  obtain ⟨u,f,hu,run,halted,outputs,cov⟩ := covered_interpret blank machine rs complete b tr halt cover
  unfold ready at run
  rw [← normalize_loaded blank] at run
  obtain ⟨finish,hr,hfin⟩ := pull_trace run
  refine ⟨u,finish,hu,hr,pull_halt (by rw [hfin]; exact halted),?_,pull_space ?_⟩
  · intro i
    simpa only [← hfin,normalize_data] using outputs i
  · rw [normalize_loaded]
    refine ⟨_,(enlarged_card cells _ _).trans (Nat.add_le_add_right card _),cov⟩

theorem interpret_loaded_halting_space {c z : TM.Config A (Fin m) I} {t S : ℕ} (b : Bool)
    (tr : Trace (TM.advance machine) c t z) (halt : TM.advance machine z = none)
    (space : VisitsAtMost machine c t S) :
    let code := program machine rs
    let K := 4*(code.length+1)
    let start := loadedConf blank code c.tape b .seek (rowAddress machine rs c.pc) 0
    ∃ u finish, u ≤ K*(t+1) ∧ Trace (TM.advance (rule blank)) start u finish ∧
      TM.advance (rule blank) finish = none ∧ (∀ i, finish.tape (.inl i) = dataCell (z.tape i)) ∧
      VisitsAtMost (rule blank) start u (S*(2*K+1) + 2*(code.length+2*K+1)) := by
  obtain ⟨u,f,hu,hr,hh,hd,V,hV,cover⟩ :=
    interpret_loaded_halting_space_sharp blank machine rs complete b tr halt space
  refine ⟨u,f,hu,hr,hh,hd,V,hV.trans (Nat.add_le_add_right ?_ _),cover⟩
  exact Nat.le_mul_of_pos_right S (by omega)

end Universal

end NearSquareRoot
end Computability
end OAI
