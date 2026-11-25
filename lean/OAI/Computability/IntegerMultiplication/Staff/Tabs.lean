import OAI.Computability.IntegerMultiplication.Staff.Nat

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Staff
open Code Strip Loom Iter
variable {I : Type} (n : I→ℕ) {r : Regime I}
abbrev Local (i:I) := Fin (n i)
abbrev Across := Sigma (Local n)

theorem diameter (m : I→ℕ) (q : Realizes r m) :
    Dom r.scale m := (Regime.Small.extent (r:=r) (k:=fun i=>send (tally (m i))) q).mono (fun i=> by
  change _ ≤ size (tally _); rw [size_tally,tally_length]; omega)

variable (q : Realizes r n)
include q

theorem stampGauge :
    Dom (fun i:Across n=>r.scale i.1) (fun i=> (send (box i.2.val)).count) := by
  refine (((Dom.const _ 2).mul ((diameter n q).map (Sigma.fst : Across n→I))).add (Dom.const _ 1)).mono ?_
  intro i; change size (tally _) ≤ _; rw [size_tally,tally_length]
  have : i.2.val<n i.1 := i.2.isLt
  omega
omit q in
abbrev signal (q : Realizes r n) := onboard r
    (fun i (x:Fin (n i))=> send (box x.val)) (stampGauge n q)

abbrev at_ : Across n → I := Sigma.fst
theorem sendRoof (v:I→ Tree) (e : r.Small v) : (signal n q).Small (v ∘ (at_ n)) :=
  onboard_small _ (stampGauge n q) _ e
theorem landing (m:I→ℕ) (e : Realizes r m) :
    Realizes (signal n q) (m ∘ (at_ n)) := sendRoof n q (fun i=>send (box (m i))) e
theorem floor_ :
    Realizes (signal n q) (fun (x:Across n)=>x.2.val) :=
  onboard_hat _ (stampGauge n q)

-- Rip -> Regime.Small at polynomial n,l
variable {x t : I → ℕ}
omit q in
theorem artis (x₁:Dom r.scale x) (t₁:Dom r.scale t) {z:I→Tree} (h:Rip r x t r.header z) :
    r.Small z := by
  obtain ⟨k,⟨a,b,e,c,C⟩,d⟩ := h
  have u : Dom r.scale (fun i=>c*(x i*(t i+(r.scale i+1)^k))) :=
    (Dom.const _ _).mul (x₁.mul (t₁.add (((Dom.base _).add (Dom.const _ 1)).pow k)))
  refine ⟨b,u.mono ?_,e⟩
  intro i
  specialize C i; unfold mass at C
  exact_mod_cast (show (b i:ℝ)≤_ from (le_trans (by linarith : (b i:ℝ)≤_+1) C)) -- normalize mass
omit q in
private theorem native {t_ : ℕ} {O : Type} (v : Fin t_ → O) :
    (Series.natural t_).tab v=List.ofFn v := by
  apply List.ext_getElem (by simp [Series.card])
  intro i hi h
  rw [List.getElem_ofFn,Series.get (i:=⟨i,_⟩)]
  · rw [Series.index_symm, Series.get_natural (t_) (i:=⟨i,_⟩)]
  all_goals simp only [Series.card, Series.count_natural,List.length_ofFn] at *; simp_all
variable {X:Type} [Codec X]
-- extract all computed tallies from anywhere, or List etc arbitrary Codec
theorem harvest (v:(i:I)→ Fin (n i)→ X)
    (h : (signal n q).Has (fun i:Across n=> v i.1 i.2)) :
    r.Has fun i=> List.ofFn (v i) := by
  let s i := Series.natural (n i)
  let A (i:I) (x:Local n i) := send (box x.val)
  let a i := n i +1
  have np i : 1≤a i := by unfold a; omega
  -- generate index sequence as primary
  have index : r.Has (fun i=> List.ofFn fun x:Fin (n i)=> box x.val) := by
    have e := (show r.Has (tally ∘ n) from q).thenDo poly_line
    simpa only [Function.comp_def,lined] using e
  have offer : r.Small (stackRun s A) := by
    unfold stackRun A; simp only [stripe_eq',s,native]; exact index
  obtain ⟨y,of_⟩ := Rip.header (l:=fun _=>0) np offer
  obtain ⟨u,HH⟩ := Rip.header (l:=fun _=>0) np (show r.Small r.header from Regime.self)
  -- clone header via spread
  let c := r.header
  have t₀ : r.Small (fun i=> Tree.fork (send (box (n i))) (c i)) :=
    Regime.Small.pair (k:=fun i=>send (box (n i))) q Regime.self
  obtain ⟨f,t⟩ := Rip.header (l:=fun _=>0) np t₀
  obtain ⟨k,D,e⟩ := r.gauge
  let W k' := mass r a (fun _=>0) k'
  have a0 : Carries (W (k+f)) c (stackRun s (fun i _=> c i)) := by
    have i : (fun i:I=> tally ((s i).count))=box ∘ n := by funext; simp [s,box]
    have u x : (s x).count=n x := Series.count_natural _
    apply spread s _
    · simp_rw [u]; exact t.larger (mass_le (by omega : f≤k+f))
    refine ⟨D, fun i => le_trans ?_ (mul_le_mul_of_nonneg_left (mass_le (by omega : k≤k+f) i) (Nat.cast_nonneg _))⟩
    rw [u]
    have j : ((c i).count:ℝ) ≤ (D:ℝ)*((r.scale i:ℝ)+1)^k := by exact_mod_cast e i
    change _ ≤ (D:ℝ) * W k i
    calc
     _ ≤ ((n i:ℝ)+1) * ((D:ℝ)*((r.scale i:ℝ)+1)^k) := by gcongr
     _ = _ := by unfold W mass a; push_cast; ring
  have tp : Rip r a (fun _=>0) c (stackRun s (fun i x=> Tree.fork (c i) (A i x))) :=
    Rip.coalesce _ _ (p:=⟨k+f,a0⟩) ⟨y,of_⟩
  obtain ⟨m,M⟩ := Rip.header (l:=fun _=>0) (r:=signal n q) (n:=fun _=>1) (fun _=>le_rfl) h
  let P (i:I) := mass r (fun _=>1) (fun _=>0) m i
  let T (i:I) (a:Local n i) := send (v i a)
  have H := liftoff s (fun i x=> Tree.fork (c i) (A i x)) T P M
  have m₁ (i): (s i).count*(P i)+1 ≤ (2:ℝ)*W m i := by
    simp only [s,Series.count_natural]
    have E : (1:ℝ)≤ ((r.scale i:ℝ)+1)^m := one_le_pow₀ (by simp)
    simp only [W,P,a,mass]; push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) (n i)]
  have H0 : r.Small (stackRun s T) :=
    artis ((diameter n q).add (Dom.const _ 1)) (Dom.const _ 0)
      (tp.chain ⟨m,H.times (unit_mass np m) 2 (by simpa using m₁)⟩)
  unfold stackRun T s at H0
  simp only [stripe_eq',native] at H0
  exact H0
end Staff

end IntegerMultiplication
end Computability
end OAI
