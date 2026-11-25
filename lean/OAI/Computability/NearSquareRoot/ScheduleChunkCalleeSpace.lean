import OAI.Computability.NearSquareRoot.BoundedProgramCompile
import OAI.Computability.NearSquareRoot.ScheduleSchoolIO

/-!
# Calling a space-bounded compiled program in a larger register bank

The compiler places both control locations and register names in finite
subtypes specific to the surrounding code. We recover a structural height
certificate from the prefixes of the original compiled run. Its register
names may be changed injectively and its lexical scope extended. Registers
outside the image retain their caller-supplied contents.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkCalleeSpace
open IntegerMultiplication IntegerMultiplication.Prog Space Schoolbook

open private pc ix next next_do ret_step pc_good touched_mem update from
  OAI.Computability.IntegerMultiplication.Prog.Compile
open private paint_update from OAI.Computability.IntegerMultiplication.TMProgram

variable {A : Type} [Fintype A] (U : List (Loc A))

private abbrev Config := SM.Config (Sym U) (Pc U) (Ix U)

private abbrev PrefixBound (x : Config U) (t B : ℕ) : Prop :=
  ∀ {n y}, n ≤ t → Trace (SM.advance (compile U)) x n y → ∀ i, (y.stack i).length ≤ B

omit [Fintype A] in
private theorem sub_bound {x y : Config U} {total n t B : ℕ} (h : PrefixBound U x total B)
    (pre : Trace (SM.advance (compile U)) x n y) (room : n+t ≤ total) :
    PrefixBound U y t B := fun {_ _} hk run i =>
  h (by omega) (pre.trans run) i

private theorem relocate_aux {j : ℕ → ℕ} (inj : Function.Injective j)
    (park : Reg A) (outer : Scope A) {B C : ℕ} (room : B ≤ C)
    {Γ c r t s} (run : Run Γ c r t s)
    (hg : Good U Γ c) (ha : Above U Γ) (k : List (Ptr U))
    (height : PrefixBound U (machine U (pc U Γ c) r k) t B)
    (initial : ∀ i, (paint j r park i).length ≤ C) :
    BoundedRun C (B-k.length) (Γ.map (Prog.rename j) ++ outer) (Prog.rename j c)
      (paint j r park) t (paint j s park) := by
  classical
  induction run generalizing k with
  | pass => exact .pass initial
  | @pop Γ i r =>
    rw [paint_update inj, ← paint_at inj r park i]
    exact .pop initial
  | @push Γ i a r =>
    have hi := touched_mem U Γ (.push i a) (hg (sites_self _ _))
    change i ∈ used U at hi
    have res := height (by rfl)
      (Run.compile_ok U (.push (Γ := Γ) (i := i) (x := a) (r := r)) hg ha k)
      (some (ix U i))
    simp only [machine, ix_val U _ hi, Function.update_self, List.length_map,
      List.length_cons] at res
    rw [paint_update inj, ← paint_at inj r park i]
    apply BoundedRun.push
    intro l
    by_cases h : l = j i
    · subst l
      simpa only [Function.update_self, paint_at inj, List.length_cons] using res.trans room
    · simpa only [Function.update_of_ne h] using initial l
  | @look Γ i f r n s child ih =>
    have hg' (v) : Good U Γ (f v) := by
      intro l hl
      apply hg
      rw [sites]
      exact List.mem_cons.mpr (Or.inr (List.mem_flatMap.mpr ⟨v,mem_options v,hl⟩))
    have one : SM.advance (compile U) (machine U (pc U Γ (.look i f)) r k) =
        some (machine U (pc U Γ (f (r i).head?)) r k) := by
      rw [pc_good U hg]
      apply next U
      have hi := touched_mem U Γ (.look i f) (hg (sites_self _ _))
      change i ∈ used U at hi
      dsimp [compile, machine, SM.tops]
      cases hr : r i <;> simp [ix_val U _ hi, hr]
    have rest := ih (hg' _) ha k (sub_bound U height (.single one) le_rfl) initial
    dsimp [Prog.rename]
    rw [← paint_at inj r park i] at rest
    exact .look rest
  | @join Γ c d r n s m t left right ih jh =>
    have hc : Good U Γ c := by
      intro l hl; apply hg; rw [sites]; simp [hl]
    have hd : Good U Γ d := by
      intro l hl; apply hg; rw [sites]; simp [hl]
    let p : Ptr U := ⟨(Γ,d), hd (sites_self _ _)⟩
    have ep : pc U Γ d = some p := pc_good U hd
    have one : SM.advance (compile U) (machine U (pc U Γ (.join c d)) r k) =
        some (machine U (pc U Γ c) r (p::k)) := by
      rw [pc_good U hg]
      apply next_do U _ _ _ _ k (p::k) none (.push (.inr p)) (g := compile U)
      · dsimp [compile, machine, SM.tops]
        rw [ep]
        rfl
      · intro i
        cases i <;> simp [machine, update, SM.Action.perform, Function.update_of_ne]
    have leftCert := ih hc ha (p::k) (sub_bound U height (.single one) (by omega)) initial
    have preRun := (Trace.cons one (left.compile_ok U hc ha (p::k))).trans
      (Trace.single (ret_step U s p k))
    rw [← ep] at preRun
    have rightCert := jh hd ha k (sub_bound U height preRun le_rfl) leftCert.finish
    have hk := height (by omega) (.single one) none
    simp only [machine, List.length_map, List.length_cons] at hk
    exact .join leftCert rightCert (by simp only [List.length_cons]; omega)
  | @tie Γ c r n s child ih =>
    have hc : Good U (c :: Γ) c := by
      intro l hl; apply hg; rw [sites]; simp [hl]
    have above : Above U (c :: Γ) := by
      intro i d e
      cases i with
      | zero =>
        have eq : c = d := by simpa using e
        subst d; exact hc
      | succ i => simpa using ha i d (by simpa using e)
    have one : SM.advance (compile U) (machine U (pc U Γ (.tie c)) r k) =
        some (machine U (pc U (c::Γ) c) r k) := by
      rw [pc_good U hg]
      exact next U _ _ _ _ rfl
    exact .tie (ih hc above k (sub_bound U height (.single one) le_rfl) initial)
  | @again Γ i c r n s look child ih =>
    have above : Above U (Γ.drop i) := by
      intro l d e
      simp only [List.getElem?_drop] at e
      simpa [List.drop_drop, add_comm] using ha _ _ e
    have one : SM.advance (compile U) (machine U (pc U Γ (.again i)) r k) =
        some (machine U (pc U (Γ.drop i) c) r k) := by
      rw [pc_good U hg]
      apply next U
      simp [compile, look]
    have ih' := ih (ha _ _ look) above k (sub_bound U height (.single one) le_rfl) initial
    have len : i < Γ.length := by
      by_contra! h
      simp [List.getElem?_eq_none h] at look
    apply BoundedRun.again (c := Prog.rename j c)
    · rw [List.getElem?_append_left (by simpa using len), List.getElem?_map, look]
      rfl
    · simpa [List.drop_append, List.length_map, Nat.sub_eq_zero_of_le len.le,
        List.map_drop] using ih'

/-- Relocate a canonical compiled callee to injectively renamed registers,
retaining the caller's arbitrary parked data and lexical scope. -/
theorem relocate {c : Prog A} {r s : Reg A} {t B C : ℕ} (run : Run [] c r t s)
    (good : Good U [] c) (j : ℕ → ℕ) (inj : Function.Injective j)
    (park : Reg A) (outer : Scope A)
    (original : Segment (compile U)
      (machine U (some ⟨([],c),good (sites_self c [])⟩) r []) t (machine U none s []) B)
    (room : B ≤ C) (initial : ∀ i, (paint j r park i).length ≤ C) :
    BoundedRun C B outer (Prog.rename j c) (paint j r park) t (paint j s park) := by
  have h := relocate_aux U inj park outer room run good (fun i => by simp) []
    (by intro n y hn hy i; rw [pc_good U good] at hy; exact original.height hn hy i) initial
  simpa using h

open IntegerMultiplication.Code

/-- Register zero contains the parent frame and register one the active
query or reply. The remaining registers are empty. -/
theorem paint_succ_raw (frame data : List Ltr) :
    paint Nat.succ (raw data) (raw frame) = Function.update (raw frame) 1 data := by
  funext i
  cases i with
  | zero =>
    rw [paint_else _ _ _ (by intro l; omega), Function.update_of_ne (by decide : 0 ≠ 1)]
  | succ i =>
    rw [paint_at Nat.succ_injective]
    cases i with
    | zero => simp
    | succ i =>
      have ne : i+2 ≠ 1 := by omega
      simp only [Function.update_of_ne ne]
      simp [raw]

abbrev siteEntry (c : Cmd) : Pc (sites [] c) := some ⟨([],c), sites_self c []⟩

/-- A bounded isolated compiled run transfers to register one. The capacity
is the larger of the callee's own peak and the parked frame length. -/
theorem succ_bounded (c : Cmd) (query reply frame : List Ltr) {t B : ℕ}
    (run : Run [] c (raw query) t (raw reply))
    (original : Segment (compile (sites [] c)) (machine _ (siteEntry c) (raw query) []) t
        (machine _ none (raw reply) []) B) :
    BoundedRun (max B frame.length) B [] (Prog.rename Nat.succ c)
      (Function.update (raw frame) 1 query) t (Function.update (raw frame) 1 reply) := by
  let zeroIdx : Idx (sites [] c) := ⟨0, by simp [used]⟩
  have h₀ := original.height (Nat.zero_le t) (.nil _) (some zeroIdx)
  change ((raw query zeroIdx.val).map Sum.inl).length ≤ B at h₀
  simp only [zeroIdx, raw_zero, List.length_map] at h₀
  have moved := relocate (sites [] c) run (fun _ e => e) _ Nat.succ_injective (raw frame)
    [] original (Nat.le_max_left B frame.length) (by
      intro i
      rw [paint_succ_raw]
      by_cases h : i=1
      · subst i
        simpa only [Function.update_self] using h₀.trans (Nat.le_max_left B frame.length)
      · rw [Function.update_of_ne h]
        by_cases h' : i=0
        · subst i; exact Nat.le_max_right ..
        · simp [raw, h'])
  simpa only [paint_succ_raw] using moved

/-- Recompile the relocated callee into the caller's finite set of program
locations and registers. Both time and every prefix height are certified. -/
theorem succ_segment (c : Cmd) (query reply frame : List Ltr) {t B : ℕ}
    (run : Run [] c (raw query) t (raw reply))
    (original : Segment (compile (sites [] c)) (machine _ (siteEntry c) (raw query) []) t
        (machine _ none (raw reply) []) B)
    (target : List (Loc Ltr)) (good : Good target [] (Prog.rename Nat.succ c)) :
    Segment (compile target)
      (machine target (some ⟨([],Prog.rename Nat.succ c),good (sites_self _ _)⟩)
        (Function.update (raw frame) 1 query) []) t
      (machine target none (Function.update (raw frame) 1 reply) []) (max B frame.length) := by
  have h := (succ_bounded c query reply frame run original).compile_segment target good
    (fun i => by simp) []
  simpa [Nat.max_assoc, Nat.max_comm frame.length B] using h

end ChunkCalleeSpace

end NearSquareRoot
end Computability
end OAI
