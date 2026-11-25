import OAI.Computability.NearSquareRoot.InterchangePivotBatch
import OAI.Computability.NearSquareRoot.InterchangeBatchFrame
import OAI.Computability.NearSquareRoot.InterchangeSpectralFibre
import OAI.Computability.NearSquareRoot.InterchangeRepairPhysical

/-! # The two full-volume reserve strips surrounding the main spectral swap

For each of the first and last `a` ranks, exchange that rank between the two
wings. All `m` middle ranks stay fixed. Combined with the batched spectral
swap on precisely those middle ranks, this exchanges both complete wings.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace OuterReserves

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom InterchangeSlots InterchangeAddress InterchangeSpectralRequest

abbrev Slots (a m : ℕ) := Fin (a + m + a)

abbrev main := Interchange.RepairSchedule.mainSlots

def first (a m : ℕ) : Fin a ↪ Slots a m :=
  ⟨fun j => ⟨j.val,by omega⟩,fun _ _ h => Fin.ext (congrArg (fun k : Slots a m => k.val) h)⟩

def last (a m : ℕ) : Fin a ↪ Slots a m :=
  ⟨fun j => ⟨a+m+j.val,by omega⟩,fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩

def ranks (a m : ℕ) : List (Slots a m) :=
  (List.finRange a).map (first a m) ++ (List.finRange a).map (last a m)

def pairs (a m : ℕ) := (ranks a m).map fun j => (j,j)

@[simp] theorem pairs_length (a m : ℕ) : (pairs a m).length = 2*a := by simp [pairs,ranks]; omega

theorem mem_main {a m : ℕ} (j : Slots a m) :
    j ∈ Set.range (main a m) ↔ a ≤ j.val ∧ j.val < a+m := by
  constructor
  · rintro ⟨k,rfl⟩
    change a ≤ a+k.val ∧ a+k.val < a+m
    omega
  · rintro ⟨lo,hi⟩
    exact ⟨⟨j.val-a,by omega⟩, Fin.ext (by change a+(j.val-a) = _; omega)⟩

theorem mem_ranks {a m : ℕ} (j : Slots a m) :
    j ∈ ranks a m ↔ j.val < a ∨ a+m ≤ j.val := by
  simp only [ranks,List.mem_append,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro (⟨k,rfl⟩ | ⟨k,rfl⟩)
    · exact .inl k.isLt
    · exact .inr (Nat.le_add_right ..)
  · rintro (lo | hi)
    · exact .inl ⟨⟨j.val,lo⟩, rfl⟩
    · exact .inr ⟨⟨j.val-(a+m),by have := j.isLt; omega⟩,
        Fin.ext (by change a+m+(j.val-(a+m)) = _; omega)⟩

theorem ranks_nodup (a m : ℕ) : (ranks a m).Nodup := by
  apply List.Nodup.append ((List.nodup_finRange _).map (first a m).injective)
    ((List.nodup_finRange _).map (last a m).injective)
  intro j ha hb
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨k,_,eq⟩ := List.mem_map.mp hb
  have h := congrArg Fin.val eq
  change a+m+k.val=i.val at h
  omega

private def mask {J T : Type} [DecidableEq J] {P G B : Dims.Tape} (ranks : List J)
    (x : Keys P G B J T) : Keys P G B J T :=
  (x.1,fun k => if k ∈ ranks then x.2.2.2.1 k else x.2.1 k,x.2.2.1,
    fun k => if k ∈ ranks then x.2.1 k else x.2.2.2.1 k,x.2.2.2.2)

abbrev swapOuter {a m : ℕ} {P G B : Dims.Tape} {T : Type} (x : Keys P G B (Slots a m) T) :=
  mask (ranks a m) x

/-- The two maps can be evaluated in either order. -/
theorem complete {a m b f : ℕ} {P G B : Dims.Tape} (x : Keys P G B (Slots a m) (Block b f)) :
    InterchangeSpectralFibre.swapMain (main a m) (swapOuter x) = swapper P G B x ∧
    swapOuter (InterchangeSpectralFibre.swapMain (main a m) x) = swapper P G B x := by
  classical
  simp only [InterchangeSpectralFibre.swapMain,swapOuter,mask,swapper,Prod.mk.injEq,true_and,and_true]
  constructor <;> constructor <;> funext k
  all_goals
    by_cases hm : k ∈ Set.range (main a m)
    · have hr : k ∉ ranks a m := by rw [mem_main] at hm; rw [mem_ranks]; omega
      simp [hm,hr]
    · have hr : k ∈ ranks a m := by rw [mem_main] at hm; rw [mem_ranks]; omega
      simp [hm,hr]

private theorem reflect_swap {J : Type} [DecidableEq J] [Fintype J] {n b f : ℕ} [NeZero b]
    (ord : J ≃ Fin n) (j : J) (P G B : Dims.Tape) (x : Keys P G B J (Block b f)) :
    (reflect ord (.pivot j j) trivial P G B f).symm x = swapAt j x := by
  let σ := reflect ord (Lag.pivot (p:=b) j j) trivial P G B f
  have out (u : Keys P G B J (Block b f)) : σ u = swapAt j u := by
    apply square.injective
    have hw := walk ord (Lag.pivot (p:=b) j j) trivial u
    have eq : Lag.fire f (chase u) (.pivot j j) = chase (swapAt j u) := by
      apply hear_all
      rintro ⟨_ | _, k⟩ <;> by_cases h : k=j <;> simp [Lag.fire,hear,place,chase,swapAt,h]
    exact Prod.ext (hw.2.trans eq) hw.1
  change σ.symm x = _
  apply σ.injective
  rw [Equiv.apply_symm_apply,out]
  rcases x with ⟨p,u,g,v,s⟩
  simp [swapAt]

private theorem mask_cons {J T : Type} [DecidableEq J] {P G B : Dims.Tape}
    (j : J) (js : List J) (h : j ∉ js) (x : Keys P G B J T) :
    swapAt j (mask js x) = mask (j :: js) x := by
  simp only [swapAt,mask,Prod.mk.injEq,true_and,and_true]
  constructor <;> funext k <;> by_cases hj : k = j
  all_goals first
    | subst k; simp [h]
    | simp [hj,Function.update_of_ne]

theorem recreation_diagonal {J : Type} [DecidableEq J] [Fintype J] {n b f : ℕ} [NeZero b]
    (ord : J ≃ Fin n) (js : List J) (h : js.Nodup) (P G B : Dims.Tape)
    (x : Keys P G B J (Block b f)) :
    (recreation ord P G B f (pivotOps b (js.map fun j => (j,j))) (pivotOps_legal _ _ _)).symm x = mask js x := by
  induction js with
  | nil => simp [mask,pivotOps,recreation]
  | cons j js ih =>
    change (reflect ord (.pivot j j) trivial P G B f).symm
      ((recreation ord P G B f (pivotOps b (js.map fun j => (j,j))) (pivotOps_legal _ _ _)).symm x) = _
    obtain ⟨hd,hs⟩ := List.nodup_cons.mp h
    rw [ih hs,reflect_swap,mask_cons _ _ hd]

theorem recreation_outer (a m b f : ℕ) [NeZero b] (P G B : Dims.Tape)
    (x : Keys P G B (Slots a m) (Block b f)) :
    (recreation (Equiv.refl _) P G B f (pivotOps b (pairs a m)) (pivotOps_legal _ _ _)).symm x =
      swapOuter x :=
  recreation_diagonal _ _ (ranks_nodup a m) P G B x

private theorem price {J : Type} (b : ℕ) (p : List (J × J)) :
    ((pivotOps b p).map Lag.prices).sum = p.length := by
  induction p with
  | nil => rfl
  | cons q qs ih =>
    obtain ⟨j,k⟩ := q
    change 1 + ((pivotOps b qs).map Lag.prices).sum = qs.length + 1
    omega

/-- The two reserve strips incur exactly `2*a` full-volume field requests.
Their physical routes use the supplied field width and inherit only the
spectator dimensions and radix. This theorem also applies when the prefix
is the augmented `BatchFrame.front P b`. -/
theorem full_volume_calls {I : Type} {r : Regime I} {b : ℕ} [NeZero b]
    (a m : ℕ) (P G B : I → Dims.Tape) (f l : I → ℕ) (good : I → Tree → Prop)
    (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (v : (i : I) → domain (J:=Slots a m) (b:=b) P G B f i → Tree)
    (hv : Manifest _ l v) (hgood : ∀ i k, good i (v i k)) :
    ChargedTyped (r:=r) (l:=l) (Equiv.refl (Slots a m)) P G B f (b:=b) good (2*a)
      (stackRun (layoutRows (Equiv.refl _) P G B f) v)
      (stackRun (layoutRows (Equiv.refl _) P G B f) (fun i => v i ∘ swapOuter)) := by
  let order := Equiv.refl (Slots a m)
  have h := execute_charged_typed order P G B f good hb hf hp hg hs (pivotOps b (pairs a m))
    (pivotOps_legal _ _ _) v hv hgood
  rw [price,pairs_length] at h
  have output (i : I) : v i ∘ (recreation order (P i) (G i) (B i) (f i)
      (pivotOps b (pairs a m)) (pivotOps_legal _ _ _)).symm = v i ∘ swapOuter :=
    funext fun k => congrArg (v i) (recreation_outer a m b (f i) (P i) (G i) (B i) k)
  simpa only [funext output] using h

/-- Executable header forest for the same exact list of full-volume requests. -/
theorem full_volume_schedule {I : Type} {r : Regime I} {b : ℕ} [NeZero b]
    (a m : ℕ) (P G B : I → Dims.Tape) (f l : I → ℕ) (good : I → Tree → Prop)
    (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (v : (i : I) → domain (J:=Slots a m) (b:=b) P G B f i → Tree)
    (hgood : ∀ i k, good i (v i k)) :
    ∃ uses : I → List (Request b), (∀ i, (uses i).length = 2*a) ∧
      (∀ i q, q ∈ uses i → (allowed f (countRows (b:=b) (Equiv.refl (Slots a m)) P G B f) l i q ∧
        ∀ k, good i (q.contents k)) ∧ inherited b (P i) (G i) (B i) q) ∧
      r.Small (fun i => InterchangeBatch.headers Request.header (uses i)) ∧
      ∀ i, InterchangeBatch.Chain Request.payload (Request.job b).reply
        (stripe (layoutRows (Equiv.refl (Slots a m)) P G B f i) (v i)) (uses i)
        (stripe (layoutRows (Equiv.refl (Slots a m)) P G B f i) (v i ∘ swapOuter)) := by
  let order := Equiv.refl (Slots a m)
  obtain ⟨uses,card,valid,tag,chain⟩ := pivot_schedule order P G B f l good hb hf hp hg hs
    (pairs a m) v hgood
  refine ⟨uses, fun i => (card i).trans (pairs_length a m), valid, tag, fun i => ?_⟩
  have output : v i ∘ (recreation order (P i) (G i) (B i) (f i) (pivotOps b (pairs a m))
      (pivotOps_legal _ _ _)).symm = v i ∘ swapOuter :=
    funext fun k => congrArg (v i) (recreation_outer a m b (f i) (P i) (G i) (B i) k)
  simpa only [output] using chain i

/-- Apply the physical row splitter and merger around the batched main swap.
The rank and cardinality of the reserve strips do not change the row map. -/
theorem with_rows_main {I : Type} {r : Regime I} {b W : ℕ} {l : I → ℕ}
    (a m : ℕ) (P G B : I → Dims.Tape) (f : I → ℕ) (hW : 0 < W) (hb : W < b)
    (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    {X : Type} {job : Job X} {zone : I → X → Prop} {calls : ℤ}
    (v : BatchFrame.Value (J:=Slots a m) (b:=b) P G B f b) (hv : Manifest _ l v)
    (run : Hopto job r (fun i =>
      (BatchFrame.rows (b:=b) (Equiv.refl (Slots a m)) P G B f (BatchRows.groups b W) i).count) l
      zone calls (together r.header (BatchFrame.packet (W:=W) (Equiv.refl _) P G B f
        (BatchFrame.padded P G B f (by omega) v)))
      (BatchFrame.packet (W:=W) (Equiv.refl _) P G B f (fun u i =>
        BatchFrame.padded P G B f (by omega) v u i ∘ InterchangeSpectralFibre.swapMain (main a m)))) :
    Hopto job r (fun i => (BatchFrame.rows (b:=b) (Equiv.refl (Slots a m)) P G B f b i).count) l
      zone calls (together r.header (stackRun (BatchFrame.rows (Equiv.refl _) P G B f b) v))
      (stackRun (BatchFrame.rows (Equiv.refl _) P G B f b)
        (fun i => v i ∘ InterchangeSpectralFibre.swapMain (main a m))) := by
  classical
  let F (i : I) (x : (Slots a m → Block b (f i)) × (Slots a m → Block b (f i))) :=
    (fun j => if j ∈ Set.range (main a m) then x.2 j else x.1 j,
     fun j => if j ∈ Set.range (main a m) then x.1 j else x.2 j)
  exact BatchFrame.with_rows (Equiv.refl _) P G B f hW hb hf hp hg hs F v hv run

end OuterReserves

end NearSquareRoot
end Computability
end OAI
