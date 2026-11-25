import OAI.Geometry.Hirsch.Compiler

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Forest

variable {I A J : Type} {B V h H : ℕ}

theorem union_bound [Finite I] [Finite J] (s : Set I) (f : I → Set J) (k : ℕ)
    (hh : ∀ i ∈ s, (f i).ncard ≤ k) : (⋃ i ∈ s, f i).ncard ≤ k * s.ncard := by
  induction s, s.toFinite using Set.Finite.induction_on with
  | empty => simp
  | @insert i s hi hs ih =>
    rw [biUnion_insert, ncard_insert_of_notMem hi, mul_add, mul_one, add_comm]
    exact (ncard_union_le ..).trans (Nat.add_le_add (hh i (mem_insert ..))
      (ih (fun j hj => hh j (mem_insert_of_mem _ hj))))

def keys (B : ℕ) (entry : I × Fin V) : Set (Port I B V) :=
  {(entry.1,none,false,entry.2), (entry.1,none,true,entry.2)}

def prices (phys : Forest I (Fin V) h) (B : ℕ) (i : I) : Set (Port I B V) :=
  ⋃ e ∈ {e | e ∈ phys.path i}, keys B e

def roles (b d : Fin B) : Set (Option (Fin B)) := {none,some b,some d}

def Footprint (phys : Forest I (Fin V) h) (b d : Fin B) (i : I) (k : ℕ)
    (s : Set (Port I B V)) : Prop :=
  ∃ direct : Set (Port I B V), direct.ncard ≤ k ∧
    (∀ x ∈ direct, x.1 = i ∧ x.2.1 ∈ roles b d) ∧ s ⊆ direct ∪ phys.prices B i

def fee (b d : Fin B) : I × Upgrade V A → Set (Port I B V)
  | (i,.inl label) => keys B (i,label)
  | (i,.inr (false,pos,_)) => {(i,none,pos)}
  | (i,.inr (true,pos,_)) => {(i,some b,pos),(i,some d,pos)}

theorem fee_bound (b d : Fin B) (e : I × Upgrade V A) : (fee b d e).ncard ≤ 2 := by
  rcases e with ⟨i,label | ⟨_ | _,pos,a⟩⟩
  · exact (ncard_insert_le ..).trans (by simp)
  · simp [fee]
  · exact (ncard_insert_le ..).trans (by simp)

variable (tree : Forest I (Upgrade V A) (h+2*H))

def charge (b d : Fin B) (i : I) := (tree.path i).head?.elim ∅ (fee b d)

theorem charge_bound (b d : Fin B) (i : I) : (tree.charge b d i).ncard ≤ 2 := by
  unfold charge
  cases (tree.path i).head? with
  | none => simp
  | some e => exact fee_bound b d e

def tolls (b d : Fin B) (i : I) := ⋃ j ∈ tree.ancestors i, tree.charge b d j

theorem fee_subset (b d : Fin B) : ∀ i e, e ∈ tree.path i → fee b d e ⊆ tree.tolls b d i := by
  apply tree.induction_path
  · intro i he; simp [he]
  · intro i j opt he ih e hm
    rw [he,List.mem_cons] at hm
    rcases hm with rfl | hm
    · intro x hx
      exact mem_iUnion₂.mpr ⟨i,mem_insert ..,by simpa [charge,he] using hx⟩
    · intro x hx
      obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (ih _ hm hx)
      refine mem_iUnion₂.mpr ⟨p,?_,hx⟩
      rw [ancestors,he,past_cons]
      exact mem_insert_of_mem _ hp

theorem price_tolls (b d : Fin B) (i : I) {x : Port I B V}
    (hx : x ∈ tree.physical.prices B i) :
    x ∈ tree.tolls b d i ∧ x.1 ∈ tree.ancestors i ∧ x.2.1 ∈ roles b d := by
  obtain ⟨e,he,hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨⟨j,opt⟩,hm,hh⟩ := trace_mem he
  cases opt with
  | inr _ => cases hh
  | inl label =>
    have heq : (j,label) = e := Option.some.inj hh
    subst e
    refine ⟨tree.fee_subset b d i _ hm hx,?_⟩
    have hj : j ∈ tree.ancestors i := Or.inr ⟨.inl label,hm⟩
    rcases hx with rfl | rfl <;> exact ⟨hj,mem_insert ..⟩

theorem bank_tolls (b d : Fin B) (i : I) {x : Port I B V}
    (hi : x.1 ∈ tree.ancestors i) (hr : x.2.1 ∈ roles b d) :
    past ((tree.compiled B).path x) ⊆ tree.tolls b d i := by
  rintro y ⟨a,ha⟩
  obtain ⟨⟨j,opt⟩,hm,hh⟩ := trace_mem (tree.trace_past H (changeBank x.2.1) i x.1 hi ha)
  obtain ⟨hj,hr',rfl⟩ := changeBank_parent hh
  apply tree.fee_subset b d i _ hm
  obtain ⟨p,role,pos⟩ := y
  dsimp at hj hr'
  subst p
  subst role
  simp only [roles,mem_insert_iff,mem_singleton_iff] at hr
  rcases hr with he | he | he <;> simp [he,fee]

variable [Fintype I] [Nonempty A]

theorem compile_support (b d : Fin B) (i : I) {s : Set (Port I B V)} {k : ℕ}
    (hf : tree.physical.Footprint b d i k s) :
    ∃ direct : Set (Port I B V), direct.ncard ≤ k ∧
      (tree.compiled B).program.closure s ⊆ direct ∪ tree.tolls b d i := by
  obtain ⟨direct,hk,hr,hs⟩ := hf
  refine ⟨direct,hk,fun y hy => ?_⟩
  obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
  have he : x ∈ direct ∪ tree.tolls b d i ∧ x.1 ∈ tree.ancestors i ∧ x.2.1 ∈ roles b d := by
    rcases hs hx with hm | hm
    · obtain ⟨hi,hb⟩ := hr x hm
      exact ⟨Or.inl hm,hi.symm ▸ mem_insert i _,hb⟩
    · obtain ⟨ht,hi,hb⟩ := tree.price_tolls b d i hm
      exact ⟨Or.inr ht,hi,hb⟩
  rcases hy with rfl | hy
  · exact he.1
  · exact Or.inr (tree.bank_tolls b d i he.2.1 he.2.2 hy)

theorem compile_span (b d : Fin B) (i : I) {s : Set (Port I B V)} {k : ℕ}
    (hf : tree.physical.Footprint b d i k s) :
    ((tree.compiled B).program.closure s).ncard ≤ k + 2 * (h+2*H+1) := by
  obtain ⟨direct,hk,hs⟩ := tree.compile_support b d i hf
  exact (ncard_le_ncard hs).trans ((ncard_union_le ..).trans (Nat.add_le_add hk
    ((union_bound _ _ 2 (fun j _ => tree.charge_bound b d j)).trans
      (Nat.mul_le_mul_left _ (tree.ancestors_bound i)))))

theorem compile_union [Nonempty (Upgrade V A)] (b : Fin B) (s : Set I)
    (f : I → Set (Port I B V)) (hf : ∀ i ∈ s, tree.physical.Footprint b b i 3 (f i)) :
    ((tree.compiled B).program.closure (⋃ i ∈ s, f i)).ncard ≤ 5 * (tree.program.closure s).ncard := by
  classical
  have hh : ∀ i, ∃ direct : Set (Port I B V), direct.ncard ≤ 3 ∧
      (i ∈ s → (tree.compiled B).program.closure (f i) ⊆ direct ∪ tree.tolls b b i) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨d,hk,hsub⟩ := tree.compile_support b b i (hf i hi)
      exact ⟨d,hk,fun _ => hsub⟩
    · exact ⟨∅,by simp,fun h => (hi h).elim⟩
  choose direct hk hsub using hh
  let covered := tree.program.closure s
  have ht : (tree.compiled B).program.closure (⋃ i ∈ s, f i) ⊆
      ⋃ i ∈ covered, direct i ∪ tree.charge b b i := by
    intro y hy
    obtain ⟨x,hx,ha⟩ := mem_iUnion₂.mp hy
    obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
    rcases hsub i hi (mem_iUnion₂.mpr ⟨x,hx,ha⟩) with hd | hc
    · exact mem_iUnion₂.mpr ⟨i,tree.program.subset_closure s hi,Or.inl hd⟩
    · obtain ⟨j,hj,hc⟩ := mem_iUnion₂.mp hc
      exact mem_iUnion₂.mpr ⟨j,mem_iUnion₂.mpr ⟨i,hi,hj⟩,Or.inr hc⟩
  exact (ncard_le_ncard ht).trans (union_bound _ _ 5 (fun i _ =>
    (ncard_union_le ..).trans (Nat.add_le_add (hk i) (tree.charge_bound b b i))))

end OAI.Geometry.Hirsch.Forest
