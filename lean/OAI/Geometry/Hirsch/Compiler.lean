import OAI.Geometry.Hirsch.Projection

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Forest

abbrev Position (V : ℕ) := Bool × Fin V
abbrev Upgrade (V : ℕ) (A : Type) := Fin V ⊕ (Bool × Position V × A)
abbrev Port (I : Type) (B V : ℕ) := I × Option (Fin B) × Position V

variable {I A : Type} {B V h H : ℕ} (tree : Forest I (Upgrade V A) (h + 2*H))

def price : I × Upgrade V A → Option (I × Fin V)
  | (i, .inl label) => some (i,label)
  | (_, .inr _) => none

def changeBank (role : Option (Fin B)) : I × Upgrade V A → Option (Port I B V × A)
  | (_, .inl _) => none
  | (i, .inr (kind,pos,a)) => if kind = role.isSome then some ((i,role,pos),a) else none

theorem changeBank_parent {role : Option (Fin B)} {i : I} {opt : Upgrade V A}
    {j : Port I B V} {a : A} (he : changeBank role (i,opt) = some (j,a)) :
    j.1 = i ∧ j.2.1 = role ∧ opt = .inr (role.isSome,j.2.2,a) := by
  rcases opt with l | ⟨kind,pos,choice⟩
  · simp [changeBank] at he
  · simp only [changeBank] at he
    split at he
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      simp_all
    · cases he

def physical : Forest I (Fin V) h where
  path i := trace h price (tree.path i)
  proper i j label rest he := by
    obtain ⟨p,opt,he,hr⟩ := tree.trace_parent h price _ _ _ he
    cases opt <;> simp [price] at he
    exact he.1 ▸ hr
  bounded _ := trace_length ..

def bankPath (i : I) (role : Option (Fin B)) := trace H (changeBank role) (tree.path i)

def compiled (B : ℕ) : Forest (Port I B V) A H where
  path x := tree.bankPath x.1 x.2.1
  proper x j a rest he := by
    obtain ⟨p,opt,he,hr⟩ := tree.trace_parent H (changeBank x.2.1) _ _ _ he
    obtain ⟨hj,hr',_⟩ := changeBank_parent he
    rw [hj, hr']
    exact hr
  bounded _ := trace_length ..

def Ready (usable : Set (Port I B V)) (b : Fin B) (i : I) : Prop :=
  ∀ pos, (i,none,pos) ∈ usable ∧ (i,some b,pos) ∈ usable

def Descent (phys : Forest I (Fin V) h) (usable : Set (Port I B V)) (b : Fin B)
    (represented : Set I) : Prop :=
  ∃ good : List (I × Fin V) → Prop, good [] ∧ ∀ i, good (phys.path i) →
    Ready usable b i → i ∉ represented →
    (phys.path i).length < h ∧ ∃ label, good ((i,label) :: phys.path i)

theorem compile_viable [Nonempty (Upgrade V A)] (usable : Set (Port I B V))
    (b : Fin B) (represented : Set I) (hv : (tree.compiled B).Viable usable)
    (hd : tree.physical.Descent usable b represented) : tree.Viable represented := by
  classical
  obtain ⟨pick,hp⟩ := hv
  obtain ⟨good,hg,hd⟩ := hd
  let c := fun i => tree.bankPath i (none : Option (Fin B))
  let t := fun i => tree.bankPath i (some b)
  let p := tree.physical.path
  let ok := fun i => Live usable pick (c i) ∧ Live usable pick (t i) ∧ good (p i) ∧
    (c i).length + (t i).length + (p i).length = (tree.path i).length
  have hc : ∀ i, (c i).length ≤ H := fun _ => trace_length ..
  have ht : ∀ i, (t i).length ≤ H := fun _ => trace_length ..
  have hl : ∀ i, (p i).length ≤ h := tree.physical.bounded
  have step : ∀ i, ∃ opt : Upgrade V A, ok i → i ∉ represented →
      (tree.path i).length < h + 2*H ∧ ∀ j, tree.path j = (i,opt) :: tree.path i → ok j := by
    intro i
    by_cases hi : ok i ∧ i ∉ represented
    swap
    · exact ⟨Classical.arbitrary _, fun hi' hn => (hi ⟨hi',hn⟩).elim⟩
    obtain ⟨⟨lc,lt,lg,le⟩,hn⟩ := hi
    have bc := hc i
    have bt := ht i
    have bl := hl i
    have next : ∀ j opt, tree.path j = (i,opt) :: tree.path i →
        c j = push H (changeBank none (i,opt)) (c i) ∧
        t j = push H (changeBank (some b) (i,opt)) (t i) ∧
        p j = push h (price (i,opt)) (p i) := by
      intro j opt hj
      simp [c,t,p,bankPath,physical,hj,trace]
    by_cases ready : Ready usable b i
    · obtain ⟨hh,label,hlabel⟩ := hd i lg ready hn
      change (p i).length < h at hh
      refine ⟨.inl label, fun _ _ => ⟨by omega, fun j hj => ?_⟩⟩
      obtain ⟨h₁,h₂,h₃⟩ := next j _ hj
      simp only [changeBank, price, push_none, push_some _ hh] at h₁ h₂ h₃
      unfold ok
      rw [h₁,h₂,h₃,hj]
      exact ⟨lc,lt,hlabel,by simp only [List.length_cons]; omega⟩
    · unfold Ready at ready
      obtain ⟨pos,hm⟩ := not_forall.mp ready
      rcases not_and_or.mp hm with hm | hm
      · let x : Port I B V := (i,none,pos)
        have hh : (c i).length < H := lt_of_le_of_ne bc (fun he => hm (hp x lc he))
        refine ⟨.inr (false,pos,pick x), fun _ _ => ⟨by omega, fun j hj => ?_⟩⟩
        obtain ⟨h₁,h₂,h₃⟩ := next j _ hj
        simp [changeBank, price, push_some _ hh] at h₁ h₂ h₃
        unfold ok
        rw [h₁,h₂,h₃,hj]
        exact ⟨(live_cons ..).mpr ⟨hm,rfl,lc⟩,lt,lg,by simp only [List.length_cons]; omega⟩
      · let x : Port I B V := (i,some b,pos)
        have hh : (t i).length < H := lt_of_le_of_ne bt (fun he => hm (hp x lt he))
        refine ⟨.inr (true,pos,pick x), fun _ _ => ⟨by omega, fun j hj => ?_⟩⟩
        obtain ⟨h₁,h₂,h₃⟩ := next j _ hj
        simp [changeBank, price, push_some _ hh] at h₁ h₂ h₃
        unfold ok
        rw [h₁,h₂,h₃,hj]
        exact ⟨lc,(live_cons ..).mpr ⟨hm,rfl,lt⟩,lg,by simp only [List.length_cons]; omega⟩
  choose upgrade hu using step
  have inv : ∀ i, Live represented upgrade (tree.path i) → ok i := by
    apply tree.induction_path
    · intro i he _
      simp [ok,c,t,p,physical,bankPath,he,trace,hg]
    · intro i j a he ih hi
      rw [he,live_cons] at hi
      exact (hu j (ih hi.2.2) hi.1).2 i (hi.2.1.symm ▸ he)
  exact ⟨upgrade, fun i hi he => by_contra fun hn => (hu i (inv i hi) hn).1.ne he⟩

end OAI.Geometry.Hirsch.Forest
