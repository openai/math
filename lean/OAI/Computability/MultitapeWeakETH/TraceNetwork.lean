import OAI.Computability.MultitapeWeakETH.Gluing
import OAI.Computability.MultitapeWeakETH.Tables

/-! # The network of consecutive block uses in a fixed schedule

A key can denote a tape block or the boundary controller. Each stage lists
the keys it touches. One wire goes from a key's producer to its next
consumer. Initial values enter the first use through the local relation.
The ambient address space can be infinite.
-/

namespace OAI.Computability.MultitapeWeakETH.TraceNetwork

open scoped Classical
noncomputable section

variable {I : Type} {V n b : ℕ} (touch : Fin V → Finset I)

/-- Outside the finite schedule there are no uses. -/
def Uses (t : ℕ) (i : I) : Prop := ∃ h : t < V, i ∈ touch ⟨t,h⟩

@[simp] theorem uses_time (t : Fin V) (i : I) : Uses touch t.val i ↔ i ∈ touch t :=
  ⟨fun ⟨_,h⟩ => h,fun h => ⟨t.isLt,h⟩⟩

abbrev prev (t : ℕ) (i : I) := BlockHistory.previous (Uses touch) t i

abbrev Port := (t : Fin V) × ↥(touch t)
abbrev Edge := {p : Port touch // ∃ u : Fin V, prev touch p.1.val p.2.val = some u.val}

namespace Edge
variable {touch}
def dst (e : Edge touch) : Fin V := e.val.1
def key (e : Edge touch) : I := e.val.2.val
def src (e : Edge touch) : Fin V := e.property.choose

theorem previous (e : Edge touch) : prev touch e.dst.val e.key = some e.src.val := e.property.choose_spec
theorem at_dst (e : Edge touch) : e.key ∈ touch e.dst := e.val.2.property
theorem at_src (e : Edge touch) : e.key ∈ touch e.src :=
  (uses_time ..).mp (((BlockHistory.previous_eq_some _).mp e.previous).2.1)

theorem ext_dst {e f : Edge touch} (hd : e.dst = f.dst) (hk : e.key = f.key) : e = f := by
  apply Subtype.ext
  apply Sigma.ext hd
  cases e with | mk p _ =>
    cases f with | mk q _ =>
      cases p with | mk t i =>
        cases q with | mk u j =>
          change t = u at hd
          subst u
          exact heq_of_eq (Subtype.ext hk)

theorem ext_src {e f : Edge touch} (hs : e.src = f.src) (hk : e.key = f.key) : e = f := by
  apply ext_dst _ hk
  apply Fin.ext
  have last := e.previous
  rw [hs,hk] at last
  exact BlockHistory.unique_consumer _ ((uses_time ..).mpr (hk ▸ e.at_dst))
    ((uses_time ..).mpr f.at_dst) last f.previous
end Edge

def edgeEquiv : Edge touch ≃ Fin (Fintype.card (Edge touch)) := Fintype.equivFin _

def network (width : I → ℕ) (input output : Fin (n ⌈/⌉ b) ↪ Fin V) : Network n b where
  vertices := V
  edges := Fintype.card (Edge touch)
  src e := ((edgeEquiv touch).symm e).src
  dst e := ((edgeEquiv touch).symm e).dst
  width e := width ((edgeEquiv touch).symm e).key
  input := input
  output := output

variable (width : I → ℕ) (input output : Fin (n ⌈/⌉ b) ↪ Fin V)

theorem degree_le (v : Fin V) :
    (network touch width input output).degree v ≤ 2*(touch v).card := by
  classical
  let G := network touch width input output
  let E := (edgeEquiv touch).symm
  have srcMem (e : Fin G.edges) (h : G.src e = v) : (E e).key ∈ touch v :=
    h ▸ (E e).at_src
  have dstMem (e : Fin G.edges) (h : G.dst e = v) : (E e).key ∈ touch v :=
    h ▸ (E e).at_dst
  let S (i : {e : Fin G.edges // G.src e = v}) : ↥(touch v) := ⟨(E i.val).key,srcMem i.val i.property⟩
  let D (i : {e : Fin G.edges // G.dst e = v}) : ↥(touch v) := ⟨(E i.val).key,dstMem i.val i.property⟩
  have s : Function.Injective S := fun i j eq => Subtype.ext (E.injective (Edge.ext_src
    (i.property.trans j.property.symm) (congrArg Subtype.val eq)))
  have d : Function.Injective D := fun i j eq => Subtype.ext (E.injective (Edge.ext_dst
    (i.property.trans j.property.symm) (congrArg Subtype.val eq)))
  have h := Nat.add_le_add (Fintype.card_le_of_injective S s) (Fintype.card_le_of_injective D d)
  change G.degree v ≤ _
  simp only [Fintype.card_subtype,Fintype.card_coe] at h
  simp only [two_mul,Network.degree]
  convert h using 1
  congr 2 <;> ext <;> simp

/-- Increasing the number of stages never increases the degree at a given stage. -/
theorem bounded (D : ℕ) (arity : ∀ v, 2*(touch v).card ≤ D)
    (sizes : ∀ i, width i ≤ D*b) : (network touch width input output).Bounded D :=
  ⟨fun v => (degree_le touch width input output v).trans (arity v),fun _ => sizes _⟩

abbrev Local (v : Fin V) := (k : ↥(touch v)) → Word (width k.val)
abbrev Values := (v : Fin V) → Local touch width v

local notation "G" => network touch width input output
local notation "E" => Equiv.symm (edgeEquiv touch)

/-- A stage may inspect its incoming blocks and external bits and choose its outgoing blocks. -/
abbrev Stage := (v : Fin V) → Local touch width v → Local touch width v →
  ((G).localBits input v → Bool) → ((G).localBits output v → Bool) → Prop

variable (init : (i : I) → Word (width i)) (legal : Stage touch width input output)

/-- The table for a stage enforces the selected stage rule, the initial value at
first use and both endpoints of every consecutive-use wire. -/
def tables : (G).Relation := fun v labels x out =>
  ∃ before after : Local touch width v, legal v before after x out ∧
    (∀ k, prev touch v.val k.val = none → before k = init k.val) ∧
    (∀ (e : Fin (G).edges) (hd : (G).dst e = v),
      labels ⟨e,Or.inr hd⟩ = before ⟨(E e).key,hd ▸ (E e).at_dst⟩) ∧
    (∀ (e : Fin (G).edges) (hs : (G).src e = v),
      labels ⟨e,Or.inl hs⟩ = after ⟨(E e).key,hs ▸ (E e).at_src⟩)

/-- A local witness at each stage glues precisely when each consumer reads the last
write and first uses read the initialized value. -/
theorem attains_iff_compatible (x out : Word n) :
    (G).Attains (tables touch width input output init legal) x out ↔
    ∃ before after : Values touch width,
      (∀ v, legal v (before v) (after v) (fun i => x i.val) (fun i => out i.val)) ∧
      (∀ v (k : ↥(touch v)), prev touch v.val k.val = none → before v k = init k.val) ∧
      ∀ e : Edge touch, before e.dst ⟨e.key,e.at_dst⟩ = after e.src ⟨e.key,e.at_src⟩ := by
  constructor
  · rintro ⟨labels,atVertex⟩
    choose before after rule first inc sent using atVertex
    refine ⟨before,after,rule,first,?_⟩
    intro e
    obtain ⟨j,rfl⟩ := (E).surjective e
    exact (inc ((G).dst j) j rfl).symm.trans (sent ((G).src j) j rfl)
  · rintro ⟨before,after,rule,first,agree⟩
    refine ⟨fun j => after (E j).src ⟨(E j).key,(E j).at_src⟩,fun v =>
      ⟨before v,after v,rule v,first v,?_,?_⟩⟩
    · rintro j rfl
      exact (agree (E j)).symm
    · rintro j rfl
      rfl

/-- Supply a block at any time, including keys outside the finite schedule. -/
def memory (after : Values touch width) (t : ℕ) (i : I) : Word (width i) :=
  if h : ∃ u : Fin V, prev touch t i = some u.val then
    after h.choose ⟨i,(uses_time ..).mp (((BlockHistory.previous_eq_some _).mp h.choose_spec).2.1)⟩
  else init i

variable {touch width init}

private theorem memory_some (after : Values touch width) {t : ℕ} {u : Fin V} {i : I}
    (h : prev touch t i = some u.val) (hi : i ∈ touch u) :
    memory touch width init after t i = after u ⟨i,hi⟩ := by
  have ex : ∃ z : Fin V, prev touch t i = some z.val := ⟨u,h⟩
  rw [memory,dite_eq_left ex]
  have eu : ex.choose = u := Fin.ext (Option.some.inj (ex.choose_spec.symm.trans h))
  cases eu
  rfl

private theorem memory_none (after : Values touch width) {t : ℕ} {i : I}
    (h : prev touch t i = none) : memory touch width init after t i = init i := by
  simp [memory,h]

private theorem memory_update (after : Values touch width) (v : Fin V) (k : ↥(touch v)) :
    memory touch width init after (v.val+1) k.val = after v k :=
  memory_some after (by simp [prev,BlockHistory.previous,(uses_time ..).mpr k.property]) k.property

private theorem memory_skip (after : Values touch width) (v : Fin V) (i : I) (hi : i ∉ touch v) :
    memory touch width init after (v.val+1) i = memory touch width init after v.val i := by
  have same : prev touch (v.val+1) i = prev touch v.val i := by
    simp [prev,BlockHistory.previous,hi]
  unfold memory
  split <;> split
  · rename_i a b
    have eq : a.choose = b.choose :=
      Fin.ext (Option.some.inj (a.choose_spec.symm.trans (same.trans b.choose_spec)))
    have matchVal (u w : Fin V) (h : u = w) (hu : i ∈ touch u) (hw : i ∈ touch w) :
        after u ⟨i,hu⟩ = after w ⟨i,hw⟩ := by subst w; rfl
    exact matchVal _ _ eq _ _
  · rename_i a b
    exact (b ⟨a.choose,same ▸ a.choose_spec⟩).elim
  · rename_i a b
    exact (a ⟨b.choose,same.symm ▸ b.choose_spec⟩).elim
  · rfl

variable (touch width init)

/-- The wire labels of the finite network describe exactly the sequential
histories of the initialized memory, with every unaccessed key preserved. -/
theorem attains_iff_history (x out : Word n) :
    (G).Attains (tables touch width input output init legal) x out ↔
    ∃ mem : ℕ → (i : I) → Word (width i), mem 0 = init ∧
      ∀ v : Fin V, legal v (fun k => mem v.val k.val) (fun k => mem (v.val+1) k.val)
          (fun i => x i.val) (fun i => out i.val) ∧
        ∀ i, i ∉ touch v → mem (v.val+1) i = mem v.val i := by
  rw [attains_iff_compatible]
  constructor
  · rintro ⟨before,after,rule,first,agree⟩
    let mem := memory touch width init after
    refine ⟨mem,funext (fun _ => memory_none _ rfl),fun v => ⟨?_, memory_skip after v⟩⟩
    have inEq (k : ↥(touch v)) : mem v.val k.val = before v k := by
      cases h : prev touch v.val k.val with
      | none => exact (memory_none after h).trans (first v k h).symm
      | some j =>
        obtain ⟨hj,hk⟩ := ((BlockHistory.previous_eq_some _).mp h).2.1
        let e : Edge touch := ⟨⟨v,k⟩,⟨⟨j,hj⟩,h⟩⟩
        exact (memory_some after e.previous e.at_src).trans (agree e).symm
    rw [show (fun k : ↥(touch v) => mem v.val k.val) = before v from funext inEq,
      show (fun k : ↥(touch v) => mem (v.val+1) k.val) = after v from funext (memory_update after v)]
    exact rule v
  · rintro ⟨mem,start,stages⟩
    let after : Values touch width := fun v k => mem (v.val+1) k.val
    have track (t : ℕ) (ht : t ≤ V) (i : I) : memory touch width init after t i = mem t i := by
      induction t with
      | zero => exact (memory_none after rfl).trans (congrFun start.symm i)
      | succ t ih =>
        let v : Fin V := ⟨t,by omega⟩
        by_cases active : i ∈ touch v
        · exact memory_update after v ⟨i,active⟩
        · exact (memory_skip after v i active).trans ((ih (by omega)).trans ((stages v).2 i active).symm)
    refine ⟨fun v k => mem v.val k.val,after,fun v => (stages v).1,?_,?_⟩
    · intro v k h
      exact (track _ v.isLt.le k.val).symm.trans (memory_none after h)
    · intro e
      exact (track _ e.dst.isLt.le e.key).symm.trans (memory_some after e.previous e.at_src)


/-- Typed registers can be packed independently into the binary wire alphabets.
Decoding the same word at both ends of a wire preserves agreement. -/
theorem exists_typed_tables (F : I → Type) (pack : (i : I) → F i ↪ Word (width i))
    (start : (i : I) → F i)
    (step : (v : Fin V) → ((i : ↥(touch v)) → F i.val) → ((i : ↥(touch v)) → F i.val) →
      ((G).localBits input v → Bool) → ((G).localBits output v → Bool) → Prop) :
    ∃ R : (G).Relation, ∀ x out, (G).Attains R x out ↔
      ∃ mem : ℕ → (i : I) → F i, mem 0 = start ∧ ∀ v : Fin V,
        step v (fun k => mem v.val k.val) (fun k => mem (v.val+1) k.val)
          (fun k => x k.val) (fun k => out k.val) ∧
        ∀ i, i ∉ touch v → mem (v.val+1) i = mem v.val i := by
  let (i : I) : Nonempty (F i) := ⟨start i⟩
  let unpack (i : I) := Function.invFun (pack i)
  have left (i : I) (z : F i) : unpack i (pack i z) = z := Function.leftInverse_invFun (pack i).injective _
  let encoded : Stage touch width input output := fun v a b =>
    step v (fun i => unpack i.val (a i)) (fun i => unpack i.val (b i))
  refine ⟨tables touch width input output (fun i => pack i (start i)) encoded,fun x out => ?_⟩
  rw [attains_iff_history]
  constructor
  · rintro ⟨mem,initial,stages⟩
    exact ⟨fun t i => unpack i (mem t i),funext (fun i => by simp [initial,left]),fun v =>
      ⟨(stages v).1,fun i hi => congrArg (unpack i) ((stages v).2 i hi)⟩⟩
  · rintro ⟨mem,initial,stages⟩
    exact ⟨fun t i => pack i (mem t i),by simp [initial],fun v =>
      ⟨by simpa only [encoded,left] using (stages v).1,
       fun i hi => congrArg (pack i) ((stages v).2 i hi)⟩⟩

end
end OAI.Computability.MultitapeWeakETH.TraceNetwork
