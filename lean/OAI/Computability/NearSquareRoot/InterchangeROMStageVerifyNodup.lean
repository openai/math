import OAI.Computability.NearSquareRoot.InterchangeROMStageRoles

/-! # Uniqueness of the literal rectangle-stage register addresses -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame

private theorem groups {A B : Type} (xs : List A) (ys : A → List B) (key : B → A)
    (hx : xs.Nodup) (hy : ∀ x, (ys x).Nodup) (hk : ∀ x z, z ∈ ys x → key z = x) :
    (xs.flatMap ys).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun x _ => hy x,hx.imp ?_⟩
  intro i j ne z hi hj
  exact ne ((hk i z hi).symm.trans (hk j z hj))

private theorem local_nodup (g : Frame) (s : Bool) (v : ℕ) :
    (localBoxes g s v).Nodup := List.nodup_range.filter _

private theorem labels_nodup (g : Frame) : (labelsBank g).Nodup :=
  List.nodup_range.map (fun _ _ e => congrArg (fun z : Role => z.2.2.1) e)

private theorem endpoints_nodup (g : Frame) (s : Bool) : (endpoints g s).Nodup := by
  apply groups _ _ (fun z => z.2.2.1) List.nodup_range
  · intro v
    exact (local_nodup g s v).map (fun _ _ e => congrArg (fun z : Role => z.2.2.2) e)
  · intro x z hz
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hz
    rfl

private theorem query_expanded (g : Frame) (s : Bool) :
    queryEndpoints g s = (List.range (queries g)).flatMap fun j =>
      (List.range (labels g)).flatMap fun v => (localBoxes g s v).map (queryEndpoint j v) := by
  simp [queryEndpoints,endpoints,List.map_flatMap,List.map_map,endpoint,Function.comp_def]

private theorem queries_nodup (g : Frame) (s : Bool) : (queryEndpoints g s).Nodup := by
  rw [query_expanded]
  apply groups _ _ (fun z => z.2.1) List.nodup_range
  · intro j
    apply groups _ _ (fun z => z.2.2.1) List.nodup_range
    · intro v
      exact (local_nodup g s v).map (fun _ _ e => congrArg (fun z : Role => z.2.2.2) e)
    · intro x z hz
      obtain ⟨_,_,rfl⟩ := List.mem_map.mp hz
      rfl
  · intro j z hz
    obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp hz
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hv
    rfl

private theorem product_nodup (m n : ℕ) (make : ℕ → ℕ → Role) (right : Role → ℕ)
    (h₁ : ∀ j k, (make j k).2.1 = j) (h₂ : ∀ j k, right (make j k) = k) :
    (product m n make).Nodup := by
  apply groups _ _ (fun z => z.2.1) List.nodup_range
  · intro j
    exact List.nodup_range.map (fun a b e => (h₂ j a).symm.trans ((congrArg right e).trans (h₂ j b)))
  · intro j z hz
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hz
    exact h₁ j k

private theorem terms_nodup (g : Frame) (s : Bool) : (terms g s).Nodup := by
  apply groups _ _ (fun z => z.2.1) List.nodup_range
  · intro j
    apply groups _ _ (fun z => z.2.2.1) List.nodup_range
    · intro i
      apply List.nodup_cons.mpr
      constructor
      · simp [rankTerm]
      · apply (local_nodup g s _).map
        intro a b e
        exact Nat.succ.inj (congrArg (fun z : Role => z.2.2.2) e)
    · intro i z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rfl
      · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hz
        rfl
  · intro j z hz
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hz
    rcases List.mem_cons.mp hi with rfl | hi
    · rfl
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hi
      rfl

private def Tags (xs : List Role) (ts : List ℕ) : Prop := ∀ z ∈ xs, z.1 ∈ ts

private theorem tags_append {xs ys : List Role} {lx ly : List ℕ}
    (hx : Tags xs lx) (hy : Tags ys ly) : Tags (xs++ys) (lx++ly) := by
  intro z hz
  rcases List.mem_append.mp hz with h|h
  · exact List.mem_append_left _ (hx _ h)
  · exact List.mem_append_right _ (hy _ h)

private theorem joinNodup {xs ys : List Role} {lx ly : List ℕ} (hx : xs.Nodup) (hy : ys.Nodup)
    (ax : Tags xs lx) (ay : Tags ys ly) (d : lx.Disjoint ly) : (xs++ys).Nodup :=
  hx.append hy (fun z h k => d (ax z h) (ay z k))

private theorem has_labels (g : Frame) : Tags (labelsBank g) [0] := by
  rintro z h
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp h
  simp [label]

private theorem has_endpoints (g : Frame) (s : Bool) : Tags (endpoints g s) [1] := by
  intro z h
  obtain ⟨_,_,h⟩ := List.mem_flatMap.mp h
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp h
  simp [endpoint]

private theorem has_queries (g : Frame) (s : Bool) : Tags (queryEndpoints g s) [2] := by
  intro z h
  rw [query_expanded] at h
  obtain ⟨_,_,h⟩ := List.mem_flatMap.mp h
  obtain ⟨_,_,h⟩ := List.mem_flatMap.mp h
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp h
  simp [queryEndpoint]

private theorem has_prod (m n : ℕ) (f : ℕ → ℕ → Role) (t : ℕ) (ht : ∀ x y, (f x y).1 = t) :
    Tags (product m n f) [t] := by
  intro z h
  obtain ⟨x,_,h⟩ := List.mem_flatMap.mp h
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp h
  simp [ht]

private theorem has_terms (g : Frame) (s : Bool) : Tags (terms g s) [4] := by
  intro z h
  obtain ⟨_,_,h⟩ := List.mem_flatMap.mp h
  obtain ⟨_,_,h⟩ := List.mem_flatMap.mp h
  rcases List.mem_cons.mp h with rfl | h
  · simp [rankTerm]
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp h
    simp [rankTerm]

theorem bank_nodup (g : Frame) (n : ℕ) : (bank g n).Nodup := by
  have lb := labels_nodup g
  have bt : Tags (boxesBank g) [3] := has_prod _ _ _ _ (fun _ _ => rfl)
  have rt : Tags (rankBank g) [5] := has_prod _ _ _ _ (fun _ _ => rfl)
  have qt : Tags (queryBank g) [6] := has_prod _ _ _ _ (fun _ _ => rfl)
  have bs : (boxesBank g).Nodup := product_nodup _ _ _ (fun z => z.2.2.2) (fun _ _ => rfl) (fun _ _ => rfl)
  have rs : (rankBank g).Nodup := product_nodup _ _ _ (fun z => z.2.2.1) (fun _ _ => rfl) (fun _ _ => rfl)
  have qs : (queryBank g).Nodup := product_nodup _ _ _ (fun z => z.2.2.1) (fun _ _ => rfl) (fun _ _ => rfl)
  have base := joinNodup lb bs (has_labels g) bt (by simp [List.Disjoint])
  have spec := joinNodup lb qs (has_labels g) qt (by simp [List.Disjoint])
  have ep (s) := joinNodup lb (endpoints_nodup g s) (has_labels g) (has_endpoints g s) (by simp [List.Disjoint])
  match n with
  | 0 => exact lb
  | 1 => exact ep false
  | 2 => exact joinNodup lb (queries_nodup g false) (has_labels g) (has_queries g false) (by simp [List.Disjoint])
  | 3 => exact base
  | 4 | 6 =>
    exact joinNodup base (terms_nodup g _) (tags_append (has_labels g) bt) (has_terms g _) (by simp [List.Disjoint])
  | 5 => exact joinNodup base rs (tags_append (has_labels g) bt) rt (by simp [List.Disjoint])
  | 7 => exact joinNodup spec bs (tags_append (has_labels g) qt) bt (by simp [List.Disjoint])
  | 8 => exact joinNodup spec (queries_nodup g true) (tags_append (has_labels g) qt) (has_queries g true) (by simp [List.Disjoint])
  | 9 | 10 => exact ep true
  | _+11 => exact lb

end InterchangeROMStage.Frame

end NearSquareRoot
end Computability
end OAI
