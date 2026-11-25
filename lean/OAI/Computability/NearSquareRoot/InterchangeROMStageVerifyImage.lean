import OAI.Computability.NearSquareRoot.InterchangeROMStageVerify

/-! # Exact image of each typed rectangle register class -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame
open Interchange Interchange.StageLedger

/-- The literal role list contains exactly the image of the injective register encoding. -/
structure Codec {A : Type} (xs : List Role) (enc : A → Role) : Prop where
  injective : Function.Injective enc
  image : ∀ z, z ∈ xs ↔ ∃ a, enc a = z

namespace Codec
variable {A B : Type} {xs ys : List Role} {enc : A → Role} {dec : B → Role}

theorem mem (c : Codec xs enc) (a : A) : enc a ∈ xs := (c.image _).mpr ⟨a,rfl⟩

theorem append (a : Codec xs enc) (b : Codec ys dec) (nd : (xs++ys).Nodup) :
    Codec (xs++ys) (Sum.elim enc dec) := by
  have dj := nd.disjoint
  constructor
  · rintro (x|y) (x'|y') e
    · exact congrArg Sum.inl (a.injective e)
    · change enc x = dec y' at e
      exact False.elim (dj (a.mem x) (e.symm ▸ b.mem y'))
    · change dec y = enc x' at e
      exact False.elim (dj (a.mem x') (e ▸ b.mem y))
    · exact congrArg Sum.inr (b.injective e)
  · intro z
    rw [List.mem_append,a.image,b.image]
    constructor
    · rintro (⟨u,rfl⟩| ⟨v,rfl⟩)
      · exact ⟨.inl u,rfl⟩
      · exact ⟨.inr v,rfl⟩
    · rintro ⟨(x|y),rfl⟩
      · exact Or.inl ⟨x,rfl⟩
      · exact Or.inr ⟨y,rfl⟩

end Codec

namespace Realization

variable {g : Frame} (r : Realization g)

theorem label_codec : Codec (labelsBank g) (labelCode (g:=g)) := by
  constructor
  · intro a b e
    exact Fin.ext (congrArg (fun z : Role => z.2.2.1) e)
  · intro z
    constructor
    · intro h
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
      exact ⟨⟨v,List.mem_range.mp hv⟩,rfl⟩
    · rintro ⟨v,rfl⟩
      exact List.mem_map.mpr ⟨v.val,List.mem_range.mpr v.isLt,rfl⟩

private theorem prod_codec (m n : ℕ) (f : ℕ → ℕ → Role) (right : Role → ℕ)
    (h₁ : ∀ j k, (f j k).2.1 = j) (h₂ : ∀ j k, right (f j k) = k) :
    Codec (product m n f) (fun p : Fin m × Fin n => f p.1 p.2) := by
  constructor
  · rintro ⟨j,k⟩ ⟨j',k'⟩ e
    apply Prod.ext <;> apply Fin.ext
    · exact (h₁ j k).symm.trans ((congrArg (fun z : Role => z.2.1) e).trans (h₁ j' k'))
    · exact (h₂ j k).symm.trans ((congrArg right e).trans (h₂ j' k'))
  · intro z
    constructor
    · intro h
      obtain ⟨j,hj,h⟩ := List.mem_flatMap.mp h
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
      exact ⟨(⟨j,List.mem_range.mp hj⟩,⟨k,List.mem_range.mp hk⟩),rfl⟩
    · rintro ⟨⟨j,k⟩,rfl⟩
      exact List.mem_flatMap.mpr ⟨j.val,List.mem_range.mpr j.isLt,
        List.mem_map.mpr ⟨k.val,List.mem_range.mpr k.isLt,rfl⟩⟩

theorem box_codec : Codec (boxesBank g) (boxCode (g:=g)) :=
  prod_codec _ _ _ (fun z => z.2.2.2) (fun _ _ => rfl) (fun _ _ => rfl)

theorem rank_codec : Codec (rankBank g) r.rankCode := by
  rw [rankBank,r.minor_length]
  exact prod_codec _ _ _ (fun z => z.2.2.1) (fun _ _ => rfl) (fun _ _ => rfl)

theorem query_codec : Codec (queryBank g) (queryCode (g:=g)) :=
  prod_codec _ _ _ (fun z => z.2.2.1) (fun _ _ => rfl) (fun _ _ => rfl)

theorem endpoint_codec (s : Bool) : Codec (endpoints g s) (r.endpointCode (s:=s)) := by
  constructor
  · rintro ⟨⟨v,hv⟩,⟨⟨b,hb⟩,hi⟩⟩ ⟨⟨v',hv'⟩,⟨⟨b',hb'⟩,hi'⟩⟩ e
    obtain ⟨rfl,rfl⟩ : v = v' ∧ b = b' :=
      ⟨congrArg (fun z : Role => z.2.2.1) e,congrArg (fun z : Role => z.2.2.2) e⟩
    rfl
  · intro z
    constructor
    · intro h
      obtain ⟨v,hv,h⟩ := List.mem_flatMap.mp h
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
      obtain ⟨hb,hi⟩ := List.mem_filter.mp hb
      let v' : Fin (labels g) := ⟨v,List.mem_range.mp hv⟩
      let b' : Fin (boxes g) := ⟨b,List.mem_range.mp hb⟩
      exact ⟨⟨v',⟨b',(r.incident_iff s v' b').mp hi⟩⟩,rfl⟩
    · rintro ⟨⟨v,b,h⟩,rfl⟩
      exact (endpoint_mem g s v b).mpr ⟨v.isLt,b.isLt,(r.incident_iff s v b).mpr h⟩

theorem queryEndpoint_codec (s : Bool) :
    Codec (queryEndpoints g s) (r.queryEndpointCode (s:=s)) := by
  constructor
  · rintro ⟨j,e⟩ ⟨j',e'⟩ h
    apply Prod.ext
    · exact Fin.ext (congrArg (fun z : Role => z.2.1) h)
    · apply (r.endpoint_codec s).injective
      exact congrArg (fun z : Role => endpoint z.2.2.1 z.2.2.2) h
  · intro z
    constructor
    · intro h
      obtain ⟨j,hj,h⟩ := List.mem_flatMap.mp h
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
      obtain ⟨e,rfl⟩ := ((r.endpoint_codec s).image _).mp he
      exact ⟨(⟨j,List.mem_range.mp hj⟩,e),rfl⟩
    · rintro ⟨⟨j,e⟩,rfl⟩
      exact (queryEndpoint_mem g s j e.1 e.2.1).mpr
        ⟨j.isLt,e.1.isLt,e.2.1.isLt,(r.incident_iff s e.1 e.2.1).mpr e.2.2⟩

private theorem term_injective (s : Bool) : Function.Injective (r.termCode (s:=s)) := by
  rintro ⟨⟨j,hj⟩,⟨⟨i,hi⟩,o⟩⟩ ⟨⟨j',hj'⟩,⟨⟨i',hi'⟩,o'⟩⟩ h
  obtain ⟨rfl,rfl⟩ : j = j' ∧ i = i' :=
    ⟨congrArg (fun z : Role => z.2.1) h,congrArg (fun z : Role => z.2.2.1) h⟩
  have hk := congrArg (fun z : Role => z.2.2.2) h
  cases o with
  | none => cases o' <;> simp_all [termCode,rankTerm]
  | some b =>
    cases o' with
    | none => simp [termCode,rankTerm] at hk
    | some c =>
      have bc : b = c := Subtype.ext (Fin.ext (Nat.succ.inj hk))
      subst c
      rfl

theorem term_codec (s : Bool) : Codec (terms g s) (r.termCode (s:=s)) := by
  refine ⟨r.term_injective s,?_⟩
  intro z
  constructor
  · intro h
    obtain ⟨j,hj,h⟩ := List.mem_flatMap.mp h
    obtain ⟨i,hi,h⟩ := List.mem_flatMap.mp h
    let j' : Fin (queries g) := ⟨j,List.mem_range.mp hj⟩
    let i' : Fin r.rank := ⟨i,r.minor_length s ▸ List.mem_range.mp hi⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(j',⟨i',none⟩),rfl⟩
    · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
      obtain ⟨hb,hm⟩ := List.mem_filter.mp hb
      let b' : Fin (boxes g) := ⟨b,List.mem_range.mp hb⟩
      have ho : (minor g s)[i]? = some (r.sel s i').val := r.minor_get s i'
      rw [ho] at hm
      exact ⟨(j',⟨i',some ⟨b',(r.incident_iff s (r.sel s i') b').mp hm⟩⟩),rfl⟩
  · rintro ⟨⟨j,⟨i,o⟩⟩,rfl⟩
    refine List.mem_flatMap.mpr ⟨j.val,List.mem_range.mpr j.isLt,?_⟩
    refine List.mem_flatMap.mpr ⟨i.val,List.mem_range.mpr ((r.minor_length s).symm ▸ i.isLt),?_⟩
    cases o with
    | none => exact List.mem_cons_self
    | some b =>
      apply List.mem_cons_of_mem _
      apply List.mem_map.mpr
      refine ⟨b.1.val,List.mem_filter.mpr ⟨List.mem_range.mpr b.1.isLt,?_⟩,rfl⟩
      rw [r.minor_get s i]
      exact (r.incident_iff s (r.sel s i) b.1).mpr b.2

end Realization
end InterchangeROMStage.Frame

end NearSquareRoot
end Computability
end OAI
