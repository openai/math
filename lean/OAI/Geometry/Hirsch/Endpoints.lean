import OAI.Geometry.Hirsch.Rays

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

variable {I : Type} {n : ℕ} (w : Board I n) (d : Bool) (s : Finset I)

def left := sInf {z | ∃ g ∈ s, w.Shore (!d) g ∧ w.num d g = z}

theorem left_le {g : I} (hg : g ∈ s) (hh : w.Shore (!d) g) : w.left d s ≤ w.num d g :=
  Nat.sInf_le ⟨g,hg,hh,rfl⟩

namespace Round

variable {w} (r : w.Round) (area : Set ℕ) (i : I)

def Straddles := ∃ g ∈ s, r.On area d i g

def right := sInf {z | ∃ g ∈ s, r.On area d i g ∧ w.num d g = z}

variable {area d i s r} {t : Finset I} {H f : ℕ} {b : Budget}

theorem On.right_le {g : I} (ho : r.On area d i g) (hg : g ∈ s) :
    r.right d s area i ≤ w.num d g := Nat.sInf_le ⟨g,hg,ho,rfl⟩

theorem Straddles.endpoint (h : r.Straddles d s area i) :
    ∃ g ∈ s, r.On area d i g ∧ w.num d g = r.right d s area i := by
  obtain ⟨g,hg,ho⟩ := h
  exact Nat.sInf_mem (s := {z | ∃ g ∈ s, r.On area d i g ∧ w.num d g = z}) ⟨_,g,hg,ho,rfl⟩

theorem Straddles.greater (h : r.Straddles d s area i) (hi : w.Shore d i) :
    w.num d i < r.right d s area i := by
  obtain ⟨_,_,ho,he⟩ := h.endpoint
  exact he ▸ ho.strict hi

theorem west (hi : w.place i ∈ area) (hb : flat 1 ≤ b) (hc : (r.test area (!d) b i).Covers s) :
    w.left d s ≤ w.num d i ∧ ∃ g ∈ s, w.Shore (!d) g ∧ w.num d g = w.left d s := by
  obtain ⟨g,hg,ho⟩ := hits hi hb hc
  have hf := ho.info.2.2.1.forward
  have h₁ := w.reverse d i
  have h₂ := w.reverse d g
  have hh : w.num d g ≤ w.num d i := by unfold num at *; omega
  exact ⟨(w.left_le d s hg ho.info.1).trans hh,
    Nat.sInf_mem (s := {z | ∃ g ∈ s, w.Shore (!d) g ∧ w.num d g = z}) ⟨_,g,hg,ho.info.1,rfl⟩⟩

theorem falls_test (r : w.Round) (area : Set ℕ) (d : Bool) (b : Budget) :
    Trial.Falls w.rank (r.test area d b) := by
  rintro g path ⟨_,_,ht⟩ j hj
  exact (ht.member hj).2

theorem keys_inside (hc : (r.test area d b i).Covers s) (hm : (r.test area d b i).Minimal s)
    {g : I} (hg : g ∈ s) : w.place g ∈ area := by
  obtain ⟨l,t,⟨_,_,ht⟩,_⟩ := hm.essential hc hg
  exact (ht.member (by simp : g ∈ l ++ g :: t)).1

def core (r : w.Round) (area : Set ℕ) (d : Bool) (H f : ℕ) (i : I)
    (hi : w.place i ∈ area) (hH : 1 ≤ H) (hf : 2*H ≤ f) : Trial.Core w.rank where
  short := r.test area (!d) (flat H) i
  long := r.test area (!d) (flat f) i
  paths := r.paths area (flat H) i
  near := r.test area (!d) (flat H)
  far := r.test area (!d) (flat (f-H))
  inhabited := by
    obtain ⟨l,⟨j,hj,ht⟩,_⟩ := r.spine hi (!d)
    exact ⟨l,j,hj,ht.more (fun _ => hH)⟩
  includes := fun _ ⟨j,_,ht⟩ => ⟨j,ht⟩
  refines := test_mono _ _ _ _ (fun _ => by simp only [flat]; omega)
  transfer := transfers _ (fun _ => by simp only [Pi.add_apply,flat]; omega)
  nested := fun _ => test_mono _ _ _ _ (fun _ => by simp only [flat]; omega)
  falls := r.falls_test area (!d) (flat H)

variable {hi : w.place i ∈ area} {hH : 1 ≤ H} {hf : 2*H ≤ f}

theorem newer_left (hc : (r.core area d H f i hi hH hf).Cut s)
    (hn : (r.core area d H f i hi hH hf).Newer s t) : w.left d t < w.left d s := by
  have hh := (r.core area d H f i hi hH hf).refines _ hc.1
  obtain ⟨_,g,hg,hw,he⟩ := west hi (fun _ => hH) hh
  have inside := keys_inside hh hc.2 hg
  obtain ⟨j,hj,ho⟩ := hits inside (fun _ => show 1 ≤ f-H by omega) (hn.2.2 g hg).1
  have := ho.strict hw
  have := w.reverse d j
  have := w.reverse d g
  have := w.left_le d t hj ho.info.1
  omega

theorem newer_right (hn : (r.core area d H f i hi hH hf).Newer s t)
    (ht : r.Straddles d t area i) : r.right d s area i < r.right d t area i := by
  obtain ⟨g,hg,ho,he⟩ := ht.endpoint
  obtain ⟨j,hj,hh,hle⟩ := ho.first hg (fun _ => hH) hn.2.1
  exact (hh.right_le hj).trans_lt (hle.trans_eq he)

structure Links (r : w.Round) (d : Bool) (P : I → Prop) : Prop where
  east : ∀ i, r.mark i d → P (w.step i d)
  west : ∀ i, r.mark i (!d) →
    ∃ j, (j = i ∨ r.jump i (!d) j) ∧ w.Middle j ∧ w.live j ∧ P (w.step j d)

theorem Links.divert {P : I → Prop} (h : r.Links d P) {g j : I} {pre rest : List I}
    (ht : r.Trip area i j b (pre ++ g :: rest)) (hw : w.Shore (!d) g) :
    ∃ y l, P y ∧ w.Shore d y ∧ w.place y = w.place g ∧
      r.Trip area i y (b+flat 1) l ∧ l ⊆ pre ++ [g,y] := by
  obtain ⟨u,e,a,hpre,hu,hm,he,hb⟩ := ht.split rfl
  have med := r.middle _ _ hm
  have info := w.middle_step med.1 med.2 e
  have eq := w.shore_inj (he ▸ info.1) hw
  subst e
  obtain ⟨v,hv,hmed,hl,hp⟩ := h.west u hm
  have heq : w.layer v = w.layer u := hv.elim (fun e => by rw [e]) (fun h => (r.localJump _ _ _ h).2.1)
  have place : w.place v = w.place u := congrArg (· / 3) heq
  have pref : ∃ l, r.Trip area i v b l ∧ l ⊆ pre ++ [g] := by
    rcases hv with rfl | hj
    · exact ⟨pre,hpre.more (le_self_add.trans hb),fun _ hh => List.mem_append_left _ hh⟩
    · have hh := (hpre.append (.step hu ⟨med.2,.inr hj⟩)).more hb
      rw [charge,ite_eq_left hm,he] at hh
      exact ⟨_,hh,fun _ h => h⟩
  obtain ⟨l,ht',hs⟩ := pref
  have hy := w.middle_step hmed hl d
  have tail := Trip.step (place.symm ▸ hu) (r.basic hl d)
  refine ⟨_,_,hp,hy.1,hy.2.trans (place.trans (he ▸ info.2.symm)),ht'.append (tail.more ?_),?_⟩
  · intro x; simp only [atLayer,flat]; split <;> omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hs hx; simp_all only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; tauto
    · simp [(r.charge_mem.mp hx).2]

end Round
end OAI.Geometry.Hirsch.Layer.Board
