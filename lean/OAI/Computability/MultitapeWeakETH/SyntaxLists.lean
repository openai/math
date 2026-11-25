import OAI.Computability.MultitapeWeakETH.FormulaSwitchProgram
import OAI.Computability.MultitapeWeakETH.RankProgram

/-! # Explicit syntax-key lists for the trivalent site and wire tables -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork

open Algorithms.SubexponentialSAT
open scoped Classical
noncomputable section

variable {n : ℕ} (F : SAT.CNF (Fin n))

/-- Each occurrence is named by one literal code followed by its clause's codes. -/
def occurrences (cs : List (List ℕ)) := cs.flatMap fun c => c.map fun l => l :: c

private theorem clause_mem {c : List ℕ} : c ∈ Encoding.cnfNumbers F ↔ ∃ b : ↥F, Encoding.clauseNumbers b.val = c := by
  simp [Encoding.cnfNumbers]

private theorem literal_mem (b : SAT.Clause (Fin n)) {l : ℕ} :
    l ∈ Encoding.clauseNumbers b ↔ ∃ a : ↥b, Encoding.literalCode a.val = l := by
  simp [Encoding.clauseNumbers]

/-- Complete and duplicate-free listing of occurrence keys in the concrete
formula body. The statement includes zero-length clauses. -/
theorem occurrence_list :
    (occurrences (Encoding.cnfNumbers F)).Nodup ∧ ∀ x, x ∈ occurrences (Encoding.cnfNumbers F) ↔
      ∃ p : Occ F, occKey F p = x := by
  constructor
  · apply List.nodup_flatMap.mpr
    constructor
    · intro c hc
      obtain ⟨b,rfl⟩ := (clause_mem F).mp hc
      exact (Finset.sort_nodup ..).map (fun x y h => (List.cons.inj h).1)
    · apply List.Pairwise.imp _ (Finset.sort_nodup ..)
      intro c d ne
      apply List.disjoint_left.mpr
      intro z hz hw
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
      obtain ⟨y,_,eq⟩ := List.mem_map.mp hw
      exact ne (List.cons.inj eq).2.symm
  · intro x
    constructor
    · intro hx
      obtain ⟨c,hc,hw⟩ := List.mem_flatMap.mp hx
      obtain ⟨b,rfl⟩ := (clause_mem F).mp hc
      obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hw
      obtain ⟨a,rfl⟩ := (literal_mem b.val).mp hl
      exact ⟨⟨b,a⟩,rfl⟩
    · rintro ⟨⟨b,a⟩,rfl⟩
      exact List.mem_flatMap.mpr ⟨_,(clause_mem F).mpr ⟨b,rfl⟩,
        List.mem_map.mpr ⟨_,(literal_mem b.val).mpr ⟨a,rfl⟩,rfl⟩⟩

def realSlot (x : List ℕ) := x.headD 0 / 2 :: 0 :: x

theorem realSlot_occ (p : Occ F) : realSlot (occKey F p) = slotKey F (atOcc F p) := by
  change Encoding.literalCode p.2.val / 2 :: _ = p.2.val.variable.val :: _
  rw [show Encoding.literalCode p.2.val / 2 = p.2.val.variable.val by
    unfold Encoding.literalCode
    split <;> omega]
  rfl

def slots (n : ℕ) (cs : List (List ℕ)) :=
  (List.range n).map (fun v => [v]) ++ (occurrences cs).map realSlot

theorem slot_list :
    (slots n (Encoding.cnfNumbers F)).Nodup ∧ ∀ x, x ∈ slots n (Encoding.cnfNumbers F) ↔
      ∃ s : Slot F, slotKey F s = x := by
  obtain ⟨nd,mem⟩ := occurrence_list F
  constructor
  · apply List.nodup_append.mpr
    refine ⟨List.nodup_range.map (fun _ _ h => (List.cons.inj h).1),nd.map ?_,?_⟩
    · exact fun _ _ h => (List.cons.inj (List.cons.inj h).2).2
    · intro z hz _ hw same
      subst_vars
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz
      obtain ⟨_,_,eq⟩ := List.mem_map.mp hw
      simp [realSlot] at eq
  · intro x
    constructor
    · intro hx
      rcases List.mem_append.mp hx with l | r
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp l
        exact ⟨⟨⟨v,List.mem_range.mp hv⟩,none⟩,rfl⟩
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp r
        obtain ⟨p,rfl⟩ := (mem w).mp hw
        exact ⟨atOcc F p,(realSlot_occ F p).symm⟩
    · rintro ⟨⟨v,o⟩,rfl⟩
      cases o with
      | none => exact List.mem_append_left _ (List.mem_map.mpr ⟨v.val,List.mem_range.mpr v.isLt,rfl⟩)
      | some p =>
        apply List.mem_append_right
        refine List.mem_map.mpr ⟨occKey F p.val,(mem _).mpr ⟨_,rfl⟩,?_⟩
        obtain ⟨p,rfl⟩ := p
        exact realSlot_occ F p

/-- Tags separate the two sides of each disjoint union. -/
def joinKeys (a b : List (List ℕ)) := a.map (0::·) ++ b.map (1::·)

private theorem joinKeys_spec {A B : Type} (a b : List (List ℕ)) (keyA : A → List ℕ) (keyB : B → List ℕ)
    (ha : a.Nodup ∧ ∀ x, x ∈ a ↔ ∃ v, keyA v = x) (hb : b.Nodup ∧ ∀ x, x ∈ b ↔ ∃ v, keyB v = x) :
    (joinKeys a b).Nodup ∧ ∀ x, x ∈ joinKeys a b ↔
      ∃ v : A ⊕ B, Sum.elim (fun v => 0 :: keyA v) (fun v => 1 :: keyB v) v = x := by
  constructor
  · apply List.nodup_append.mpr
    refine ⟨ha.1.map (fun _ _ h => (List.cons.inj h).2),hb.1.map (fun _ _ h => (List.cons.inj h).2),?_⟩
    simp
  · intro x
    simp [joinKeys,ha.2,hb.2,Sum.exists]

def siteKeys (n : ℕ) (cs : List (List ℕ)) := joinKeys (slots n cs) cs
def wireKeys (n : ℕ) (cs : List (List ℕ)) := joinKeys (slots n cs) (occurrences cs)
def endKeys (n : ℕ) (cs : List (List ℕ)) := joinKeys (wireKeys n cs) (wireKeys n cs)

theorem site_list :
    (siteKeys n (Encoding.cnfNumbers F)).Nodup ∧ ∀ x, x ∈ siteKeys n (Encoding.cnfNumbers F) ↔
      ∃ s : Site F, siteKey F s = x :=
  joinKeys_spec _ _ _ _ (slot_list F) ⟨Finset.sort_nodup ..,fun _ => clause_mem F⟩

theorem end_list :
    (endKeys n (Encoding.cnfNumbers F)).Nodup ∧ ∀ x, x ∈ endKeys n (Encoding.cnfNumbers F) ↔
      ∃ e : End F, endKey F e = x := by
  have wires := joinKeys_spec _ _ _ _ (slot_list F) (occurrence_list F)
  exact joinKeys_spec _ _ _ _ wires wires

private theorem occ_length (width : SAT.WidthAtMost 3 F) (p : Occ F) :
    ((occKey F) p).length ≤ 4 := by
  change (_ :: Encoding.clauseNumbers p.1.val).length ≤ 4
  exact Nat.succ_le_succ ((Encoding.length_clauseNumbers _).trans_le (width _ p.1.property))

theorem slot_length (width : SAT.WidthAtMost 3 F) (s : Slot F) :
    ((slotKey F) s).length ≤ 6 := by
  obtain ⟨v, _ | p⟩ := s
  · exact Nat.succ_le_succ (Nat.zero_le _)
  · exact Nat.succ_le_succ (Nat.succ_le_succ (occ_length F width p.val))

theorem site_length (width : SAT.WidthAtMost 3 F) (v : Site F) :
    ((siteKey F) v).length ≤ 7 := by
  cases v with
  | inl s => exact Nat.succ_le_succ (slot_length F width s)
  | inr c =>
    change (_ :: Encoding.clauseNumbers c.val).length ≤ 7
    simp only [List.length_cons, Encoding.length_clauseNumbers]
    have := width _ c.property
    omega

theorem end_length (width : SAT.WidthAtMost 3 F) (e : End F) :
    ((endKey F) e).length ≤ 8 := by
  rcases e with (s | p) | (s | p)
  all_goals first
    | exact Nat.succ_le_succ (Nat.succ_le_succ (slot_length F width s))
    | exact Nat.succ_le_succ (Nat.succ_le_succ ((occ_length F width p).trans (by decide : 4 ≤ 6)))

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork
