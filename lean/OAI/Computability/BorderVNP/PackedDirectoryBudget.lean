import OAI.Computability.BorderVNP.PackedDirectoryInverse

/-! # Source traffic of the executable Section 7.3 delivery directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

/-- Bits of the compact directory classified by their original candidate and source team.
Empty intersections have empty fibers, exactly as in the compacting writer. -/
abbrev SourceBits (d : Layout) (pp lp : ℕ → ℕ × ℕ) (team : ℕ) :=
  (i : Fin d.candidates) × Fin (if (d.row pp lp i).team = team then (d.row pp lp i).width else 0)

/-- Each private-tail bit may be sourced once in addition to its occurrence among the
ordinary literal pins. Additional-field bits occupy their own addresses. -/
abbrev SourceSlots (d : Layout) :=
  (Fin d.processors × Fin (d.literal/2)) ⊕ (Fin d.processors × Fin d.fields × Fin d.literal)

private def decode (d : Layout) (team : ℕ) : SourceSlots d → ℕ × ℕ
  | .inl (p,a) => d.recoverPrivate team p a
  | .inr (p,f,a) => d.recoverLive team p f a

private theorem liveReencode (d : Layout) (i : ℕ) (hi : 2*d.entries ≤ i) :
    let j := i-2*d.entries
    let k := d.literal/d.block+2
    let u := j/k
    let a := u/d.fields
    d.liveIndex (a/d.processors) (a%d.processors) (u%d.fields) (j%k) = i := by
  simp only [Layout.liveIndex,Nat.div_add_mod]
  rw [Nat.add_assoc,Nat.div_add_mod,Nat.add_sub_of_le hi]

private theorem reconstruct (d : Layout) (pp lp : ℕ → ℕ × ℕ) (team : ℕ)
    (hp : 0 < d.processors) (hf : 0 < d.fields) (hb : 0 < d.block)
    (b : SourceBits d pp lp team) : ∃ a : SourceSlots d, decode d team a = (b.1.val,b.2.val) := by
  obtain ⟨i,e⟩ := b
  let row := d.row pp lp i
  have he := e.isLt
  change e.val < (if row.team = team then row.width else 0) at he
  by_cases hteam : row.team = team
  · have hwidth : e.val < row.width := he.trans_eq (ite_eq_left hteam)
    by_cases priv : i.val < 2*d.entries
    · let j := i.val/2
      let k := i.val%2
      have er : row = d.privateRow pp j k := by simp only [row,Layout.row,priv,ite_true,j,k]
      have hr : row.processor < d.processors := by
        rw [er]
        exact Nat.mod_lt _ hp
      have hh := d.recover_privateRow pp j k e.val (er ▸ hwidth)
      rw [← er] at hh
      obtain ⟨ht,hback⟩ := hh
      let a : SourceSlots d := .inl (⟨row.processor,hr⟩,⟨row.offset+e-(d.literal-d.literal/2),ht⟩)
      refine ⟨a,?_⟩
      change d.recoverPrivate team row.processor _ = _
      exact ((congrArg (fun t => d.recoverPrivate t row.processor (row.offset+e-(d.literal-d.literal/2))) hteam.symm).trans hback).trans (Prod.ext (Nat.div_add_mod i.val 2) rfl)
    · let j := i.val-2*d.entries
      let k := d.literal/d.block+2
      let u := j/k
      let a := u/d.fields
      let t := a/d.processors
      let p := a%d.processors
      let f := u%d.fields
      let step := j%k
      have er : row = d.liveRow lp t p f step := by simp only [row,Layout.row,priv,ite_false,t,p,f,step,a,u,j,k]
      have hh := d.recover_liveRow lp t p f step e.val hb (er ▸ hwidth)
      rw [← er] at hh
      obtain ⟨ht,hback⟩ := hh
      have hr : row.processor < d.processors := er ▸ Nat.mod_lt _ hp
      have hfield : row.field < d.fields := er ▸ Nat.mod_lt _ hf
      let s : SourceSlots d := .inr (⟨row.processor,hr⟩,⟨row.field,hfield⟩,⟨row.offset+e,ht⟩)
      refine ⟨s,?_⟩
      change d.recoverLive team row.processor row.field (row.offset+e) = _
      exact ((congrArg (fun t => d.recoverLive t row.processor row.field (row.offset+e)) hteam.symm).trans hback).trans (Prod.ext (liveReencode d i.val (by omega)) rfl)
  · exact (Nat.not_lt_zero _ (he.trans_eq (ite_eq_right hteam))).elim

/-- Source bits carried by the actual compact directory inject into the distinct
processor-tail and literal/extra field positions within their source team. -/
theorem Layout.outgoing_bound (d : Layout) (pp lp : ℕ → ℕ × ℕ) (team : ℕ)
    (hp : 0 < d.processors) (hf : 0 < d.fields) (hb : 0 < d.block) :
    (∑ i : Fin d.candidates, if (d.row pp lp i).team = team then (d.row pp lp i).width else 0) ≤
      d.processors*(d.literal/2) + d.processors*(d.fields*d.literal) := by
  classical
  let addr (b : SourceBits d pp lp team) := Classical.choose (reconstruct d pp lp team hp hf hb b)
  have inv (b : SourceBits d pp lp team) : decode d team (addr b) = (b.1.val,b.2.val) :=
    Classical.choose_spec (reconstruct d pp lp team hp hf hb b)
  have hinj : Function.Injective addr := by
    rintro ⟨i,e⟩ ⟨j,f⟩ eq
    have h := (inv ⟨i,e⟩).symm.trans ((congrArg (decode d team) eq).trans (inv ⟨j,f⟩))
    have hij : i = j := Fin.ext (congrArg Prod.fst h)
    subst j
    exact congrArg (Sigma.mk i) (Fin.ext (congrArg Prod.snd h))
  simpa only [SourceBits,SourceSlots,Fintype.card_sigma,Fintype.card_fin,Fintype.card_sum,
    Fintype.card_prod] using Fintype.card_le_of_injective addr hinj

/-- The same outgoing bound holds when summed directly over the populated rows read
by the router. This gives at most twice the team's literal width for one source field
and at most three times that width when the additional pinned field is present. -/
theorem Layout.populated_outgoing (d : Layout) (pp lp : ℕ → ℕ × ℕ) (team : ℕ)
    (hp : 0 < d.processors) (hf : 0 < d.fields) (hb : 0 < d.block) :
    ((d.directory pp lp).map fun r => if r.team = team then r.width else 0).sum ≤
      (d.fields+1)*(d.processors*d.literal) := by
  let cost (r : Row) := if r.team = team then r.width else 0
  have del (xs : List Row) :
      ((xs.filter fun r => 0 < r.width).map cost).sum = (xs.map cost).sum := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      by_cases h : 0 < x.width
      · simp [h,ih]
      · have h0 : x.width = 0 := by omega
        simp [ih,cost,h0]
  have eq : ((d.directory pp lp).map cost).sum =
      ∑ i : Fin d.candidates, cost (d.row pp lp i) := by
    rw [directory,del,List.map_map,Finset.sum_fin_eq_sum_range]
    rw [← List.sum_toFinset (cost ∘ d.row pp lp) List.nodup_range, List.toFinset_range]
    exact Finset.sum_congr rfl (fun i hi => by simp [Finset.mem_range.mp hi])
  change ((d.directory pp lp).map cost).sum ≤ _
  rw [eq]
  calc
    _ ≤ _ := d.outgoing_bound pp lp team hp hf hb
    _ ≤ d.processors*d.literal+d.processors*(d.fields*d.literal) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.div_le_self ..)) _
    _ = _ := by ring

end Packing.Directory

end BorderVNP
end Computability
end OAI
