import OAI.Hierarchy.ProtocolRAMPurchaseSuccessor
import OAI.Hierarchy.ProtocolRAMPurchaseDFS
import OAI.Hierarchy.ProbeStageChains

namespace OAI
/-! # The global native purchase scan leaves few tiles in each actual CT group -/

namespace Hierarchy.AdaptiveProbe
open ProbeStage ProtocolRAM ProtocolRAMPurchaseOwners
open scoped BigOperators Classical
noncomputable section

/-- Padding each bounded-degree row with `none` retains every true sampler edge. -/
def portDigits {m D : ℕ} (next : Fin m → List (Fin m)) (o : Fin m) (j : Fin D) := (next o)[j.val]?

theorem portDigits_hits {m D : ℕ} (next : Fin m → List (Fin m)) (degree : ∀ o,(next o).length ≤ D)
    (o i : Fin m) : i ∈ next o ↔ ∃ j : Fin D, portDigits next o j=some i := by
  constructor
  · intro mem
    obtain ⟨j,hit⟩ := List.mem_iff_getElem?.mp mem
    obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp hit
    exact ⟨⟨j,bound.trans_le (degree o)⟩,hit⟩
  · rintro ⟨j,hit⟩; exact List.mem_iff_getElem?.mpr ⟨j.val,hit⟩

/-- Editing the occupied port-owner bank to its actual partial inverse realizes exactly
this adjacency. A successful transition stays in its group and takes a true sampler join. -/
theorem native_next {G : Type*} {n D m groups : ℕ} (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups)
    (next : Fin m → List (Fin m)) (degree : ∀ o,(next o).length ≤ D) (r v : Fin n) :
    let choices := successor p enc (D:=D) (portDigits next)
    v ∈ PurchaseDFS.next choices r ↔ p.group v=p.group r ∧ p.input v ∈ next (p.output r) := by
  intro choices
  rw [PurchaseDFS.next,List.reduceOption_mem_iff,List.mem_ofFn]
  constructor
  · rintro ⟨j,hit⟩
    obtain ⟨same,edge⟩ := (successor_eq_some_iff p enc _ r v j).mp hit
    exact ⟨same,(portDigits_hits next degree _ _).mpr ⟨j,edge⟩⟩
  · rintro ⟨same,edge⟩
    obtain ⟨j,hit⟩ := (portDigits_hits next degree _ _).mp edge
    exact ⟨j,(successor_eq_some_iff p enc _ r v j).mpr ⟨same,hit⟩⟩

/-- The padded native DFS runs over *all* records at once. Its final bank nonetheless
satisfies the paper's separate bound on every group, including groups with unoccupied
ports. No independent per-group invocation of the scan is assumed. -/
theorem native_group_residue {G : Type*} [DecidableEq G] {n D m groups : ℕ}
    (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (next : Fin m → List (Fin m))
    (degree : ∀ o, (next o).length ≤ D) {a : ℕ} (ha : 0 < a)
    (mix : SamplerMixes (fun i j => j ∈ next i) a) (h : ℕ) (marked : Finset (Fin n)) (g : G) :
    let choices := successor p enc (D:=D) (portDigits next)
    let left := (scanPaths (PurchaseDFS.candidates choices h) marked).2
    (left.filter fun r => p.group r=g).card < (h+1)*(2*a) := by
  classical
  intro choices left
  let group := left.subtype (fun r => p.group r=g)
  rw [←Finset.card_subtype]
  change group.card < _
  apply remaining_tiles_lt a (h+1) ha (Nat.succ_pos _) (mix.on_tiles (p.outputPort g) (p.inputPort g)) group
  intro f inside path
  let flow : Fin (h+1) ↪ Fin n := f.trans (Function.Embedding.subtype _)
  let list := List.ofFn flow
  have chain : list.IsChain (fun x y => y ∈ PurchaseDFS.next choices x) := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    have bound : i+1 < h+1 := by simpa [list] using hi
    have edge := path i bound
    have live := (native_next p enc next degree (flow ⟨i,by omega⟩) (flow ⟨i+1,bound⟩)).mpr
      ⟨(f ⟨i+1,bound⟩).property.trans (f ⟨i,by omega⟩).property.symm,edge⟩
    simpa only [list,List.getElem_ofFn] using live
  have candidate : list ∈ PurchaseDFS.candidates choices h := (PurchaseDFS.mem_candidates choices).mpr
    ⟨List.length_ofFn,List.nodup_ofFn.mpr flow.injective,chain⟩
  apply (PurchaseDFS.purchase_spec choices h marked).1 list candidate
  intro v hv
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hv)
  exact Finset.mem_subtype.mp (inside j)

/-- Account for a full signed stratum without splitting the program into independent
group jobs. Its marked leftovers partition by true group, so their number is bounded
by the total rounding allowance. -/
theorem native_stage_count {G : Type*} [Fintype G] [DecidableEq G] {n D m groups : ℕ}
    (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (next : Fin m → List (Fin m))
    (degree : ∀ o, (next o).length ≤ D) {a : ℕ} (ha : 0 < a)
    (mix : SamplerMixes (fun i j => j ∈ next i) a) (h : ℕ) (marked : Finset (Fin n)) :
    let choices := successor p enc (D:=D) (portDigits next)
    let result := scanPaths (PurchaseDFS.candidates choices h) marked
    marked.card ≤ result.1.length*(h+1)+Fintype.card G*((h+1)*(2*a)) := by
  intro choices result
  have rem (g : G) := (native_group_residue p enc next degree ha mix h marked g).le
  change ∀ g : G, (result.2.filter fun r => p.group r=g).card ≤ (h+1)*(2*a) at rem
  have count : result.2.card = ∑ g, (result.2.filter fun r => p.group r=g).card :=
    Finset.card_eq_sum_card_fiberwise (fun r _ => Finset.mem_univ (p.group r))
  have total := Finset.sum_le_sum (s:=Finset.univ) fun g _ => rem g
  rw [←count] at total
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at total
  have exact' := (PurchaseDFS.purchase_spec choices h marked).2.2
  change result.1.length*(h+1)+result.2.card=marked.card at exact'
  omega

end
end Hierarchy.AdaptiveProbe

end OAI
