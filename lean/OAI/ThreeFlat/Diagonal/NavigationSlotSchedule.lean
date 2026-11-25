import OAI.ThreeFlat.Diagonal.NavigationRootPublication
import OAI.ThreeFlat.RAM.TickTerminalPrepare
import OAI.ThreeFlat.RAM.TickSelectedFiber
import OAI.ThreeFlat.Diagonal.TickEvaluationProduct

namespace OAI
/-! # Reading each true work-bounded processor slot in chronological root order -/

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive

open Computability.VPVNP.BurstRAM RAM LinearAlgebra.SpectralBooks.VNP TickGreedyReplay HistoryContraction
open scoped BigOperators Fin.CommRing

variable {W : ℕ}

def groupBlocks (a : RootArchive) (N : Nodes a) :=
  schedule a.groups (Team.ticks N.work a.ids) a.totalPairs N.work N.pairs a.ids

def groupBlock (a : RootArchive) (N : Nodes a) (g : ℕ) := ((a.groupBlocks N)[g]?).getD []

def slotBlocks (a : RootArchive) (N : Nodes a) (slots g : ℕ) :=
  (Team.handoff N.work (a.slotBudget/4) slots (a.groupBlock N g)).1

def slotBlock (a : RootArchive) (N : Nodes a) (slots g s : ℕ) : List (Fin a.rootCount) :=
  ((a.slotBlocks N slots g)[s]?).getD []

theorem groupBlocks_length (a : RootArchive) (N : Nodes a) : (a.groupBlocks N).length=a.groups :=
  Team.handoff_length ..

theorem slotBlocks_length (a : RootArchive) (N : Nodes a) (slots g : ℕ) :
    (a.slotBlocks N slots g).length=slots := Team.handoff_length ..

private theorem actual_block_charge {α : Type*} (work : α→ℕ) (lim : ℕ) (data : List α)
    (blocks : List (List α)) (rest : List α) (h : Team.ValidHandoff work lim data blocks rest)
    {b : List α} (hb : b∈blocks) : Team.ticks work b≤lim := by
  induction blocks generalizing data with
  | nil=>simp at hb
  | cons hd tl ih=>
    obtain ⟨next,_,head,tail⟩:=h
    rcases List.mem_cons.mp hb with rfl|mem
    · exact head.1
    · exact ih next tail mem

theorem slotBlock_budget (a : RootArchive) (N : Nodes a) (slots g s : ℕ) :
    Team.ticks N.work (a.slotBlock N slots g s)≤a.slotBudget/4 := by
  by_cases hs : s<(a.slotBlocks N slots g).length
  · simp only [slotBlock,List.getElem?_eq_getElem hs,Option.getD_some]
    exact actual_block_charge N.work (a.slotBudget/4) (a.groupBlock N g) (a.slotBlocks N slots g) _ (Team.handoff_valid N.work (a.slotBudget/4) slots (a.groupBlock N g)) (List.getElem_mem hs)
  · simp [slotBlock,List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hs),Team.ticks]

theorem slotBlock_sum (a : RootArchive) (N : Nodes a) (slots g s : ℕ)
    (f : Fin a.rootCount→ℕ) (charge : ∀ i∈a.slotBlock N slots g s,f i≤N.work i) :
    ((a.slotBlock N slots g s).map f).sum≤a.slotBudget/4 := by
  apply Nat.le_trans _ (a.slotBlock_budget N slots g s)
  change _≤((a.slotBlock N slots g s).map N.work).sum
  generalize a.slotBlock N slots g s=bs at charge ⊢
  induction bs with
  | nil=>rfl
  | cons b bs ih=>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (charge b List.mem_cons_self) (ih (fun x h=>charge x (List.mem_cons_of_mem _ h)))

/-- Every genuine group is exactly flattened by the available chronological slots. -/
theorem slotBlocks_flatten (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (h : ScheduleFacts a W slots N.work N.pairs a.ids) (g : Fin a.groups) :
    (a.slotBlocks N slots g.val).flatten=a.groupBlock N g.val := by
  have gi : g.val<(a.groupBlocks N).length := by rw [groupBlocks_length];exact g.isLt
  have member : a.groupBlock N g.val∈a.groupBlocks N := by
    simp only [groupBlock,List.getElem?_eq_getElem gi,Option.getD_some]
    exact List.getElem_mem gi
  have full:=Team.handoff_flatten N.work (a.slotBudget/4) slots (a.groupBlock N g.val)
  rw [h.covered _ member,List.append_nil] at full
  exact full

theorem groupBlocks_flatten (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (h : ScheduleFacts a W slots N.work N.pairs a.ids) : (a.groupBlocks N).flatten=a.ids :=
  (schedule_spec h.groups h.nonempty h.pairPositive N.work N.pairs a.ids h.positive le_rfl h.pairBound h.cell).2.1

def tags (a : RootArchive) (N : Nodes a) (slots : ℕ) :=
  labelBoth (fun b=>label 0 (Team.handoff N.work (a.slotBudget/4) slots b).1) 0 (a.groupBlocks N)

private theorem label_slot_lt {α : Type*} (v : ℕ×α) (base : ℕ) (bs : List (List α))
    (hv : v∈label base bs) : v.1<base+bs.length := by
  induction bs generalizing base with
  | nil=>simp [label] at hv
  | cons b bs ih=>
    rw [label,List.mem_append] at hv
    rcases hv with here|tail
    · obtain ⟨i,_,rfl⟩:=List.mem_map.mp here
      simp
    · have:=ih (base+1) tail
      simp only [List.length_cons];omega

private theorem tag_bounds {α : Type*} (f : List α→List (ℕ×α)) (slots i : ℕ) (gs : List (List α))
    (bounded : ∀ b∈gs,∀ y∈f b,y.1<slots) (x : (ℕ×ℕ)×α) (hx : x∈labelBoth f i gs) :
    x.1.1< i+gs.length ∧ x.1.2<slots := by
  induction gs generalizing i with
  | nil=>simp [labelBoth] at hx
  | cons b gs ih=>
    rw [labelBoth,List.mem_append] at hx
    rcases hx with here|tail
    · obtain ⟨y,hy,rfl⟩:=List.mem_map.mp here
      exact ⟨by simp,bounded b List.mem_cons_self y hy⟩
    · have h:=ih (i+1) (fun b hb=>bounded b (List.mem_cons_of_mem _ hb)) tail
      exact ⟨by simp only [List.length_cons];omega,h.2⟩

theorem tags_bounded (a : RootArchive) (N : Nodes a) (slots : ℕ) (x) (hx : x∈a.tags N slots) :
    x.1.1<a.groups ∧ x.1.2<slots := by
  have h:=tag_bounds _ slots 0 (a.groupBlocks N) (fun b _ y hy=>by
    have t:=label_slot_lt y 0 (Team.handoff N.work (a.slotBudget/4) slots b).1 hy
    simpa only [Nat.zero_add,Team.handoff_length] using t) x hx
  simpa only [Nat.zero_add,groupBlocks_length] using h

theorem tags_length (a : RootArchive) (N : Nodes a) (slots : ℕ) (h : ScheduleFacts a W slots N.work N.pairs a.ids) :
    (a.tags N slots).length=a.rootCount := by
  have eq : (a.scheduled (W:=W) slots N.work N.pairs a.ids)=(a.tags N slots).map RAM.TickGreedyNat.owner:=rfl
  have l:=a.scheduled_length slots N.work N.pairs a.ids h
  rw [eq, List.length_map] at l
  simpa only [ids, List.length_ofFn] using l

def ordinalOwner (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (h : ScheduleFacts a W slots N.work N.pairs a.ids) (i : Fin a.rootCount) : ℕ×ℕ :=
  ((a.tags N slots)[i.val]'(by rw [tags_length a N slots h];exact i.isLt)).1

theorem owner_bounded (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (h : ScheduleFacts a W slots N.work N.pairs a.ids) (i : Fin a.rootCount) :
    (a.ordinalOwner N slots h i).1<a.groups ∧ (a.ordinalOwner N slots h i).2<slots := by
  exact a.tags_bounded N slots _ (List.getElem_mem (by rw [a.tags_length N slots h];exact i.isLt))

def slotOf (a : RootArchive) (N : Nodes a) (slots : ℕ) (h : ScheduleFacts a W slots N.work N.pairs a.ids)
    (i : Fin a.rootCount) : Fin slots :=
  ⟨(a.ordinalOwner N slots h i).2,(a.owner_bounded N slots h i).2⟩

theorem slot_owner_words (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (h : ScheduleFacts a W slots N.work N.pairs a.ids) (i : Fin a.rootCount) :
    a.scheduledOwner (W:=W) N slots i.val=
      (((a.ordinalOwner N slots h i).1:Word W),((a.ordinalOwner N slots h i).2:Word W)) := by
  have index : i.val<(a.tags N slots).length := by rw [a.tags_length N slots h];exact i.isLt
  change (((a.tags N slots).map RAM.TickGreedyNat.owner)[i.val]?).getD (0,0)=_
  rw [List.getElem?_eq_getElem (by simpa using index),List.getElem_map]
  rfl

theorem groupOf_ordinal (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (h : ScheduleFacts a W slots N.work N.pairs a.ids) (fit : a.groups<2^W) (i : Fin a.rootCount) :
    (a.groupOf N slots h fit i).val=(a.ordinalOwner N slots h i).1 := by
  have index : i.val<(a.scheduled (W:=W) slots N.work N.pairs a.ids).length := by
    rw [a.scheduled_length slots N.work N.pairs a.ids h];simp [ids]
  have r:=congrArg (fun z : Word W×Word W=>z.1.val) (a.slot_owner_words N slots h i)
  have bound:=(a.owner_bounded N slots h i).1.trans fit
  simpa only [groupOf,scheduledOwner,List.getElem?_eq_getElem index,Option.getD_some,Fin.val_cast_of_lt bound] using r

theorem finite_owner_words (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (h : ScheduleFacts a W slots N.work N.pairs a.ids) (gf : a.groups<2^W) (i : Fin a.rootCount) :
    a.scheduledOwner (W:=W) N slots i.val=
      (((a.groupOf N slots h gf i).val:Word W),((a.slotOf N slots h i).val:Word W)) := by
  rw [a.groupOf_ordinal N slots h gf i]
  exact a.slot_owner_words N slots h i

theorem slotBlock_filter (a : RootArchive) (N : Nodes a) (slots g s : ℕ)
    (h : ScheduleFacts a W slots N.work N.pairs a.ids) :
    (List.finRange a.rootCount).filter (fun i=>decide (a.ordinalOwner N slots h i=(g,s))) =
      a.slotBlock N slots g s := by
  apply finRange_filter_slot N.work (a.slotBudget/4) slots (a.groupBlocks N) g s (a.ordinalOwner N slots h)
  · exact (a.groupBlocks_flatten N slots h).trans (List.ofFn_id a.rootCount)
  · exact h.covered
  · intro i
    change ((a.tags N slots)[i.val]?).map Prod.fst=_
    have ix : i.val<(a.tags N slots).length:=by rw [a.tags_length N slots h];exact i.isLt
    simp only [List.getElem?_eq_getElem ix,Option.map_some,ordinalOwner]

private theorem ticks_filtered {α : Type*} (pay : α→ℕ) (p : α→Prop) [DecidablePred p]
    (xs : List α) : Team.ticks pay (xs.filter (fun i=>decide (p i))) =
      (xs.map (fun i=>if p i then pay i else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hit : p x
    · simpa [Team.ticks,hit] using congrArg (fun z=>pay x+z) ih
    · simpa [Team.ticks,hit] using ih

/-- The pair mass of the intrinsic group label, for any bounded work/pair functions.
Its only ordinal input identifies the chronological two-level tag stream. -/
theorem schedule_group_pairs_by_owner (a : RootArchive) (teams : ℕ) (work pay : Fin a.rootCount→ℕ)
    (facts : ScheduleFacts a W teams work pay a.ids) (owner : Fin a.rootCount→ℕ×ℕ)
    (correct : ∀ i : Fin a.rootCount,
      (((labelBoth (fun b=>label 0 (Team.handoff work (a.slotBudget/4) teams b).1) 0
        (schedule a.groups (Team.ticks work a.ids) a.totalPairs work pay a.ids))[i.val]?).map Prod.fst)=some (owner i))
    (g : ℕ) :
    a.groups*(∑i : Fin a.rootCount,if (owner i).1=g then pay i else 0)≤4*a.totalPairs := by
  let bs:=schedule a.groups (Team.ticks work a.ids) a.totalPairs work pay a.ids
  obtain ⟨num,flat,cap⟩:=schedule_spec facts.groups facts.nonempty facts.pairPositive work pay a.ids
    facts.positive le_rfl facts.pairBound facts.cell
  have hit:=finRange_filter_group work (a.slotBudget/4) teams bs g owner
    (flat.trans (List.ofFn_id a.rootCount)) facts.covered correct
  have count := ticks_filtered pay (fun i=>(owner i).1=g) (List.finRange a.rootCount)
  rw [hit] at count
  simp only [←List.ofFn_id,List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq] at count
  rw [←count]
  by_cases bound : g<bs.length
  · rw [List.getElem?_eq_getElem bound,Option.getD_some]
    exact (cap _ (List.getElem_mem bound)).2
  · simp [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt bound),Team.ticks]

private theorem physicalOwners (a : RootArchive) (teams : ℕ) (work pay : Fin a.rootCount→ℕ)
    (h : ScheduleFacts a W teams work pay a.ids) (wg : a.groups<2^W) :
    let group:=fun i : Fin a.rootCount=>((a.scheduled (W:=W) teams work pay a.ids)[i.val]?).elim 0 (fun z=>z.1.val)
    let bs:=schedule a.groups (Team.ticks work a.ids) a.totalPairs work pay a.ids
    let all:=labelBoth (fun b=>label 0 (Team.handoff work (a.slotBudget/4) teams b).1) 0 bs
    ∃ own : Fin a.rootCount→ℕ×ℕ, (∀i,(all[i.val]?).map Prod.fst=some (own i)) ∧
      (∀i,(own i).1<a.groups ∧ (own i).2<teams) ∧ ∀i,group i=(own i).1 := by
  intro group bins tagged
  let bs:=schedule a.groups (Team.ticks work a.ids) a.totalPairs work pay a.ids
  let slots:=fun b=>(Team.handoff work (a.slotBudget/4) teams b).1
  let all:=labelBoth (fun b=>label 0 (slots b)) 0 bs
  obtain ⟨num,flat,_⟩:=schedule_spec h.groups h.nonempty h.pairPositive work pay a.ids
    h.positive le_rfl h.pairBound h.cell
  have payload : all.map Prod.snd=a.ids := (labelBoth_payload slots bs 0 (fun b hb=>by
    simpa only [slots,h.covered b hb,List.append_nil] using Team.handoff_flatten work (a.slotBudget/4) teams b)).trans flat
  have len : all.length=a.rootCount := by simpa only [List.length_map,ids,List.length_ofFn] using congrArg List.length payload
  have ix (i : Fin a.rootCount):i.val<all.length:=len.symm ▸ i.isLt
  let own:=fun i : Fin a.rootCount=>(all[i.val]'(ix i)).1
  have correct (i : Fin a.rootCount) : (all[i.val]?).map Prod.fst=some (own i) := by
    simp only [List.getElem?_eq_getElem (ix i),Option.map_some,own]
  have bound (i : Fin a.rootCount) : (own i).1<a.groups ∧ (own i).2<teams := by
    have tag:=tag_bounds (fun b=>label 0 (slots b)) teams 0 bs (fun b _ y hy=>by
      simpa only [slots,Nat.zero_add,Team.handoff_length] using label_slot_lt y 0 (slots b) hy)
      (all[i.val]'(ix i)) (List.getElem_mem (ix i))
    simpa only [Nat.zero_add,show bs.length=a.groups from num] using tag
  have same (i : Fin a.rootCount) : group i=(own i).1 := by
    change (((all.map (RAM.TickGreedyNat.owner (w:=W)))[i.val]?).elim 0 _)=_
    rw [List.getElem?_map,List.getElem?_eq_getElem (ix i)]
    change (((own i).1 : Word W)).val=(own i).1
    exact Fin.val_cast_of_lt ((bound i).1.trans wg)
  exact ⟨own,correct,bound,same⟩

/-- Both bounds hold for the literal group word read by ranked root scheduling,
with no published node state or program-history hypothesis. -/
theorem groupWord_bounds (a : RootArchive) (teams : ℕ) (work pay : Fin a.rootCount→ℕ)
    (h : ScheduleFacts a W teams work pay a.ids) (wg : a.groups<2^W) :
    let group:=fun i : Fin a.rootCount=>((a.scheduled (W:=W) teams work pay a.ids)[i.val]?).elim 0 (fun z=>z.1.val)
    (∀i,group i<a.groups) ∧ ∀g,a.groups*(∑i,if group i=g then pay i else 0)≤4*a.totalPairs := by
  intro group
  obtain ⟨own,correct,bound,same⟩:=physicalOwners a teams work pay h wg
  have reads : group = fun i => (own i).1 := funext same
  rw [reads]
  exact ⟨fun i=>(bound i).1,schedule_group_pairs_by_owner a teams work pay h own correct⟩

open TickChronology TickRangeChronology TickEvaluationProduct

/-- Each chronological slice member's actual stored group word is the named group. -/
theorem arrayBlock_group (a : RootArchive) (work pay : Fin a.rootCount→ℕ)
    (teams g s : ℕ) (h : ScheduleFacts a W teams work pay a.ids) (wg : a.groups<2^W) :
    let bs:=schedule a.groups (Team.ticks work a.ids) a.totalPairs work pay a.ids
    let b:=(bs[g]?).getD []
    let slots:=(Team.handoff work (a.slotBudget/4) teams b).1
    ∀ i∈(slots[s]?).getD [],((a.scheduled (W:=W) teams work pay a.ids)[i.val]?).elim 0 (fun z=>z.1.val)=g := by
  intro bs b slots i mem
  obtain ⟨own,correct,_,same⟩:=physicalOwners a teams work pay h wg
  have order:bs.flatten=List.finRange a.rootCount := by
    exact (schedule_spec h.groups h.nonempty h.pairPositive work pay a.ids
      h.positive le_rfl h.pairBound h.cell).2.1.trans (List.ofFn_id a.rootCount)
  have pick:=finRange_filter_slot work (a.slotBudget/4) teams bs g s own order h.covered correct
  rw [←pick] at mem
  have hit : own i=(g,s) := of_decide_eq_true (List.mem_filter.mp mem).2
  exact (same i).trans (congrArg Prod.fst hit)

/-- The charged work of a particular native time/team row is within the slot budget,
including empty and out-of-range rows. -/
theorem arrayBlock_budget (a : RootArchive) (work pay : Fin a.rootCount→ℕ)
    (c : Clock) (teams g s : ℕ) :
    let bs:=schedule a.groups (Team.ticks work a.ids) a.totalPairs work pay a.ids
    let b:=(bs[g]?).getD []
    let slices:=(Team.handoff work (a.slotBudget/4) (c.evaluateTicks*teams) b).1
    Team.ticks work ((slices[s]?).getD [])≤a.slotBudget/4 := by
  intro bs b slices
  by_cases hs : s<slices.length
  · rw [List.getElem?_eq_getElem hs,Option.getD_some]
    exact actual_block_charge work (a.slotBudget/4) b slices _ (Team.handoff_valid ..) (List.getElem_mem hs)
  · simp [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hs),Team.ticks]

/-- Cell product read by the true time/team slot address from the two handoff arrays. -/
def arrayWeight {F : Type*} [CommMonoid F] (a : RootArchive) (work pay : Fin a.rootCount→ℕ)
    (c : Clock) (teams group : ℕ) (f : Fin a.rootCount→F) (t : ℕ) : F :=
  let bs:=schedule a.groups (Team.ticks work a.ids) a.totalPairs work pay a.ids
  let b:=(bs[group]?).getD []
  let slots:=(Team.handoff work (a.slotBudget/4) (c.evaluateTicks*teams) b).1
  ∏ j : Fin teams,(((slots[TickClockWords.values c 0 teams j.val t 3]?).getD []).map f).prod

private theorem list_weight {F α : Type*} [CommMonoid F] (xs : List α) (f : α→F) :
    (∏ i : Fin xs.length,f (xs.get i))=(xs.map f).prod := by
  calc
    _ = (List.ofFn (f ∘ xs.get)).prod := (Fin.prod_ofFn _).symm
    _ = ((List.ofFn xs.get).map f).prod := by rw [List.map_ofFn]
    _ = _ := by rw [List.ofFn_get]

/-- Over all evaluation ticks, the native time/team addresses enumerate the true
group fiber exactly once, before any chronological node rows are published. -/
theorem arrayWeight_group {F : Type*} [CommMonoid F] (a : RootArchive) (work pay : Fin a.rootCount→ℕ)
    (c : Clock) (teams : ℕ) (h : ScheduleFacts a W (c.evaluateTicks*teams) work pay a.ids)
    (wg : a.groups<2^W) (g : Fin c.groups) (f : Fin a.rootCount→F) :
    ((evalTicks c g.val).map (a.arrayWeight work pay c teams g.val f)).prod =
      ∏ i : {i : Fin a.rootCount // ((a.scheduled (W:=W) (c.evaluateTicks*teams) work pay a.ids)[i.val]?).elim 0
        (fun z=>z.1.val)=g.val},f i.val := by
  classical
  let cap:=c.evaluateTicks*teams
  let group:=fun i : Fin a.rootCount=>((a.scheduled (W:=W) cap work pay a.ids)[i.val]?).elim 0 (fun z=>z.1.val)
  let bs:=schedule a.groups (Team.ticks work a.ids) a.totalPairs work pay a.ids
  let b:=(bs[g.val]?).getD []
  let slots:=(Team.handoff work (a.slotBudget/4) cap b).1
  obtain ⟨own,correct,bound,same⟩:=physicalOwners a cap work pay h wg
  let Cell:={i : Fin a.rootCount // group i=g.val}
  let place:Cell→Fin cap:=fun i=>⟨(own i.val).2,(bound i.val).2⟩
  have order : bs.flatten = List.finRange a.rootCount :=
    ((schedule_spec h.groups h.nonempty h.pairPositive work pay a.ids
      h.positive le_rfl h.pairBound h.cell).2.1).trans (List.ofFn_id a.rootCount)
  apply eval_product c g place (fun i=>f i.val)
  intro t
  unfold arrayWeight
  apply Finset.prod_congr rfl
  intro j _
  rw [clock_slot]
  let s : Fin cap:=finProdFinEquiv (t,j)
  let xs:=(slots[s.val]?).getD []
  have picked:(List.finRange a.rootCount).filter (fun i=>decide (own i=(g.val,s.val)))=xs :=
    finRange_filter_slot work (a.slotBudget/4) cap bs g.val s.val own order h.covered correct
  have nodup:xs.Nodup := by rw [←picked]; exact (List.nodup_finRange _).filter _
  have mem (i : Fin a.rootCount) : i∈xs ↔ group i=g.val ∧ (own i).2=s.val := by
    have ownerGroup : group i = (own i).1 := same i
    rw [←picked, ownerGroup]
    simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
    exact ⟨fun h=>⟨congrArg Prod.fst h,congrArg Prod.snd h⟩,fun h=>Prod.ext h.1 h.2⟩
  let e:Fin xs.length ≃ Owned place s :=
    (List.Nodup.getEquiv xs nodup).trans
      ⟨fun i=>⟨⟨i.val,((mem i.val).mp i.property).1⟩,Fin.ext ((mem i.val).mp i.property).2⟩,
        fun i=>⟨i.val.val,(mem i.val.val).mpr ⟨i.val.property,congrArg Fin.val i.property⟩⟩,fun _=>rfl,fun _=>rfl⟩
  change (xs.map f).prod=_
  rw [←list_weight]
  exact e.prod_comp (fun i=>f i.val.val)

/-- Bucket mass of the actual native group number. Covers all natural group
indices; an out-of-range group has no owners. -/
theorem schedule_group_pairs (a : RootArchive) (N : Nodes a) (teams : ℕ)
    (h : ScheduleFacts a W teams N.work N.pairs a.ids) (fit : a.groups<2^W) (g : ℕ) :
    a.groups*(∑i : Fin a.rootCount,if (a.groupOf N teams h fit i).val=g then N.pairs i else 0)≤4*a.totalPairs := by
  simp_rw [a.groupOf_ordinal N teams h fit]
  apply schedule_group_pairs_by_owner a teams N.work N.pairs h (a.ordinalOwner N teams h) _ g
  intro i
  change ((a.tags N teams)[i.val]?).map Prod.fst=_
  have ix : i.val<(a.tags N teams).length := by rw [a.tags_length N teams h];exact i.isLt
  simp only [List.getElem?_eq_getElem ix,Option.map_some,ordinalOwner]

private theorem filter_ordinals {n : ℕ} (f : ℕ→Bool) (g : Fin n→Bool)
    (same : ∀ i : Fin n,f i.val=g i) :
    (List.range n).filter f=((List.finRange n).filter g).map Fin.val := by
  have eq : (List.finRange n).map Fin.val=List.range n := by
    apply List.ext_getElem <;> simp
  rw [←eq]
  generalize List.finRange n=ls
  induction ls with
  | nil=>rfl
  | cons i ls ih=>
    cases hh : g i <;> simp [hh,same,ih]

/-- The S17 root list used by the terminal interpreter is the precise
contiguous slot of the two-level greedy schedule, in original root order. -/
theorem selected_block (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (h : ScheduleFacts a W slots N.work N.pairs a.ids) (gf : a.groups≤2^W) (sf : slots≤2^W)
    (g : Fin a.groups) (s : Fin slots) (m : Memory W)
    (cg : m (TickWorkspace.base a.age 1)=(g.val:Word W))
    (cs : m (TickWorkspace.base a.age 1+3)=(s.val:Word W)) :
    TickTerminalRoot.rootIds a.age (a.summaryHeader N) (a.scheduledOwner N slots) m =
      (a.slotBlock N slots g.val s.val).map Fin.val := by
  change (List.range a.rootCount).filter (TickSlotLookup.matchesOwner (a.scheduledOwner N slots)
    (m (TickWorkspace.base a.age 1)) (m (TickWorkspace.base a.age 1+3)))=_
  rw [cg,cs,←a.slotBlock_filter N slots g.val s.val h]
  apply filter_ordinals
  intro i
  have b:=a.owner_bounded N slots h i
  have g1 : (a.ordinalOwner N slots h i).1<2^W:=lt_of_lt_of_le b.1 gf
  have s1 : (a.ordinalOwner N slots h i).2<2^W:=lt_of_lt_of_le b.2 sf
  have g2 := g.isLt.trans_le gf
  have s2 := s.isLt.trans_le sf
  unfold TickSlotLookup.matchesOwner
  rw [a.slot_owner_words N slots h i]
  simp only [decide_eq_decide]
  constructor
  · intro eq
    have first:=congrArg (fun z : Word W×Word W=>z.1.val) eq
    have second:=congrArg (fun z : Word W×Word W=>z.2.val) eq
    apply Prod.ext
    · simpa only [Fin.val_cast_of_lt g1,Fin.val_cast_of_lt g2] using first
    · simpa only [Fin.val_cast_of_lt s1,Fin.val_cast_of_lt s2] using second
  · intro eq
    exact congrArg (fun z : ℕ×ℕ=>((z.1:Word W),(z.2:Word W))) eq

def atRoot (a : RootArchive) {α : Type*} (f : Fin a.rootCount→α) (fallback : α) (i : ℕ) :=
  if hi : i<a.rootCount then f ⟨i,hi⟩ else fallback

theorem selected_budget (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (h : ScheduleFacts a W slots N.work N.pairs a.ids) (gf : a.groups≤2^W) (sf : slots≤2^W)
    (g : Fin a.groups) (s : Fin slots) (m : Memory W)
    (cg : m (TickWorkspace.base a.age 1)=(g.val:Word W))
    (cs : m (TickWorkspace.base a.age 1+3)=(s.val:Word W)) :
    let ids:=TickTerminalRoot.rootIds a.age (a.summaryHeader N) (a.scheduledOwner N slots) m
    Team.ticks (a.atRoot N.work 0) ids≤a.slotBudget/4 := by
  dsimp only
  rw [a.selected_block N slots h gf sf g s m cg cs]
  simpa [Team.ticks,List.map_map,Function.comp_def,atRoot] using a.slotBlock_budget N slots g.val s.val


/-- The physical evaluator preserves the actual four S1 clock words across
publication, the pair header initializer, and the evaluator request fill. -/
theorem prepared_clock {F : Type*} [Field F] [Fintype F] {B : TickActiveROM.Layout} {p H J : ℕ}
    {fit : RAM.Contraction.Fits (TickWeightedBank.shape F p H J) W} {c : TickChronology.Clock}
    (x : TickActiveROM.CellInput B c fit) (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (ls : List Layers) (g : Fin a.initialLanes→Fin a.groups) (m prepared : Memory W)
    (post : a.preparedInput x N slots ls m g prepared)
    (team t : ℕ) (input : TickPhysicalABI.Inputs B c m team t)
    (cur : a.current<2^W) (clockLow : B.clockWords+3<a.protectedBelow)
    (boundsLow : B.clockWords+4≤B.bounds) (requestLow : B.clockWords+4≤B.auxRequest)
    (boundsFit : B.bounds+4≤2^W) (i : Fin 4) :
    prepared (B.clockWords+i.val)=(TickClockWords.values c B.bits B.teams team t i:Word W) := by
  obtain ⟨b,o,pub,done,rfl⟩:=post
  have hi:=i.isLt
  change RAM.fillSegment _ _ _ _ _=_
  rw [fill_frame _ _ _ _ _ (.inl (by omega)),TickActiveROM.bounds_low _ _ _ _ (by omega) boundsFit,
    a.read_low _ _ _ _ _ _ _ pub done cur _ (by omega)]
  exact input.2 i

/-- Evaluator iteration j of group g uses precisely its selected (j,team)
block in the chronological schedule mounted at S1. -/
theorem selected_at_time {F : Type*} [Field F] [Fintype F] {B : TickActiveROM.Layout} {p H J : ℕ}
    {fit : RAM.Contraction.Fits (TickWeightedBank.shape F p H J) W} {c : TickChronology.Clock}
    (x : TickActiveROM.CellInput B c fit) (a : RootArchive) (N : Nodes a)
    (ls : List Layers) (home : Fin a.initialLanes→Fin a.groups) (m prepared : Memory W)
    (post : a.preparedInput x N (c.evaluateTicks*B.teams) ls m home prepared)
    (g : Fin c.groups) (j : Fin c.evaluateTicks) (k : Fin B.teams)
    (input : TickPhysicalABI.Inputs B c m k.val (TickEvaluationProduct.time c g j))
    (current : a.current<2^W) (low : B.clockWords+3<a.protectedBelow)
    (beforeBounds : B.clockWords+4≤B.bounds) (beforeRequest : B.clockWords+4≤B.auxRequest)
    (fits : B.bounds+4≤2^W) (layout : B.clockWords=TickWorkspace.base a.age 1)
    (ng : c.groups=a.groups) (gf : a.groups≤2^W) (sf : c.evaluateTicks*B.teams≤2^W)
    (h : ScheduleFacts a W (c.evaluateTicks*B.teams) N.work N.pairs a.ids) :
    TickTerminalRoot.rootIds a.age (a.summaryHeader N) (a.scheduledOwner N (c.evaluateTicks*B.teams)) prepared =
      (a.slotBlock N (c.evaluateTicks*B.teams) g.val (finProdFinEquiv (j,k)).val).map Fin.val := by
  have words:=a.prepared_clock x N _ ls home m prepared post k.val _ input current low beforeBounds beforeRequest fits
  apply a.selected_block N _ h gf sf (finCongr ng g) (finProdFinEquiv (j,k))
  · have got:=words 0
    change prepared (B.clockWords+0)=(c.group (TickEvaluationProduct.time c g j):Word W) at got
    have lim:=j.isLt
    have room:=c.room
    have val: c.group (TickEvaluationProduct.time c g j)=g.val:=
      (c.in_group g.isLt (show c.chunks+1+j.val<c.groupDuration by omega)).2.1
    simpa only [layout,Nat.add_zero,val,finCongr_apply_coe] using got
  · have got:=words 3
    rw [TickEvaluationProduct.clock_slot] at got
    have slotIndex : (3 : Fin 4).val = 3 := by decide
    simpa only [layout,slotIndex] using got


open HistoryNodeDirectory

/-- The compact reverse pass stores the ordinal of the terminal owner, and
the greedy pass stores the group and slot under that ordinal. -/
def selectedDirectory (a : RootArchive) (N : Nodes a) (slots : ℕ) (group slot : Word W) :
    Selected.Directory W a.rootsTotal where
  root i := (N.chronology.root i:Word W)
  owner i := a.scheduledOwner N slots i.val
  group := group
  slot := slot

theorem picked_lane_group (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (h : ScheduleFacts a W slots N.work N.pairs a.ids) (gf : a.groups<2^W)
    (rf : a.rootCount≤2^W) (lanes : a.initialLanes≤a.rootsTotal) (i : Fin a.initialLanes)
    (g : Fin a.groups) (s : Word W)
    (picked : Selected.picked (a.selectedDirectory N slots (g.val:Word W) s) i.val=true) :
    a.groupOf N slots h gf (N.laneRoot lanes i)=g := by
  let r:=N.laneRoot lanes i
  have within : i.val<a.rootsTotal:=lt_of_lt_of_le i.isLt lanes
  simp only [Selected.picked, dite_eq_left within, decide_eq_true_eq] at picked
  have laneId : (a.selectedDirectory N slots (g.val : Word W) s).root ⟨i.val,within⟩ =
      (r.val : Word W) := rfl
  rw [laneId] at picked
  have eq : a.scheduledOwner N slots ((r.val:Word W).val)=((g.val:Word W),s) := picked
  rw [Fin.val_cast_of_lt (r.isLt.trans_le rf),a.finite_owner_words N slots h gf r] at eq
  apply Fin.ext
  have fst:=congrArg (fun ab : Word W×Word W=>ab.1.val) eq
  simpa only [Fin.val_cast_of_lt ((a.groupOf N slots h gf r).isLt.trans gf),Fin.val_cast_of_lt (g.isLt.trans gf)] using fst

set_option maxHeartbeats 1800000 in
/-- The records of the forward selected-node guard are read from the
published S45 and S11 directories and the two S1 clock words. -/
theorem prepared_directory {F : Type*} [Field F] [Fintype F] {B : TickActiveROM.Layout} {p H J : ℕ}
    {fit : RAM.Contraction.Fits (TickWeightedBank.shape F p H J) W} {c : TickChronology.Clock}
    (x : TickActiveROM.CellInput B c fit) (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (ls : List Layers) (groups : Fin a.initialLanes→Fin a.groups) (m prepared : Memory W)
    (post : a.preparedInput x N slots ls m groups prepared)
    (team t : ℕ) (clock : TickPhysicalABI.Inputs B c m team t)
    (sched : ScheduleFacts a W slots N.work N.pairs a.ids) (room : OutputRoom a W) (sizes : PublishSizes a W)
    (cache : a.rootCache=TickWorkspace.base a.age 45) (sources : a.sourceRows=TickWorkspace.base a.age 46)
    (groupBase : a.groupRows=TickWorkspace.base a.age 47)
    (clockBase : B.clockWords=TickWorkspace.base a.age 1) (low : B.clockWords+3<a.protectedBelow)
    (beforeBounds : B.clockWords+4≤B.bounds) (beforeReq : B.clockWords+4≤B.auxRequest)
    (fits : B.bounds+4≤2^W) (boundsEnd : B.bounds+4≤a.statsBase) (reqEnd : B.auxRequest+8*B.bits≤a.statsBase) :
    Selected.Recorded (HistoryStageBody.Physical.ownerData W a.age)
      (a.selectedDirectory N slots (c.group t:Word W) (TickClockWords.values c B.bits B.teams team t 3:Word W))
      prepared := by
  let s:=TickWorkspace.stride a.age
  have fixed : 128 ≤ s := sizes.fixed
  have endFit : 51*s<2^W:=sizes.address
  have nodeBound : 8*a.rootsTotal ≤ s := sizes.nodes
  have laneBound:=sizes.lanes
  have groupsBound : a.groups ≤ s := sizes.groups
  have chunksBound : a.chunkBits ≤ s := sizes.chunks
  have indexFit : a.rootCount<2^W:=room.rootCount
  have s5 : TickWorkspace.base a.age 5+4*a.initialLanes≤a.statsBase:=by change 6*s+4*a.initialLanes≤7*s;omega
  have s6 : a.statsBase+8≤TickWorkspace.base a.age 7:=by change 7*s+8≤8*s;omega
  have s8 : TickWorkspace.base a.age 8+a.groups≤a.ownerBase:=by
    change 9*s+a.groups≤12*s+1*(s/4);omega
  have clocks:=a.prepared_clock x N slots ls groups m prepared post team t clock room.current low beforeBounds beforeReq fits
  have clk0:=clocks 0
  have clk3:=clocks 3
  change prepared (B.clockWords+0)=(c.group t:Word W) at clk0
  rw [Nat.add_zero,clockBase] at clk0
  rw [clockBase] at clk3
  obtain ⟨branch,out,first,done,rfl⟩:=post
  have owners:=(a.directory_read x N slots groups _ branch out first done sched room s5 s6 s8 fits boundsEnd reqEnd).2
  intro i
  let rank:=N.chronology.root i
  have rlt : rank<a.rootCount:=by
    have hi:=N.chronology.root_lt i
    rw [N.first] at hi
    simpa [rootsTotal] using hi
  have rankFit := rlt.trans indexFit
  have ic:=i.isLt
  have rbank : x.filled .evaluate out (TickWorkspace.base a.age 45+i.val)=(rank:Word W):=by
    have b1 : B.bounds+4≤TickWorkspace.base a.age 45+i.val:=by
      change B.bounds+4≤46*s+i.val; change B.bounds+4≤7*s at boundsEnd;omega
    have b2 : B.auxRequest+8*B.bits≤TickWorkspace.base a.age 45+i.val:=by
      change B.auxRequest+8*B.bits≤46*s+i.val;change B.auxRequest+8*B.bits≤7*s at reqEnd;omega
    rw [filled_high x out .evaluate _ fits b1 b2]
    have keep:=a.output_frame groups branch out done (TickWorkspace.base a.age 45+i.val)
    rw [keep]
    · simpa only [cache] using first.1.2.2.1 i
    · right;change 6*s+4*a.initialLanes≤46*s+i.val;omega
    · right;change 8*s+a.chunkBits≤46*s+i.val;omega
    · right;change 9*s+a.groups≤46*s+i.val;omega
    · left;rw [sources];change 46*s+i.val<47*s;omega
    · left;rw [groupBase];change 46*s+i.val<48*s;omega
  let ptr : Fin 5→ℕ:=![TickWorkspace.base a.age 45+i.val,TickPhysicalABI.directory a.age 1+2*rank,
    TickPhysicalABI.directory a.age 1+2*rank+1,TickWorkspace.base a.age 1,TickWorkspace.base a.age 1+3]
  let D:=a.selectedDirectory (W:=W) N slots (c.group t) (TickClockWords.values c B.bits B.teams team t 3)
  let data:=HistoryStageBody.Physical.ownerData W a.age
  have ptrFits (j : Fin 5) : ptr j<2^W:=by
    have count : a.rootCount≤a.rootsTotal:=by dsimp [rootsTotal];omega
    fin_cases j
    · change 46*s+i.val<2^W;omega
    · change 12*s+1*(s/4)+2*rank<2^W;omega
    · change 12*s+1*(s/4)+2*rank+1<2^W;omega
    · change 2*s<2^W;omega
    · change 2*s+3<2^W;omega
  have addr (j : Fin 5) : Selected.addresses data D i j=(ptr j:Word W):=by
    fin_cases j <;> simp [Selected.addresses,D,data,ptr,selectedDirectory,HistoryStageBody.Physical.ownerData,
      rank,Nat.two_mul,Nat.cast_add]
  have vals (j : Fin 5) : (x.filled .evaluate out) (ptr j)=Selected.contents D i j:=by
    have own:=owners rank rlt
    fin_cases j
    · exact rbank
    · change _=(a.scheduledOwner N slots ((rank:Word W).val)).1
      rw [Fin.val_cast_of_lt rankFit]
      exact own.1
    · change _=(a.scheduledOwner N slots ((rank:Word W).val)).2
      rw [Fin.val_cast_of_lt rankFit]
      exact own.2
    · exact clk0
    · exact clk3
  intro j
  rw [addr j,Fin.val_cast_of_lt (ptrFits j)]
  exact vals j


/-- Every chronological node is charged to the terminal root reached by its
actual chain of physical parent pointers. -/
def Nodes.lastRoot {a : RootArchive} (N : Nodes a) (i : Fin a.rootsTotal) : Fin a.rootCount :=
  ⟨N.chronology.root i,by
    have h:=N.chronology.root_lt i
    rw [N.first] at h
    simpa [rootsTotal] using h⟩

theorem selected_descendant_sum (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (facts : ScheduleFacts a W slots N.work N.pairs a.ids)
    (groupsFit : a.groups≤2^W) (slotsFit : slots≤2^W) (rootsFit : a.rootCount≤2^W)
    (g : Fin a.groups) (s : Fin slots) (cost : Fin a.rootsTotal→ℕ)
    :
    let D:=a.selectedDirectory N slots (g.val:Word W) (s.val:Word W)
    (∑ i : Fin a.rootsTotal,if Selected.picked D i.val then cost i else 0)=
      ((a.slotBlock N slots g.val s.val).map (fun r=>∑ i : {i // N.lastRoot i=r},cost i.val)).sum := by
  intro D
  let charges (r : Fin a.rootCount):=∑ i : {i // N.lastRoot i=r},cost i.val
  let hit (r : Fin a.rootCount):=a.ordinalOwner N slots facts r=(g.val,s.val)
  have selects (i : Fin a.rootsTotal) : Selected.picked D i.val=decide (hit (N.lastRoot i)):=by
    let r:=N.lastRoot i
    have hf:=(a.owner_bounded N slots facts r).1.trans_le groupsFit
    have sf:=(a.owner_bounded N slots facts r).2.trans_le slotsFit
    have gf:=g.isLt.trans_le groupsFit
    have tf:=s.isLt.trans_le slotsFit
    simp only [Selected.picked,dite_eq_left i.isLt]
    change decide (a.scheduledOwner N slots ((r.val:Word W).val)=_)=_
    rw [Fin.val_cast_of_lt (r.isLt.trans_le rootsFit),a.slot_owner_words N slots facts r]
    change decide (((_:Word W),(_:Word W))=((g.val:Word W),(s.val:Word W)))=decide (hit r)
    simp only [decide_eq_decide]
    constructor
    · intro yes
      have fst:=congrArg (fun v : Word W×Word W=>v.1.val) yes
      have snd:=congrArg (fun v : Word W×Word W=>v.2.val) yes
      exact Prod.ext (by simpa only [Fin.val_cast_of_lt hf,Fin.val_cast_of_lt gf] using fst)
        (by simpa only [Fin.val_cast_of_lt sf,Fin.val_cast_of_lt tf] using snd)
    · exact congrArg (fun v : ℕ×ℕ=>((v.1:Word W),(v.2:Word W)))
  have charged : (∑ i : Fin a.rootsTotal,if Selected.picked D i.val then cost i else 0)=
      ∑ r : Fin a.rootCount, if hit r then charges r else 0:=by
    simp_rw [selects,decide_eq_true_eq]
    rw [←Fintype.sum_fiberwise N.lastRoot (fun i=>if hit (N.lastRoot i) then cost i else 0)]
    apply Finset.sum_congr rfl
    intro r _
    have atRoot (i : {i // N.lastRoot i=r}) : N.lastRoot i.val=r:=i.property
    by_cases yes : hit r <;> simp [charges,atRoot,yes]
  have block:=ticks_filtered charges hit (List.finRange a.rootCount)
  rw [a.slotBlock_filter N slots g.val s.val facts] at block
  simp only [←List.ofFn_id,List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq] at block
  simpa only [Team.ticks,charges] using charged.trans block.symm

theorem selected_descendant_budget (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (facts : ScheduleFacts a W slots N.work N.pairs a.ids)
    (groupsFit : a.groups≤2^W) (slotsFit : slots≤2^W) (rootsFit : a.rootCount≤2^W)
    (g : Fin a.groups) (s : Fin slots) (cost : Fin a.rootsTotal→ℕ)
    (subtree : ∀ r,(∑ i : {i // N.lastRoot i=r},cost i.val)≤N.work r) :
    let D:=a.selectedDirectory N slots (g.val:Word W) (s.val:Word W)
    (∑ i : Fin a.rootsTotal,if Selected.picked D i.val then cost i else 0)≤a.slotBudget/4 := by
  exact (a.selected_descendant_sum N slots facts groupsFit slotsFit rootsFit g s cost).le.trans
    (a.slotBlock_sum N slots g.val s.val (fun r => ∑ i : {i // N.lastRoot i=r}, cost i.val)
      (fun r _ => subtree r))


end ThreeFlat.Diagonal.NavigationPass.RootArchive

end OAI
