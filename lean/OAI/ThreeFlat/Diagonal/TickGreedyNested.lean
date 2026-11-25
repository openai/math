import OAI.ThreeFlat.Diagonal.TickGreedyReplay

namespace OAI
/-! # Streaming group and processor ownership in a single traversal -/

namespace ThreeFlat.Diagonal.TickGreedyReplay

open LinearAlgebra.SpectralBooks.VNP
variable {α : Type*}

/-- One per-cell update of the group and slot cursors. Group changes reset the
local processor number and its remaining capacity before placing the current cell. -/
def placeBoth (groupCap slotCap : ℕ) (g s : Cursor) (score work : ℕ) : Cursor × Cursor :=
  let g' := place groupCap g score
  (g',place slotCap (if g'.1 = g.1 then s else (0,slotCap)) work)

def assignBoth (score work : α → ℕ) (groupCap slotCap : ℕ) (g s : Cursor) :
    List α → List ((ℕ × ℕ) × α)
  | [] => []
  | x::xs =>
    let p := placeBoth groupCap slotCap g s (score x) (work x)
    ((p.1.1,p.2.1),x) :: assignBoth score work groupCap slotCap p.1 p.2 xs

private def slots (work : α → ℕ) (cap last : ℕ) (s : Cursor) :
    List (ℕ × α) → List ((ℕ × ℕ) × α)
  | [] => []
  | (g,x)::xs =>
    let s' := place cap (if g = last then s else (0,cap)) (work x)
    ((g,s'.1),x)::slots work cap g s' xs

private theorem factor (score work : α → ℕ) (gc sc : ℕ) (g s : Cursor) (xs : List α) :
    assignBoth score work gc sc g s xs = slots work sc g.1 s (assign score gc g xs) := by
  induction xs generalizing g s with
  | nil => rfl
  | cons x xs ih => simp only [assignBoth,placeBoth,assign,slots,ih]

private theorem before (g : ℕ) (bs : List (List α)) (z : ℕ × α) (hz : z ∈ label g bs) : g ≤ z.1 := by
  induction bs generalizing g with
  | nil => simp [label] at hz
  | cons b bs ih =>
    rcases List.mem_append.mp hz with head | tail
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp head
      exact le_rfl
    · exact (Nat.le_succ g).trans (ih (g+1) tail)

private theorem batch (work : α → ℕ) (cap g : ℕ) (s : Cursor) (b : List α) (tail : List (ℕ × α))
    (later : ∀ z ∈ tail, z.1 ≠ g) :
    slots work cap g s (b.map (fun x => (g,x)) ++ tail) =
    (assign work cap s b).map (fun z => ((g,z.1),z.2)) ++ slots work cap g (0,cap) tail := by
  induction b generalizing s with
  | nil =>
    cases tail with
    | nil => rfl
    | cons z zs =>
      rcases z with ⟨n,x⟩
      have ne : n ≠ g := later _ List.mem_cons_self
      simp [assign,slots,ne]
  | cons x xs ih => simp [assign,slots,ih]

private theorem fresh (work : α → ℕ) (cap i j : ℕ) (tail : List (ℕ × α)) :
    slots work cap i (0,cap) tail = slots work cap j (0,cap) tail := by
  cases tail with
  | nil => rfl
  | cons z zs => rcases z with ⟨g,x⟩; simp [slots]

/-- Enumerate the nested handoff with the actual group and processor index.
Empty groups and empty processor slots emit no cells. -/
def labelBoth (slotOwner : List α → List (ℕ × α)) (g : ℕ) :
    List (List α) → List ((ℕ × ℕ) × α)
  | [] => []
  | b::bs => (slotOwner b).map (fun z => ((g,z.1),z.2)) ++ labelBoth slotOwner (g+1) bs

private theorem slots_label (work : α → ℕ) (cap g : ℕ) (bs : List (List α)) :
    slots work cap g (0,cap) (label g bs) = labelBoth (assign work cap (0,cap)) g bs := by
  induction bs generalizing g with
  | nil => rfl
  | cons b bs ih =>
    rw [label,batch work cap g _ b _ (fun z hz => by have := before (g+1) bs z hz; omega)]
    rw [fresh work cap g (g+1),ih,labelBoth]

private theorem labelBoth_congr (f h : List α → List (ℕ × α)) (g : ℕ) (bs : List (List α))
    (same : ∀ b ∈ bs, f b = h b) : labelBoth f g bs = labelBoth h g bs := by
  induction bs generalizing g with
  | nil => rfl
  | cons b bs ih =>
    rw [labelBoth,labelBoth,same b List.mem_cons_self,ih (g+1) (fun b hb => same b (List.mem_cons_of_mem _ hb))]

/-- The one-pass two-counter assignment is exactly the nested greedy handoff
for the paper's group score and per-group work budget. -/
theorem assignBoth_schedule {J W B : ℕ} (hJ : 0 < J) (hW : 0 < W) (hB : 0 < B)
    (m teams : ℕ) (work pairs : α → ℕ) (xs : List α)
    (pos : ∀ x ∈ xs, 0 < work x) (wt : Team.ticks work xs ≤ W) (pt : Team.ticks pairs xs ≤ B)
    (small : ∀ x ∈ xs, cellScore J W B work pairs x ≤ 2*(W*B))
    (slotFits : ∀ x ∈ xs, work x ≤ m/4)
    (covered : ∀ b ∈ schedule J W B work pairs xs, (Team.handoff work (m/4) teams b).2 = []) :
    assignBoth (cellScore J W B work pairs) work (4*(W*B)) (m/4) (0,4*(W*B)) (0,m/4) xs =
      labelBoth (fun b => label 0 (Team.handoff work (m/4) teams b).1) 0 (schedule J W B work pairs xs) := by
  rw [factor,assign_groups hJ hW hB work pairs xs pos wt pt small,slots_label]
  apply labelBoth_congr
  intro b hb
  apply assign_slots work m teams b _ (covered b hb)
  intro x hx
  apply slotFits
  rw [← (schedule_spec hJ hW hB work pairs xs pos wt pt small).2.1]
  exact List.mem_flatten.mpr ⟨b,hb,hx⟩

/-- Select a label, retaining the left-to-right order of the payloads. -/
def pickLabel {ι : Type*} [DecidableEq ι] (key : ι) (xs : List (ι × α)) : List α :=
  (xs.filter fun z=>decide (z.1=key)).map Prod.snd

private theorem pick_cons {ι : Type*} [DecidableEq ι] (key tag : ι) (x : α) (xs : List (ι×α)) :
    pickLabel key ((tag,x)::xs)=if tag=key then x::pickLabel key xs else pickLabel key xs := by
  by_cases h : tag=key <;> simp [pickLabel,h]

private theorem pick_append {ι : Type*} [DecidableEq ι] (key : ι) (a b : List (ι×α)) :
    pickLabel key (a++b)=pickLabel key a++pickLabel key b := by simp [pickLabel]

private theorem pick_tag (key tag : ℕ) (b : List α) :
    pickLabel key (b.map (fun x=>(tag,x)))=if tag=key then b else [] := by
  induction b with
  | nil => by_cases h : tag=key <;> simp [pickLabel,h]
  | cons x xs ih =>
    rw [List.map_cons, pick_cons, ih]
    split <;> simp_all

private theorem pick_empty {ι : Type*} [DecidableEq ι] (key : ι) (xs : List (ι×α))
    (away : ∀ x∈xs,x.1≠key) : pickLabel key xs=[] := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    rcases z with ⟨tag,x⟩
    rw [pick_cons,ite_eq_right (away _ List.mem_cons_self)]
    exact ih (fun t ht=>away _ (List.mem_cons_of_mem _ ht))

theorem label_pick (bins : List (List α)) (start k : ℕ) :
    pickLabel (start+k) (label start bins)=(bins[k]?).getD [] := by
  induction bins generalizing start k with
  | nil => simp [label,pickLabel]
  | cons b bs ih =>
    cases k with
    | zero =>
      have tail : pickLabel start (label (start+1) bs)=[] :=
        pick_empty _ _ (fun z hz=>by have := before (start+1) bs z hz; omega)
      simp [label,pick_append,pick_tag,tail]
    | succ k =>
      have ne : start≠start+(k+1) := by omega
      have eq : start+(k+1)=start+1+k := by omega
      simp only [label,pick_append,pick_tag,ite_eq_right ne,List.nil_append]
      rw [eq,ih]; rfl

private def splitLabel (z : (ℕ×ℕ)×α) := (z.1.1,(z.1.2,z.2))

private theorem split_pick (xs : List ((ℕ×ℕ)×α)) (g s : ℕ) :
    pickLabel (g,s) xs=pickLabel s (pickLabel g (xs.map splitLabel)) := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    rcases z with ⟨⟨h,t⟩,x⟩
    by_cases hg : h=g <;> by_cases ts : t=s <;> simp [pick_cons,splitLabel,hg,ts,ih,Prod.mk.injEq]

private theorem split_both (f : List α→List (ℕ×α)) (groups : List (List α)) (start : ℕ) :
    (labelBoth f start groups).map splitLabel=label start (groups.map f) := by
  induction groups generalizing start with
  | nil => rfl
  | cons b bs ih => simp [labelBoth,label,ih,List.map_map,Function.comp_def,splitLabel]

/-- A missing group or slot yields the empty selection, including padded handoffs. -/
theorem labelBoth_pick_slot (slots : List α→List (List α)) (groups : List (List α)) (g s : ℕ) :
    pickLabel (g,s) (labelBoth (fun b=>label 0 (slots b)) 0 groups) =
      ((groups[g]?).bind fun b=>(slots b)[s]?).getD [] := by
  let f:=fun b=>label 0 (slots b)
  rw [split_pick,split_both]
  have outer := label_pick (groups.map f) 0 g
  simp only [Nat.zero_add,List.getElem?_map] at outer
  rw [outer]
  cases atG : groups[g]? with
  | none => simp [pickLabel]
  | some b => simpa [atG,f] using label_pick (slots b) 0 s

private theorem payload_label (g : ℕ) (bs : List (List α)) :
    (label g bs).map Prod.snd=bs.flatten := by
  induction bs generalizing g with
  | nil => rfl
  | cons b bs ih => simp [label,ih,List.map_map,Function.comp_def]

/-- Complete handoffs emit each original payload once in original order. -/
theorem labelBoth_payload (slots : List α→List (List α)) (groups : List (List α)) (start : ℕ)
    (covered : ∀ b∈groups,(slots b).flatten=b) :
    (labelBoth (fun b=>label 0 (slots b)) start groups).map Prod.snd=groups.flatten := by
  induction groups generalizing start with
  | nil => rfl
  | cons b bs ih =>
    have tail:=ih (start+1) (fun t ht=>covered t (List.mem_cons_of_mem _ ht))
    simp [labelBoth,List.map_map,Function.comp_def,payload_label,covered b List.mem_cons_self,tail]

private theorem filter_owners {ι : Type*} [DecidableEq ι] (owner : α→ι) (key : ι)
    (xs : List (ι×α)) (correct : ∀ z∈xs,owner z.2=z.1) :
    (xs.map Prod.snd).filter (fun x=>decide (owner x=key))=pickLabel key xs := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    rcases z with ⟨tag,x⟩
    have h : owner x=tag := correct _ List.mem_cons_self
    have t:=ih (fun a ha=>correct a (List.mem_cons_of_mem _ ha))
    by_cases e : tag=key <;> simp [h,e,pick_cons,t]

private theorem handoff_empty_slot (work : α→ℕ) (cap teams s : ℕ) :
    ((Team.handoff work cap teams []).1[s]?).getD []=[] := by
  induction teams generalizing s with
  | zero => simp [Team.handoff]
  | succ teams ih => cases s <;> simp [Team.handoff,Team.splitBlock,ih]

private theorem ordinal_labels {n : ℕ} {ι : Type*} (owner : Fin n→ι) (xs : List (ι×Fin n))
    (payload : xs.map Prod.snd=List.finRange n)
    (correct : ∀i : Fin n,(xs[i.val]?).map Prod.fst=some (owner i)) :
    ∀ z∈xs,owner z.2=z.1 := by
  have len : xs.length=n := by simpa using congrArg List.length payload
  intro z hz
  obtain ⟨i,hi⟩:=List.mem_iff_get.mp hz
  subst z
  have within : i.val<n := i.isLt.trans_le len.le
  have key := congrArg (fun l : List (Fin n)=>l[i.val]?) payload
  have range : i.val<(List.finRange n).length := by simpa using within
  simp only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem range,
    Option.map_some,Option.some.injEq,List.getElem_finRange] at key
  have val : (xs.get i).2=⟨i.val,within⟩ := key
  rw [val]
  have h := correct ⟨i.val,within⟩
  change (xs[i.val]?).map Prod.fst=some (owner ⟨i.val,within⟩) at h
  change owner ⟨i.val,within⟩ = xs[i.val].1
  simpa only [List.getElem?_eq_getElem i.isLt,Option.map_some,Option.some.injEq] using h.symm

/-- The deterministic ordinal scan picks exactly the members of the named group
and processor, also for empty and out-of-range slots. The owner check is only
needed for actual ordinals in the input list. -/
theorem finRange_filter_slot {n : ℕ} (work : Fin n→ℕ) (cap teams : ℕ)
    (groups : List (List (Fin n))) (g s : ℕ) (owner : Fin n→ℕ×ℕ)
    (order : groups.flatten=List.finRange n)
    (covered : ∀ b∈groups,(Team.handoff work cap teams b).2=[])
    (correct : ∀ i : Fin n,
      (((labelBoth (fun b=>label 0 (Team.handoff work cap teams b).1) 0 groups)[i.val]?).map Prod.fst)=
        some (owner i)) :
    (List.finRange n).filter (fun i=>decide (owner i=(g,s))) =
      (((Team.handoff work cap teams ((groups[g]?).getD [])).1)[s]?).getD [] := by
  let slots:=fun b=> (Team.handoff work cap teams b).1
  let xs:=labelBoth (fun b=>label 0 (slots b)) 0 groups
  have payload : xs.map Prod.snd=List.finRange n := by
    apply Eq.trans (labelBoth_payload slots groups 0 ?_) order
    intro b hb
    simpa only [covered b hb,List.append_nil] using Team.handoff_flatten work cap teams b
  have owners := ordinal_labels owner xs payload correct
  rw [←payload,filter_owners owner _ xs owners,labelBoth_pick_slot slots groups g s]
  cases h : groups[g]? with
  | none => simpa [h] using (handoff_empty_slot work cap teams s).symm
  | some b => rfl

/-- Dropping a complete handoff's slot coordinate keeps each outer group label in
the original payload order. -/
private theorem outer_labels (slots : List α→List (List α)) (bs : List (List α)) (start : ℕ)
    (full : ∀ b∈bs,(slots b).flatten=b) :
    (labelBoth (fun b=>label 0 (slots b)) start bs).map (fun z=>(z.1.1,z.2))=label start bs := by
  induction bs generalizing start with
  | nil => rfl
  | cons b bs ih =>
    simp only [labelBoth,label,List.map_append,List.map_map]
    rw [ih (start+1) (fun x hx=>full x (List.mem_cons_of_mem _ hx))]
    have head:=congrArg (List.map (fun x=>(start,x))) ((payload_label 0 (slots b)).trans (full b List.mem_cons_self))
    simpa only [List.map_map,Function.comp_def] using congrArg (fun l=>l++label (start+1) bs) head

theorem finRange_filter_group {n : ℕ} (work : Fin n→ℕ) (cap teams : ℕ)
    (groups : List (List (Fin n))) (g : ℕ) (owner : Fin n→ℕ×ℕ)
    (order : groups.flatten=List.finRange n)
    (covered : ∀ b∈groups,(Team.handoff work cap teams b).2=[])
    (correct : ∀ i : Fin n,
      (((labelBoth (fun b=>label 0 (Team.handoff work cap teams b).1) 0 groups)[i.val]?).map Prod.fst)=
        some (owner i)) :
    (List.finRange n).filter (fun i=>decide ((owner i).1=g))=(groups[g]?).getD [] := by
  let slots:=fun b=>(Team.handoff work cap teams b).1
  let xs:=labelBoth (fun b=>label 0 (slots b)) 0 groups
  let proj:=fun z : (ℕ×ℕ)×Fin n=>(z.1.1,z.2)
  have full (b) (hb:b∈groups) : (slots b).flatten=b := by
    simpa only [slots,covered b hb,List.append_nil] using Team.handoff_flatten work cap teams b
  have payload : xs.map Prod.snd=List.finRange n := (labelBoth_payload slots groups 0 full).trans order
  have owners:=ordinal_labels owner xs payload correct
  have projected : (xs.map proj).map Prod.snd=List.finRange n := by
    rw [List.map_map]
    change xs.map Prod.snd=List.finRange n
    exact payload
  rw [←projected,filter_owners (fun i=>(owner i).1) g (xs.map proj) (by
    intro z hz;obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hz
    exact congrArg Prod.fst (owners x hx))]
  rw [show xs.map proj=label 0 groups from outer_labels slots groups 0 full]
  simpa only [Nat.zero_add] using label_pick groups 0 g

end ThreeFlat.Diagonal.TickGreedyReplay

end OAI
