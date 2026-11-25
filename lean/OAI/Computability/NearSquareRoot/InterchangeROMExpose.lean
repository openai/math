import OAI.Computability.NearSquareRoot.InterchangeROMFrame
import OAI.Computability.NearSquareRoot.InterchangeExpose
import OAI.Computability.NearSquareRoot.CRTControlledFlatSwaps

/-! # Leading and trailing endpoint requests for the parameter-uniform frame prelude -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMExpose

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeFrame

structure Input where
  b : ℕ
  n : ℕ
  req : Request b
  radix : 2 ≤ b
  slots : 0 < n
  inside : n < req.width
  valid : req.Admissible

variable (i : Input)

abbrev ord := Equiv.refl (Fin i.n)
abbrev f := Request.lanes i.n i.req.width
abbrev rem := Request.tail i.n i.req.width
abbrev mesh := expanded (ord i) i.b 1 (f i) (rem i) i.req.before i.req.between i.req.after_
noncomputable abbrev whole := parent (ord i) i.b 1 (f i) (rem i) i.req.before i.req.between i.req.after_

private theorem width_split : i.req.width = width (n:=i.n) 1 (f i) (rem i) :=
  Request.width_eq (i.slots.trans i.inside) _

noncomputable def home : Adopt (mesh i) i.req.rows :=
  (whole i).thenDo (Request.widthView i.req.before i.req.between i.req.after_ (width_split i).symm)

abbrev leadView := (leadingAxis (ord i) i.b 1 (f i) (rem i) i.req.before i.req.between i.req.after_).view
abbrev tailView := (trailingAxis (ord i) i.b 1 (f i) (rem i) i.req.before i.req.between i.req.after_).view
abbrev centerView := (axis (ord i) i.b 1 (f i) (rem i) i.req.before i.req.between i.req.after_).view
abbrev leadMap := leading (J:=Fin i.n) i.b 1 (f i) (rem i) i.req.before i.req.between i.req.after_
abbrev tailMap := trailing (J:=Fin i.n) i.b 1 (f i) (rem i) i.req.before i.req.between i.req.after_
abbrev centerMap := center (J:=Fin i.n) i.b 1 (f i) (rem i) i.req.before i.req.between i.req.after_

noncomputable abbrev initial := i.req.contents ∘ (home i).cast

noncomputable def leadRequest : Request i.b where
  before := i.req.before ++ []
  between := Request.headAfter i.n i.req ++ (i.req.between ++ [])
  after_ := Request.headAfter i.n i.req ++ i.req.after_
  width := 1
  recordWidth := i.req.recordWidth
  contents := initial i ∘ (leadView i).cast.symm

noncomputable def tailRequest : Request i.b where
  before := i.req.before ++ Request.tailBefore i.n i.req
  between := [] ++ (i.req.between ++ Request.tailBefore i.n i.req)
  after_ := [] ++ i.req.after_
  width := rem i
  recordWidth := i.req.recordWidth
  contents := initial i ∘ leadMap i ∘ (tailView i).cast.symm

abbrev centerRows := arrays (ord i) (line i.b (f i))
  (pre i.b 1 i.req.before) (gap i.b 1 (rem i) i.req.between) (post i.b (rem i) i.req.after_)
noncomputable abbrev centerValues := initial i ∘ leadMap i ∘ tailMap i ∘ (centerView i).cast.symm
noncomputable abbrev centerPayload := stripe (centerRows i) (centerValues i)
noncomputable abbrev schedule := [leadRequest i, tailRequest i]

abbrev template : InterchangeROMFrame.Input :=
  ((tally i.b,tally i.n),InterchangeROMAddress.header i.req.width i.req.before i.req.between i.req.after_)

abbrev centerHeader : InterchangeROMAddress.Header :=
  InterchangeROMAddress.header (f i) (pre i.b 1 i.req.before)
    (gap i.b 1 (rem i) i.req.between) (post i.b (rem i) i.req.after_)

theorem header_tree :
    (leadRequest i).header = send (InterchangeROMFrame.split (template i)).1 ∧
    (tailRequest i).header = send (InterchangeROMFrame.split (template i)).2.1 ∧
    centerHeader i = (InterchangeROMFrame.split (template i)).2.2 := by
  rw [template, InterchangeROMFrame.split_header]
  simp [centerHeader,leadRequest,tailRequest,Request.header,InterchangeROMAddress.header,f,rem,pre,field]

private theorem transfer {X Y : Type} {s : Series X} {d : Series Y}
    (e : Adopt s d) (v : X → Tree) : stripe d (v ∘ e.cast.symm) = stripe s v :=
  (e.back.packet v).symm

theorem lead_payload : (leadRequest i).payload = i.req.payload :=
  (transfer (leadView i) (initial i)).trans ((home i).packet i.req.contents).symm

private theorem axis_reply {X : Type} {b j : ℕ} {P G B : Tape} {s : Series X}
    (e : Adopt s (stock b P G B j)) (changeKey : X → X)
    (holds : ∀ k, e.cast (changeKey k) = swapper _ _ _ (e.cast k)) (v : X → Tree) :
    stripe (stock b P G B j) ((v ∘ e.cast.symm) ∘ swapper _ _ _) = stripe s (v ∘ changeKey) := by
  rw [e.packet]
  apply congrArg (stripe s)
  funext k
  simp only [Function.comp_apply, ← holds, Equiv.symm_apply_apply]

theorem lead_reply : (Request.job i.b).reply (leadRequest i) =
    stripe (mesh i) (initial i ∘ leadMap i) :=
  axis_reply (leadView i) _ (leading_cast (ord i) i.b 1 (f i) (rem i) _ _ _) (initial i)

theorem tail_payload : (tailRequest i).payload = (Request.job i.b).reply (leadRequest i) :=
  (transfer (tailView i) (initial i ∘ leadMap i)).trans (lead_reply i).symm

theorem tail_reply : (Request.job i.b).reply (tailRequest i) = centerPayload i :=
  (axis_reply (tailView i) _ (trailing_cast (ord i) i.b 1 (f i) (rem i) _ _ _) (initial i ∘ leadMap i)).trans
    (transfer (centerView i) (initial i ∘ leadMap i ∘ tailMap i)).symm

theorem chain : InterchangeBatch.Chain Request.payload (Request.job i.b).reply i.req.payload
    (schedule i) (centerPayload i) := by
  rw [← lead_payload i]
  apply InterchangeBatch.Chain.cons
  rw [← tail_payload i]
  apply InterchangeBatch.Chain.cons
  rw [tail_reply i]
  exact .nil _

theorem center_reply :
    stripe (centerRows i) (centerValues i ∘ swapper _ _ _) = (Request.job i.b).reply i.req := by
  change stripe _ _ = stripe _ _
  rw [(centerView i).packet,(home i).packet]
  apply congrArg (stripe _)
  funext k
  apply congrArg i.req.contents
  change (home i).cast (leadMap i (tailMap i ((centerView i).cast.symm
    (swapper _ _ _ ((centerView i).cast k))))) = swapper _ _ _ ((home i).cast k)
  rw [← center_cast (ord i) i.b 1 (f i) (rem i) _ _ _ k, Equiv.symm_apply_apply]
  have all := parent_cast (ord i) i.b 1 (f i) (rem i) i.req.before i.req.between i.req.after_ k
  let canon := Request.widthView (b:=i.b) i.req.before i.req.between i.req.after_ (width_split i).symm
  exact (congrArg canon.cast all).trans (Request.widthView_swap _ _ _ _ _)

theorem row_counts : (leadRequest i).rows.count = i.req.rows.count ∧
    (tailRequest i).rows.count = i.req.rows.count ∧ (centerRows i).count = i.req.rows.count :=
  ⟨(leadView i).cost.symm.trans (home i).cost, (tailView i).cost.symm.trans (home i).cost,
   (centerView i).cost.symm.trans (home i).cost⟩

theorem widths : (leadRequest i).width = 1 ∧ (tailRequest i).width < i.n :=
  ⟨rfl, Request.tail_lt _ i.slots⟩

theorem admissible : (leadRequest i).Admissible ∧ (tailRequest i).Admissible := by
  have branch (h : ℕ) : ∀ k ∈ field i.b h, 2 ≤ k ∧ k ≤ i.b := ivory i.radix
  have head : ∀ k ∈ Request.headAfter i.n i.req, 2 ≤ k ∧ k ≤ i.b := by
    simp only [Request.headAfter,List.nil_append,rack_eq,List.forall_mem_append]
    exact ⟨branch _,branch _⟩
  have last : ∀ k ∈ Request.tailBefore i.n i.req, 2 ≤ k ∧ k ≤ i.b := by
    simp only [Request.tailBefore,List.append_nil,rack_eq,List.forall_mem_append]
    exact ⟨branch _,branch _⟩
  have old := i.valid
  simp only [Request.Admissible, List.forall_mem_append] at old
  simp only [Request.Admissible,leadRequest,tailRequest,List.nil_append,List.append_nil,
    List.forall_mem_append]
  simp only [Request.headAfter,Request.tailBefore,List.nil_append,List.append_nil,List.forall_mem_append] at head last
  tauto

theorem request_reply_count {b : ℕ} (r : Request b) : ((Request.job b).reply r).count = r.payload.count := by
  let sw : Equiv.Perm (SpanKey r.before r.between r.after_ (Block b r.width)) :=
    ⟨swapper _ _ _,swapper _ _ _,fun _ => rfl,fun _ => rfl⟩
  exact Controlled.stripe_count_perm r.rows sw r.contents

theorem data_counts :
    (leadRequest i).payload.count = i.req.payload.count ∧
    ((Request.job i.b).reply (leadRequest i)).count = i.req.payload.count ∧
    (tailRequest i).payload.count = i.req.payload.count ∧
    ((Request.job i.b).reply (tailRequest i)).count = i.req.payload.count ∧
    (centerPayload i).count = i.req.payload.count ∧
    (stripe (centerRows i) (centerValues i ∘ swapper _ _ _)).count = i.req.payload.count := by
  have a := congrArg Tree.count (lead_payload i)
  have b := (request_reply_count (leadRequest i)).trans a
  have c := (congrArg Tree.count (tail_payload i)).trans b
  have d := (request_reply_count (tailRequest i)).trans c
  have e := (congrArg Tree.count (tail_reply i).symm).trans d
  exact ⟨a,b,c,d,e,(congrArg Tree.count (center_reply i)).trans (request_reply_count i.req)⟩

private theorem shape_le_room (s : Tape) (valid : solid s) : size (shape s) ≤ 4 * room s := by
  induction s with
  | nil => decide
  | cons a t ih =>
    obtain ⟨ha,ht⟩ := (solid_cons a t).mp valid
    rw [shape_cons, size_cons, size_tally, tally_length, room_cons]
    cases t with
    | nil => simp; omega
    | cons d t =>
      have hd := (solid_cons d t).mp ht
      have big : 2 ≤ room (d::t) := hd.1.trans (Nat.le_mul_of_pos_right d (wide _ hd.2))
      have p := Nat.mul_le_mul_left a big
      have q := Nat.mul_le_mul_right (room (d::t)) ha
      have e := ih ht
      nlinarith

/-- A uniform header-size bound, including when the template radix varies.
Each nontrivial spectator range contributes fewer unary header nodes than
four times the size of its cartesian range. -/
theorem uniform_header_count {b : ℕ} (a : Request b) (hb : 2 ≤ b) (ok : a.Admissible) :
    a.header.count ≤ 18 * a.rows.count := by
  have sp : solid a.before := fun d h => (ok _ (by simp [h])).1
  have sg : solid a.between := fun d h => (ok _ (by simp [h])).1
  have sb : solid a.after_ := fun d h => (ok _ (by simp [h])).1
  let blocks := [room a.before, b ^ a.width, room a.between, b ^ a.width, room a.after_]
  have cells : a.rows.count = blocks.prod := by
    have line_room : room (field b a.width) = b ^ a.width :=
      (space (field b a.width)).symm.trans (lineSize b a.width)
    change ((layout a.before).cart ((line b a.width).cart
      ((layout a.between).cart ((line b a.width).cart (layout a.after_))))).count = _
    simp only [blocks,Series.count_cart,space,line_room,List.prod_cons,List.prod_nil,mul_one]
  have pos : 0 < blocks.prod := by
    have p := wide _ sp
    have g := wide _ sg
    have s := wide _ sb
    dsimp [blocks]
    positivity
  have part (x : ℕ) (mem : x ∈ blocks) : x ≤ a.rows.count := by
    rw [cells]
    exact Nat.le_of_dvd pos (List.dvd_prod mem)
  have p := (shape_le_room _ sp).trans (Nat.mul_le_mul_left 4 (part _ (by simp [blocks])))
  have g := (shape_le_room _ sg).trans (Nat.mul_le_mul_left 4 (part _ (by simp [blocks])))
  have s := (shape_le_room _ sb).trans (Nat.mul_le_mul_left 4 (part _ (by simp [blocks])))
  have w : a.width ≤ a.rows.count := (Nat.lt_two_pow_self (n:=a.width)).le.trans
    ((Nat.pow_le_pow_left hb _).trans (part _ (by simp [blocks])))
  have p0 : 0 < a.rows.count := cells ▸ pos
  change size (_,_,_,_) ≤ _
  simp only [size_prod,size_tally,tally_length]
  omega

theorem rows_le_payload {b : ℕ} (a : Request b) : a.rows.count ≤ a.payload.count := by
  simp only [Request.payload,stripe_simple,Task.forest_count,Series.count]
  omega

/-- The complete child issues, including their new headers, fit a fixed
multiple of the incoming occupied data regardless of the radix or lane count. -/
theorem issue_counts : ((Request.job i.b).issue (leadRequest i)).count ≤ 20*i.req.payload.count ∧
    ((Request.job i.b).issue (tailRequest i)).count ≤ 20*i.req.payload.count := by
  have h := (row_counts i)
  have d := data_counts i
  have p := rows_le_payload i.req
  have l := uniform_header_count (leadRequest i) i.radix (admissible i).1
  have t := uniform_header_count (tailRequest i) i.radix (admissible i).2
  have positive := Tree.count_pos i.req.payload
  change (leadRequest i).header.count + (leadRequest i).payload.count + 1 ≤ _ ∧
    (tailRequest i).header.count + (tailRequest i).payload.count + 1 ≤ _
  rw [h.1] at l
  rw [h.2.1] at t
  rw [d.1,d.2.2.1]
  omega

abbrev descriptor {b : ℕ} (a : Request b) :=
  (tally b, InterchangeROMAddress.header a.width a.before a.between a.after_)

theorem header_budget : ∃ e C : ℕ, ∀ i : Input,
    size (descriptor (leadRequest i)) + size (descriptor (tailRequest i)) + size (centerHeader i) ≤
      C * (size (template i) + 1) ^ e := by
  let x (i : Input) := size (template i)
  have radixBound : Dom x (fun i => size (tally i.b)) := by
    apply (Dom.base x).mono
    intro i
    dsimp only [x, template, size_prod]
    omega
  have splitBound : Dom x (fun i => size (InterchangeROMFrame.split (template i))) :=
    InterchangeROMFrame.split_poly.length.map template
  apply ((radixBound.add radixBound).add splitBound).mono
  intro i
  obtain ⟨h1,h2,h3⟩ := header_tree i
  have a := congrArg Tree.count h1
  have b := congrArg Tree.count h2
  let z := InterchangeROMFrame.split (template i)
  change (leadRequest i).header.count = size z.1 at a
  change (tailRequest i).header.count = size z.2.1 at b
  change centerHeader i = z.2.2 at h3
  change size (tally i.b) + (leadRequest i).header.count + 1 +
    (size (tally i.b) + (tailRequest i).header.count + 1) + size (centerHeader i) ≤
    size (tally i.b) + size (tally i.b) + (size z.1 + (size z.2.1 + size z.2.2 + 1) + 1)
  rw [a,b,h3]
  omega

theorem endpoint_cardinalities :
    (line i.b (leadRequest i).width).count ≤ i.b ^ i.n ∧
    (line i.b (tailRequest i).width).count ≤ i.b ^ i.n := by
  have ⟨lead,trail⟩ := widths i
  rw [lineSize,lineSize,lead]
  have hb : 0 < i.b := (by decide : 0 < 2).trans_le i.radix
  exact ⟨Nat.pow_le_pow_right hb i.slots,Nat.pow_le_pow_right hb trail.le⟩

end InterchangeROMExpose

end NearSquareRoot
end Computability
end OAI
