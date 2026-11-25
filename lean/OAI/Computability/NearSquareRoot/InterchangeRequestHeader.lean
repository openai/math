import OAI.Computability.NearSquareRoot.InterchangeCalls
import OAI.Computability.NearSquareRoot.InterchangeFrame
import OAI.Computability.IntegerMultiplication.Staff.Nat
import OAI.Computability.IntegerMultiplication.Param.Base

/-! # Reading and bounding the recursive interchange descriptor -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port
  IntegerMultiplication.Adic IntegerMultiplication.Loom IntegerMultiplication.Staff

variable {I : Type} {b : ℕ}

/-- Use the literal request header as the descriptor channel, including when
the input index restricts the set of admissible requests. -/
def regime (xs : I → Request b) : Regime I where
  header i := (xs i).header
  scale i := (xs i).header.count
  gauge := Dom.base _

abbrev Admissible (a : Request b) :=
  ∀ d ∈ a.before ++ a.between ++ a.after_, 2 ≤ d ∧ d ≤ b

theorem admissible_inherited {P G B : Tape} {a : Request b}
    (hb : 2 ≤ b) (ok : ∀ d ∈ P ++ G ++ B, 2 ≤ d ∧ d ≤ b)
    (selected : inherited b P G B a) : Admissible a := by
  intro d h
  rcases selected _ h with rfl | hd
  · exact ⟨hb, le_rfl⟩
  · exact ok _ hd

/-- Cutting the fields of one request to expose its center stage preserves
the modulus bounds required to read its children's headers. -/
theorem admissible_center {a : Request b} (h t : ℕ) (hb : 2 ≤ b) (ok : Admissible a) :
    ∀ d ∈ InterchangeFrame.pre b h a.before ++ InterchangeFrame.gap b h t a.between ++
      InterchangeFrame.post b t a.after_, 2 ≤ d ∧ d ≤ b := by
  intro d hd
  simp only [InterchangeFrame.pre, InterchangeFrame.gap, InterchangeFrame.post, List.mem_append] at hd
  have spec : d ∈ a.before ∨ d ∈ a.between ∨ d ∈ a.after_ → 2 ≤ d ∧ d ≤ b :=
    fun e => ok d (by simpa only [List.mem_append, or_assoc] using e)
  have hf : d ∈ field b h → 2 ≤ d ∧ d ≤ b := ivory hb _
  have ht : d ∈ field b t → 2 ≤ d ∧ d ≤ b := ivory hb _
  tauto

def lanes (n w : ℕ) := (w - 1) / n
def tail (n w : ℕ) := (w - 1) % n

theorem width_eq {w : ℕ} (hw : 0 < w) (n : ℕ) :
    w = InterchangeFrame.width (n:=n) 1 (lanes n w) (tail n w) := by
  have h := Nat.div_add_mod (w-1) n
  unfold InterchangeFrame.width lanes tail
  omega

theorem tail_lt (w : ℕ) {n : ℕ} (hn : 0 < n) : tail n w < n := Nat.mod_lt _ hn

theorem lanes_mul_le (n w : ℕ) : lanes n w * n ≤ w :=
  (Nat.div_mul_le_self _ _).trans (Nat.sub_le ..)

variable (xs : I → Request b)

private theorem packet_has :
    (regime xs).Has (fun i => (tally (xs i).width, shape (xs i).before,
      shape (xs i).between, shape (xs i).after_)) := Regime.self

theorem width_has : Realizes (regime xs) (fun i => (xs i).width) :=
  (packet_has xs).ez Easy.fst

theorem before_has : (regime xs).Has (fun i => shape (xs i).before) :=
  ((packet_has xs).ez Easy.snd).ez Easy.fst

theorem between_has : (regime xs).Has (fun i => shape (xs i).between) :=
  (((packet_has xs).ez Easy.snd).ez Easy.snd).ez Easy.fst

theorem after_has : (regime xs).Has (fun i => shape (xs i).after_) :=
  (((packet_has xs).ez Easy.snd).ez Easy.snd).ez Easy.snd

theorem lane_has (n : ℕ) : Realizes (regime xs) (fun i => lanes n (xs i).width) :=
  ((width_has xs).minused (Realizes.fix 1)).dividing (Realizes.fix _)

theorem tail_has (n : ℕ) : Realizes (regime xs) (fun i => tail n (xs i).width) :=
  ((width_has xs).minused (Realizes.fix 1)).rem (Realizes.fix _)

theorem branch_known (n : ℕ) : Classified (regime xs) (fun i => n < (xs i).width) :=
  (Realizes.fix (r:=regime xs) n).below (width_has xs)

theorem lanes_pos {n w : ℕ} (hn : 0 < n) (hw : n < w) : 0 < lanes n w :=
  Nat.div_pos (by omega) hn

theorem lanes_lt {n w : ℕ} (hw : 0 < w) : lanes n w < w :=
  (Nat.div_le_self _ _).trans_lt (by omega)

theorem shapes_told_of_solid (p : ∀ i, solid (xs i).before) (g : ∀ i, solid (xs i).between)
    (s : ∀ i, solid (xs i).after_) :
    Told (regime xs) (fun i => (xs i).before) ∧
    Told (regime xs) (fun i => (xs i).between) ∧
    Told (regime xs) (fun i => (xs i).after_) :=
  ⟨⟨p, before_has xs⟩, ⟨g, between_has xs⟩, ⟨s, after_has xs⟩⟩

theorem shapes_told (valid : ∀ i, Admissible (xs i)) :
    Told (regime xs) (fun i => (xs i).before) ∧
    Told (regime xs) (fun i => (xs i).between) ∧
    Told (regime xs) (fun i => (xs i).after_) :=
  ⟨⟨fun i d h => (valid i d (by simp [h])).1, before_has xs⟩,
   ⟨fun i d h => (valid i d (by simp [h])).1, between_has xs⟩,
   ⟨fun i d h => (valid i d (by simp [h])).1, after_has xs⟩⟩

/-- Descriptors of the center stage with the leading and remainder digits
incorporated into the spectators on each wing. -/
theorem center_told (hb : 2 ≤ b) (valid : ∀ i, Admissible (xs i)) (n : ℕ) :
    Told (regime xs) (fun i => InterchangeFrame.pre b 1 (xs i).before) ∧
    Told (regime xs) (fun i => InterchangeFrame.gap b 1 (tail n (xs i).width) (xs i).between) ∧
    Told (regime xs) (fun i => InterchangeFrame.post b (tail n (xs i).width) (xs i).after_) := by
  obtain ⟨p,g,s⟩ := shapes_told xs valid
  have lead := Told.carrier hb (fun _ : I => 1) (Regime.fixed (tally 1) (r:=regime xs))
  have rem := Told.carrier hb _ (tail_has xs n)
  exact ⟨p.append lead, rem.append (g.append lead), rem.append s⟩

/-- The two endpoint stages are selected by a common within-wing slot.
The counts on each side of the slot can contain arbitrary stacked fields. -/
theorem side_told {P G B D E : I → Tape} {r : Regime I}
    (p : Told r P) (g : Told r G) (s : Told r B) (d : Told r D) (e : Told r E) :
    Told r (fun i => P i ++ D i) ∧ Told r (fun i => E i ++ (G i ++ D i)) ∧
      Told r (fun i => E i ++ B i) :=
  ⟨p.append d, e.append (g.append d), e.append s⟩

abbrev headAfter (n : ℕ) (a : Request b) :=
  [] ++ (Rack (field b (lanes n a.width)) n ++ field b (tail n a.width))
abbrev tailBefore (n : ℕ) (a : Request b) :=
  field b 1 ++ (Rack (field b (lanes n a.width)) n ++ [])

theorem endpoint_fields_told (hb : 2 ≤ b) (n : ℕ) :
    Told (regime xs) (headAfter n ∘ xs) ∧ Told (regime xs) (tailBefore n ∘ xs) := by
  have mid := (Told.carrier hb _ (lane_has xs n)).stacked n
  have last := Told.carrier hb _ (tail_has xs n)
  have first := Told.carrier hb (fun _ : I => 1) (Regime.fixed (tally 1) (r:=regime xs))
  exact ⟨Told.nil.append (mid.append last), first.append (mid.append Told.nil)⟩

/-- The number of base-two address digits that can be charged to the row count. -/
abbrev digits (a : Request b) :=
  a.before.length + (a.width + (a.between.length + (a.width + a.after_.length)))

private theorem room_lower (d : Tape) (hs : solid d) : 2 ^ d.length ≤ room d := by
  induction d with
  | nil => simp
  | cons a d ih =>
    rw [List.length_cons, pow_succ', room_cons]
    exact Nat.mul_le_mul (hs a List.mem_cons_self) (ih (solid_cons _ _ |>.mp hs).2)

theorem pow_digits_le (a : Request b) (hb : 2 ≤ b) (ok : Admissible a) :
    2 ^ a.digits ≤ a.rows.count := by
  have sp : solid a.before := fun d h => (ok _ (by simp [h])).1
  have sg : solid a.between := fun d h => (ok _ (by simp [h])).1
  have sb : solid a.after_ := fun d h => (ok _ (by simp [h])).1
  change _ ≤ ((layout a.before).cart ((line b a.width).cart
    ((layout a.between).cart ((line b a.width).cart (layout a.after_))))).count
  have hline : room (field b a.width) = b ^ a.width :=
    (space (field b a.width)).symm.trans (lineSize b a.width)
  simp only [digits, pow_add, Series.count_cart, space, hline]
  exact Nat.mul_le_mul (room_lower _ sp) (Nat.mul_le_mul (Nat.pow_le_pow_left hb _)
    (Nat.mul_le_mul (room_lower _ sg) (Nat.mul_le_mul (Nat.pow_le_pow_left hb _) (room_lower _ sb))))

theorem header_count_le (a : Request b) (ok : Admissible a) :
    a.header.count ≤ (2*b+8) * (a.digits+1) := by
  have hp := Stair.entry_size a.before (p:=b) fun d h => (ok d (by simp [h])).2
  have hg := Stair.entry_size a.between (p:=b) fun d h => (ok d (by simp [h])).2
  have hs := Stair.entry_size a.after_ (p:=b) fun d h => (ok d (by simp [h])).2
  change size (_,_,_,_) ≤ _
  simp only [size_prod, size_tally, tally_length, digits, Nat.mul_add, Nat.add_mul] at *
  omega

theorem header_count_log (a : Request b) (hb : 2 ≤ b) (ok : Admissible a) :
    a.header.count ≤ (2*b+8) * (Nat.log 2 a.rows.count + 1) :=
  (header_count_le a ok).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.le_log_of_pow_le (by decide) (pow_digits_le a hb ok)) _))

/-- A polynomial in the header size costs at most a constant times the total
number of records. The constant is uniform over all admissible requests. -/
theorem header_polynomial (b k : ℕ) : ∃ C : ℕ, ∀ a : Request b,
    2 ≤ b → Admissible a → (a.header.count + 1) ^ k ≤ C * a.rows.count := by
  let d := 2*b + 9
  obtain ⟨cut, hcut⟩ := Filter.eventually_atTop.1 (Param.beats (d ^ k) k)
  refine ⟨2 + (d * cut) ^ k, fun a hb ok => ?_⟩
  have hbase : a.header.count + 1 ≤ d * (a.digits + 1) := by
    have h := header_count_le a ok
    change _ ≤ (2 * b + 8 + 1) * _
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hp := pow_digits_le a hb ok
  have hpos : 0 < a.rows.count := lt_of_lt_of_le (Nat.pow_pos (by decide)) hp
  by_cases h : cut ≤ a.digits + 1
  · calc
      _ ≤ (d * (a.digits+1)) ^ k := Nat.pow_le_pow_left hbase _
      _ = d ^ k * (a.digits + 1) ^ k := Nat.mul_pow ..
      _ ≤ 2 ^ (a.digits + 1) := hcut _ h
      _ = 2 * 2 ^ a.digits := pow_succ' _ _
      _ ≤ 2 * a.rows.count := Nat.mul_le_mul_left _ hp
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right ..)
  · have hu := Nat.pow_le_pow_left (hbase.trans (Nat.mul_le_mul_left d (by omega : a.digits+1 ≤ cut))) k
    exact hu.trans ((Nat.le_mul_of_pos_right _ hpos).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_left ..)))

theorem ripe_rows (hb : 2 ≤ b) (valid : ∀ i, Admissible (xs i)) :
    (regime xs).ripe (fun i => ((xs i).rows.count : ℝ)) := by
  constructor
  · intro i
    change (1 : ℝ) ≤ ((xs i).rows.count : ℝ)
    exact_mod_cast (Nat.succ_le_of_lt
      ((Nat.pow_pos (by decide : 0 < 2)).trans_le (pow_digits_le (xs i) hb (valid i))))
  · intro k
    obtain ⟨C, hc⟩ := header_polynomial b k
    refine ⟨C, fun i => ?_⟩
    change (((xs i).header.count + 1) ^ k : ℕ) ≤ (C : ℝ) * (xs i).rows.count
    exact_mod_cast hc (xs i) hb (valid i)

abbrev recordVolume (a : Request b) := a.rows.count * (a.recordWidth + 1)

theorem ripe_volume (hb : 2 ≤ b) (valid : ∀ i, Admissible (xs i)) {w : I → ℝ}
    (major : ∀ i, ((xs i).rows.count : ℝ) ≤ w i) : (regime xs).ripe w := by
  obtain ⟨pos, bound⟩ := ripe_rows xs hb valid
  refine ⟨fun i => (pos i).trans (major i), fun k => ?_⟩
  obtain ⟨C, bound⟩ := bound k
  exact ⟨C, fun i => (bound i).trans (mul_le_mul_of_nonneg_left (major i) (by positivity))⟩

theorem rows_le_recordVolume (a : Request b) : a.rows.count ≤ a.recordVolume :=
  Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

theorem issue_volume (hb : 2 ≤ b) (valid : ∀ i, Admissible (xs i))
    (data : Manifest _ (fun i => (xs i).recordWidth) (fun i => (xs i).contents)) :
    Volume (fun i => ((xs i).recordVolume : ℝ)) ((job b).issue ∘ xs) := by
  have pos i : 0 < (xs i).rows.count :=
    (Nat.pow_pos (by decide : 0 < 2)).trans_le (pow_digits_le _ hb (valid i))
  obtain ⟨H, hH⟩ := header_polynomial b 1
  obtain ⟨C, hC⟩ := data.size
  refine ⟨H+C+3, fun i => ?_⟩
  have hs := stripe_size (xs i).rows (xs i).contents _ (hC i)
  have hh := hH (xs i) hb (valid i)
  have hr := (xs i).rows_le_recordVolume
  have hpos := pos i
  change ((Tree.fork (xs i).header (stripe (xs i).rows (xs i).contents)).count : ℝ) ≤ _
  rw [Tree.count]
  change _ ≤ (↑(H+C+3 : ℕ) : ℝ) * ↑(xs i).recordVolume
  exact_mod_cast (show (xs i).header.count + (stripe (xs i).rows (xs i).contents).count + 1 ≤
      (H+C+3) * (xs i).recordVolume by
    rw [pow_one] at hh
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm _ C, Nat.mul_assoc] at hs
    change _ ≤ C * (xs i).recordVolume + (xs i).rows.count * 1 + 1 at hs
    have hmajor := Nat.mul_le_mul_left H hr
    simp only [Nat.mul_one, Nat.add_mul] at *
    omega)

theorem branch_has (n : ℕ) : (regime xs).Has (fun i => decide (n < (xs i).width)) := by
  obtain ⟨s, hs, h⟩ := branch_known xs n
  have eq : s = (fun i => decide (n < (xs i).width)) := by
    funext i
    by_cases hi : n < (xs i).width
    · simpa only [hi, decide_true] using (h i).mp hi
    · have hn : s i ≠ true := fun e => hi ((h i).mpr e)
      simpa only [hi, decide_false] using Bool.eq_false_of_not_eq_true hn
  rwa [← eq]

theorem branch_tag (n : ℕ) {w : I → ℝ} (ripe : (regime xs).ripe w)
    (stored : Volume w ((job b).issue ∘ xs)) :
    Carries w ((job b).issue ∘ xs) (fun i =>
      Tree.fork (.atom (decide (n < (xs i).width))) ((job b).issue (xs i))) := by
  have header : Carries w ((job b).issue ∘ xs) (regime xs).header :=
    Carries.dropRight ripe.1 stored.left stored.right
  have tag := (branch_has xs n).cooked ripe
  exact (header.chain tag).twice (Carries.idles ripe.1 stored)

def branch_ledger {X : Type} (n : ℕ) (uses : {i // n < (xs i).width} → List X) (i : I) :=
  if h : n < (xs i).width then uses ⟨i,h⟩ else []

/-- Physically test the tagged width and run either of two fixed commands.
The leaf makes no recursive calls, and the internal branch retains its
charged ledger. -/
theorem branch_tunnel {X : Type} {o : Oracle X} {w : I → ℝ} (n : ℕ)
    (ripe : (regime xs).ripe w) (stored : Volume w ((job b).issue ∘ xs))
    (uses : {i // n < (xs i).width} → List X)
    (leaf : Sized (fun i : {i // (xs i).width ≤ n} => w i)
      (fun i => (job b).issue (xs i)) (fun i => (job b).reply (xs i)))
    (step : Tunnel o (fun i : {i // n < (xs i).width} => w i) uses
      (fun i => (job b).issue (xs i)) (fun i => (job b).reply (xs i))) :
    Tunnel o w (branch_ledger xs n uses) ((job b).issue ∘ xs) ((job b).reply ∘ xs) := by
  let test (i : I) := decide (n < (xs i).width)
  have tagged : Tunnel o w (branch_ledger xs n uses) (fun i =>
      Tree.fork (.atom (test i)) ((job b).issue (xs i))) ((job b).reply ∘ xs) := by
    apply Tunnel.fork test
    · have h (i : {i // test i = false}) : ¬n < (xs i.val).width := of_decide_eq_false i.property
      let down (i : {i // test i = false}) : {i // (xs i).width ≤ n} := ⟨i.val, Nat.le_of_not_gt (h i)⟩
      simpa only [branch_ledger, h, ↓reduceDIte, down, Function.comp_def] using
        (Tunnel.walkway (o:=o) (leaf.along down))
    · have h (i : {i // test i = true}) : n < (xs i.val).width := of_decide_eq_true i.property
      let up (i : {i // test i = true}) : {i // n < (xs i).width} := ⟨i.val, h i⟩
      simpa only [branch_ledger, h, ↓reduceDIte, up, Function.comp_def] using (step.slide up)
  simpa only [List.nil_append] using
    (Tunnel.walkway (o:=o) (branch_tag xs n ripe stored).runs).join tagged

/-- Restrict the recursive job to its admissible domain. This changes only
the proof indices of the actual charged calls. The compiled command, issue
and reply bytes, length of the ledger and every repeated call are preserved. -/
theorem restrict_calls {X : Type} {r : Regime I} {n l : I → ℕ} {j : Job X}
    {zone : I → X → Prop} {c : ℤ} {p q : I → Tree} (cert : Hopto j r n l zone c p q)
    (valid : X → Prop) (closed : ∀ i x, zone i x → valid x) :
    Hopto (⟨fun x : Subtype valid => j.issue x.val, fun x => j.reply x.val⟩ : Job _)
      r n l (fun i x => zone i x.val) c p q := by
  classical
  obtain ⟨uses, legal, card, work⟩ := cert.safe
  let ledger (i : I) : List (Subtype valid) := (uses i).attach.map
    (fun x => ⟨x.val, closed i x.val (legal i _ x.property)⟩)
  have original (i : I) : (ledger i).map Subtype.val = uses i := by
    simp [ledger, List.map_map, Function.comp_def]
  refine ⟨ledger, ?_, ?_, ?_⟩
  · intro i x hx
    apply legal
    rw [← original i]
    exact List.mem_map_of_mem hx
  · intro i
    simpa only [ledger,List.length_map,List.length_attach] using card i
  · obtain ⟨k, hk⟩ := work.eligible
    refine ⟨k, fun fare => ?_⟩
    let cost (x : X) : ℝ := if h : valid x then fare ⟨x,h⟩ else 0
    obtain ⟨hw, cmd, K, execute⟩ := hk cost
    refine ⟨hw, cmd, K, fun i parent env D ih => ?_⟩
    have good_cost (y : Subtype valid) : cost y.val = fare y := by simp [cost, y.property]
    have costs : ((uses i).map cost).sum = ((ledger i).map fare).sum := by
      rw [← original i, List.map_map]
      simp only [Function.comp_def, good_cost]
    have allowed x (hx : x ∈ uses i) : Acc (parent :: env) parent
        (j.issue x) (j.reply x) ((D : ℝ) * cost x) := by
      rw [← original i] at hx
      obtain ⟨y,hy,hyx⟩ := List.mem_map.mp hx
      subst x
      rw [good_cost]
      exact ih y hy
    simpa only [Oracle.reserve,costs] using execute i parent env D allowed

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
