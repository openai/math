import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Reorder
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Depth
import Mathlib.Data.Fin.Tuple.Basic

/-! # A uniform fusion script -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset Motion Stage
open scoped Classical
variable {F J L K N : Type} [Field F] {r t : ℕ} {p : Params}
  {m : Job F r t J L K N} {ν : ℕ → K}

def Job.test (m : Job F r t J L K N) (P : ℕ) (z : F) (j : ℤ) : Test F r t :=
  coefficient P (powered P m.A) m.B z j

def Job.evalAt (m : Job F r t J L K N) (p : Params) (z : F) (j : ℤ) (q : Task m p) :=
  q.s.observe p.P (q.R.vertex m.v) (m.test p.P z j)

def Job.pairs (m : Job F r t J L K N) (P : ℕ) (u : Entry F r t K N) (j : ℤ) :=
  (Motion.pairs P m.d m.e j).filter
    (fun i => 0 ≤ fusedEnergy u.a m.x.a i.1 ∧ 0 ≤ fusedEnergy u.b m.x.b i.2)

private theorem Task.prepare (q : Task m p) (a : q.s.St) (c : q.s.Ct)
    (ha : a ∈ q.rest.stations) (he : q.rest.positions.Perm (a.pos :: c.positions))
    (hc : c.inserts ⊆ q.rest.inserts) (d l : ℕ) [ExpChar F d] (hP : p.P = d ^ l) :
      let A := powered p.P m.A
      let B := m.B
      a.pos ^ p.P ∈ A ∧ a.pos ∈ B ∧ q.mover.pos ^ p.P ∉ A ∧ q.mover.pos ∉ B ∧
        c.Fixed p.P (A.erase (a.pos ^ p.P)) (B.erase a.pos) := by
  rw [← q.sites, ← q.inserts, hP]
  have hv := q.move.distinct q.valid
  have ht : a.pos ∉ c.sites := fun h =>
    (List.nodup_cons.mp (he.nodup_iff.mp hv.1)).1 (List.mem_toFinset.mp h)
  have hs : c.sites ⊆ q.rest.sites := fun i hi =>
    List.mem_toFinset.mpr (he.mem_iff.mpr (.tail _ (List.mem_toFinset.mp hi)))
  have hb := q.rest.mem_inserts ha
  exact ⟨mem_image_of_mem _ (q.rest.inserts_sub hb), hb, (powered_iff _ _ _ _).not.mpr hv.2,
    fun h => hv.2 (q.rest.inserts_sub h), c.fixed_erase d l a.pos ht _ _ hs
      (fun i hi => mem_erase.mpr ⟨fun h => ht (h ▸ c.inserts_sub hi), hc hi⟩)⟩

theorem Job.absorb (q₀ : Task m p) (rec : m.Subtasks p ν) (hn : m.n ≤ p.U) (safe : Covers m.a.ports m.v (p.U - m.n))
    (a : Entry F r t K N) (ha : a ∈ m.tail) (d l : ℕ) [ExpChar F d] (hP : p.P = d ^ l)
    (j : ℤ) (hj : j ≤ if a.role = .collector then (p.g * m.threshold p : ℕ) else 0) :
    m.Solvable p ν (m.evalAt p a.pos j) := by
  obtain ⟨ls, rs, hxs⟩ := List.append_of_mem ha
  let I := m.pairs p.P a j
  let M (i : I) := m.a.edit m.v (a.merge m.x i.val :: (ls ++ rs))
  have cont (i : I) : ∃ f : Script F r t J L K N, f.Ordered ν m.n p.U ∧
      Fintype.card f.I ≤ p.limit F ^ (m.fuel p - 1) ∧ f.Resumes p (M i) m.v := by
    refine rec.resume _ _ (a.merge m.x i.val) (ls ++ rs) _ (by simp [M, Record.edit]) ?_ hn safe ?_
    · simp only [Entry.merge, m.active]; split_ifs <;> simp
    · simp only [fuel, hxs, List.length_append, List.length_cons]; omega
  choose f hf hc hg using cont
  have size : Fintype.card I ≤ p.fan F := by
    have bound : j ≤ (p.g * (p.P * p.D + p.D + 2 * p.P * p.H) : ℕ) := by
      have ht := q₀.move.threshold_le (H := p.H) (P := p.P) (q₀.room _ .refl)
      change m.threshold p ≤ _ at ht
      have := Nat.mul_le_mul_left p.g ht
      split_ifs at hj <;> omega
    obtain ⟨hA, hB⟩ := (q₀.s.scene.cell (q₀.R.vertex m.v)).order_bounds q₀.s.scene.level
      (q₀.room _ .refl _).2
    rw [q₀.orderA] at hA
    rw [q₀.orderB] at hB
    rw [Fintype.card_coe]
    refine (card_filter_le _ _).trans ((pairs_card hA hB bound).trans ?_)
    unfold Params.fan width
    exact (Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_mul_of_pos_right _ (by positivity))
  let sig := rotSign (m.x::ls) a
  let res := Script.sum (fun _ : I => (1 : F)) f
  refine ⟨res.times sig, Script.ordered_sum (fun _ : I => (1 : F)) f hf,
    (Script.card_sum (fun _ : I => (1 : F)) f hc).trans (Nat.mul_le_mul_right _ size), fun q => ?_⟩
  let v := q.R.vertex m.v
  let b := q.mover
  obtain ⟨xs, ys, u, er, hl, hu, hr⟩ := split_match (hxs ▸ q.rows.2)
  let c : q.s.Ct := ⟨q.rest.ports, xs++ys⟩
  let s := q.s.reord v (b::xs) [u] ys
  have here : (q.s.scene.cell v).stations = (b::xs) ++ u :: ys := by simp [v, b, q.here, Cell.insert, er]
  obtain ⟨upd, eqn⟩ := q.match'.rotate (p := p) q.valid m.v (b::xs) ys u (m.x::ls) rs a here
    (.cons q.rows.1 hl) hr hu
  have loc : s.scene.cell v = (c.insert b).insert u := by simp [s, reord, put, Scene.put, v, q.here, Cell.insert, c]
  have moved : b.label.role = .active m.n := q.rows.1.role.trans m.active
  have other (w) (h : w ≠ v) : s.scene.cell w = q.s.scene.cell w := by
    simp [s, reord, put, Scene.put, h]
  have idle' : ∀ w ∈ u :: c.stations, idle q.allowed v w := by
    intro w hw
    apply q.others
    rw [er]; exact List.perm_middle.mem_iff.mpr hw
  have ready : s.Ready v (u :: c.stations) := by
    refine ⟨fun w h => (idle' w h).1, fun w hw z hz => ?_⟩
    rw [other _ hw] at hz
    exact (q.away _ hw _ hz).1
  have hperm : q.rest.positions.Perm (u.pos :: c.positions) := by
    simp only [Cell.positions, er, c, List.map_append, List.map_cons, List.append_assoc, List.cons_append]
    exact List.perm_middle
  have hm : u ∈ q.rest.stations := by rw [er]; simp
  have hc : c.inserts ⊆ q.rest.inserts := by
    simp only [Cell.inserts, c, er, List.map_append, List.map_cons, List.toFinset_append, List.toFinset_cons]
    exact union_subset_union Subset.rfl (subset_insert _ _)
  obtain ⟨HA, HB, HA', HB', fixed⟩ := q.prepare _ _ hm hperm hc d l hP
  have eA : (s.scene.cell v).orderA s.scene.level = m.d := by
    rw [← q.orderA, loc, q.here]
    simp only [Cell.orderA, s, reord, put, Scene.put, Cell.insert, c, er, sumA, List.map_cons, List.sum_cons,
      List.map_append, List.sum_append, b]
    omega
  have eB : (s.scene.cell v).orderB = m.e := by
    rw [← q.orderB, loc, q.here]
    simp only [Cell.orderB, s, reord, put, Scene.put, Cell.insert, c, er, sumB, List.map_cons, List.sum_cons, List.map_append, List.sum_append, b]
    omega
  let U (i : I) := mergeAt u b (u.label.join b.label) i.val
  let Q (i : I) := s.put v (c.insert (U i))
  have pairs : merges p.P u b ((s.scene.cell v).orderA s.scene.level) (s.scene.cell v).orderB j = I := by
    rw [eA, eB]
    simp only [I, merges, Job.pairs, hu.left, hu.right, b, q.rows.1.left, q.rows.1.right]
  have update (i : I) : Update p.P p.g p.H p.U q.R q.β q.β s (Q i) (M i) [] := by
    have hb : j ≤ if u.label.role = .collector then (p.g * (energyOf p.P b + 2 * p.P * p.H) : ℕ) else 0 := by
      rw [hu.role]; exact hj
    have hstep : s.Step p.P p.g p.H p.U (Q i) :=
      .merge _ _ _ _ _ _ loc moved ready _ _ (by erw [pairs]; exact i.property) hb
    refine ⟨.single hstep, upd.valid.merge v c u b _ loc moved ready i.val, ?_, Outside.put _ (Set.mem_range_self m.v) _⟩
    have step := upd.match'.edit m.v (c.insert (U i)) (a.merge m.x i.val :: (ls++rs))
      (by rw [loc]; rfl) (.cons (hu.merge q.rows.1 (by rw [moved]; simp) _) (List.rel_append hl hr)) s.expired
    simp only [Record.edit, Function.update_idem] at step
    exact step
  have branch (i : I) : (f i).Executes p.P p.g p.H p.U q.R q.β s q.allowed ((Q i).value p.P) := by
    let w := (q.toWorld.next upd).next (update i)
    have e : (Q i).scene.cell v = c.insert (U i) := by
      simp only [Q, put, Scene.put]
      erw [Function.update_self]
    have away z (hz : z ≠ v) : (Q i).scene.cell z = q.s.scene.cell z := by
      exact (Function.update_of_ne hz (c.insert (U i)) s.scene.cell).trans (other z hz)
    have h := hg i w c (U i) e (fun x hx => idle' x (.tail _ hx)) (by
      intro z hz y hy
      change y ∈ ((Q i).scene.cell z).stations at hy
      rw [away z hz] at hy
      exact q.away _ hz _ hy)
    exact h.prior (update i)
  have value : s.observe p.P v (m.test p.P a.pos j) = fun x => ∑ i : I, (1 : F) * (Q i).value p.P x := by
    have e := s.scene.merge d l v c u b loc (u.label.join b.label) _ _
      (by rwa [← hP]) HB (by rwa [← hP]) HB' (by rwa [← hP]) j
    rw [← hP] at e
    dsimp only at e
    erw [pairs, hu.pos] at e
    funext x
    unfold observe Job.test
    rw [funext e, trace_sum]
    simp only [one_mul]
    rfl
  have h := Script.executes_sum (fun _ : I => (1 : F)) f _ branch
  rw [← value] at h
  change (res.times sig).Executes _ _ _ _ _ _ _ _ (q.s.observe _ _ _)
  rw [eqn (m.test p.P a.pos j) (coefficient_signed _ _ _ _ _)]
  exact (h.prior upd).times _

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Crossing a seam inside a common local script -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Gate

open Finset Motion Stage Function
open scoped Classical
variable {F J L K N : Type} [Field F] [Fintype F] {r t : ℕ} {p : Params}
  {m : Job F r t J L K N} {ν : ℕ → K}

variable (G : Gate m)

def result (P : ℕ) (key : K) (j : ℤ) (i : G.indices P j) :=
  m.a.cross m.v G.w G.i m.x key i.2.1.val (G.root P i.2.2.2) i.height i.2.2.1.val

variable (d l : ℕ) [ExpChar F d] (hP : p.P = d ^ l) (hF : p.M * (2 * p.D + 1) < Fintype.card F)
  (j : ℤ) (hj : m.threshold p ≤ -j)

def out (q : Task m p) (i : G.indices p.P j) := q.s.advance (G.path d l hP hF j hj q)
  (q.R.vertex m.v) (q.R.vertex G.w) (q.R.edge G.i) (G.near q) (G.far q) (lowering F r) i

theorem enact (q : Task m p) (hn : m.n < p.U) (k : K) (i : G.indices p.P j) :
    Update p.P p.g p.H p.U q.R q.β (allocate q.β q.s.hidden.length k) q.s
      (G.out d l hP hF j hj q i) (G.result p.P k j i) [(k, m.x.b)] := by
  let a := G.path d l hP hF j hj q
  have ha : q.mover.label.role = .active m.n := q.rows.1.role.trans m.active
  have hv : q.s.scene.cell (q.R.vertex m.v) = ((G.near q).plug (q.R.edge G.i) a.z).insert q.mover := by
    change _ = ((G.near q).plug _ G.z).insert _
    rw [G.near_eq, q.here]
  have hw := (G.far_eq q).symm
  have ne := q.R.vertex.injective.ne G.ne
  have step : q.s.Step p.P p.g p.H p.U (G.out d l hP hF j hj q i) :=
    .cross _ _ _ _ _ _ _ a _ i m.n hv hw ne (q.match'.level G.i) rfl ha hn q.move.ready rfl
  have fresh₁ : i.2.1.val ∉ ((G.near q).plug (q.R.edge G.i) G.z).positions := by
    rw [G.near_eq]
    intro h
    have h' : i.2.1.val ∈ q.rest.sites := List.mem_toFinset.mpr h
    rw [q.sites] at h'
    exact (mem_sdiff.mp i.2.1.property).2 h'
  have fresh₂ : G.root p.P i.2.2.2 ∉ ((G.far q).plug (q.R.edge G.i) G.y).positions := by
    rw [G.far_eq]
    intro h
    have h' : G.root p.P i.2.2.2 ∈ (q.s.scene.cell (q.R.vertex G.w)).sites := List.mem_toFinset.mpr h
    rw [q.match'.sites] at h'
    exact (mem_sdiff.mp (mem_image.mp i.2.2.2.property).choose_spec.1).2 h'
  exact ⟨.single step,
    q.valid.advance _ _ _ _ _ _ a _ i m.n hv hw ne ha hn q.move.ready fresh₁ fresh₂,
    q.match'.advance a _ _ _ _ _ i m.x k hv hw G.ne (by rw [m.row]; rfl) (by rw [ha]; simp),
    Outside.advance a (Set.mem_range_self m.v) (Set.mem_range_self G.w) (Set.mem_range_self G.i)
      _ _ _ i k⟩

theorem follows (q : Task m p) (hn : m.n < p.U) (k : K) (i : G.indices p.P j)
    (S : Script F r t J L K N) (hS : S.Resumes p (G.result p.P k j i) G.w) :
    q.executes (S.prepend [(k, m.x.b)]) ((G.out d l hP hF j hj q i).value p.P) := by
  let a := G.path d l hP hF j hj q
  let u := G.enact d l hP hF j hj q hn k i
  let w := q.toWorld.next u
  let z := G.out d l hP hF j hj q i
  let v := q.R.vertex G.w
  let c : z.Ct := (q.s.scene.cell v).pull Prod.fst id
  let arrives := a.arrives (q.mover.label.take q.s.hidden.length) (lowering F r) i
  have he : z.scene.cell v = c.insert arrives := by
    simp only [z, out, v, Stage.advance, Scene.crossed, update_self, Passage.right]
    change (((G.far q).plug _ G.y).pull Prod.fst id).insert _ = _
    rw [G.far_eq]; rfl
  have hi : ∀ x ∈ c.stations, idle q.allowed v x := by
    intro x hx
    obtain ⟨x, hxin, rfl⟩ := List.mem_map.mp hx
    exact q.away _ (q.R.vertex.injective.ne G.ne.symm) x hxin
  have other : ∀ j, j ≠ v → ∀ x ∈ (z.scene.cell j).stations, idle q.allowed j x := by
    intro y hy x hx
    change y ≠ q.R.vertex G.w at hy
    simp only [z, out, Stage.advance, Scene.crossed, update_of_ne hy] at hx
    by_cases h : y = q.R.vertex m.v
    · subst y
      rw [update_self] at hx
      rcases List.mem_cons.mp hx with rfl|hx
      · exact ⟨rfl, fun _ h => by cases h⟩
      · obtain ⟨x, hxin, rfl⟩ := List.mem_map.mp hx
        exact q.others x hxin
    rw [update_of_ne h] at hx
    obtain ⟨x, hxin, rfl⟩ := List.mem_map.mp hx
    exact q.away y h x hxin
  exact (hS w c arrives he hi other).before u

theorem value (q w : Task m p) :
    m.evalAt p G.z j q = fun x =>
      ∑ i : G.indices p.P j, (G.path d l hP hF j hj w).signed w.s.scene.level (G.near w) (G.far w) d l hP i *
        (G.out d l hP hF j hj q i).value p.P x := by
  let a := G.path d l hP hF j hj q
  have hv : q.s.scene.cell (q.R.vertex m.v) = ((G.near q).plug (q.R.edge G.i) a.z).insert q.mover := by
    change _ = ((G.near q).plug _ G.z).insert _
    rw [G.near_eq, q.here]
  obtain ⟨hl, hr, other⟩ := G.available_ports q
  have h := q.s.scene.cross a _ _ _ _ _ (Tag.leave q.s.hidden.length) (q.mover.label.take q.s.hidden.length)
    d l hP (G.fits d l hP hF j hj q) (q.R.vertex.injective.ne G.ne)
    (q.match'.level G.i) hv (G.far_eq q).symm hl hr other
  funext x
  change traceStack t x q.s.hidden (q.s.scene.observe p.P (q.R.vertex m.v) a.coeff) = _
  rw [funext h, trace_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [trace_mul, G.uniform d l hP hF j hj q w i]
  rfl

include hP hF hj in
theorem exit (w : Task m p) (rec : m.Subtasks p ν) (hn : m.n < p.U)
    (safe : Covers m.a.ports G.w (p.U - (m.n + 1))) :
    m.Solvable p ν (m.evalAt p G.z j) := by
  let I := G.indices p.P j
  let k := ν m.n
  let f (i : I) := (G.path d l hP hF j hj w).signed w.s.scene.level (G.near w) (G.far w) d l hP i
  obtain ⟨_, _, hnear, _, hlen⟩ := G.room w
  have decr : (p.U - (m.n + 1)) * (p.M + 1) + (m.a.rows G.w).length < m.fuel p := by
    unfold Job.fuel
    rw [show p.U - m.n = (p.U - (m.n + 1)) + 1 by omega, add_mul]
    omega
  have size : Fintype.card I ≤ p.fan F := by
    have card (s : Finset F) : s.card ≤ Nat.card F + 1 := by
      rw [Nat.card_eq_fintype_card]; exact (card_le_univ s).trans (by omega)
    apply hop_card _ _ _ _ _ _ _ (card _) (card _)
    · omega
    · omega
    · omega
  have cont (i : I) : ∃ S : Script F r t J L K N, S.Ordered ν (m.n + 1) p.U ∧
      Fintype.card S.I ≤ p.limit F ^ (m.fuel p - 1) ∧ S.Resumes p (G.result p.P k j i) G.w := by
    let x := m.x.taken k (G.root p.P i.2.2.2) i.2.2.1.val
    refine rec.resume _ _ x (m.a.rows G.w) _ ?_ ?_ (by omega) safe decr
    · simp [result, Record.cross, x]
    · exact .inl (by simp [x, Entry.taken, m.active, Role.clock])
  choose S hS hc hf using cont
  let prog i := (S i).prepend [(k, m.x.b)]
  have order (i) : (prog i).Ordered ν m.n p.U := (hS i).emit _
  refine ⟨Script.sum f prog, Script.ordered_sum f prog order,
    (Script.card_sum f prog hc).trans (Nat.mul_le_mul_right _ size), fun q => ?_⟩
  rw [G.value d l hP hF j hj q w]
  exact Script.executes_sum f prog _ (fun i => G.follows d l hP hF j hj q hn k i (S i) (hf i))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Gate
end

/-! # Selecting a dormant original mark by position -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset Function Stage
open scoped Classical
variable {F J L K N : Type} [Field F] {r t : ℕ} {p : Params} {ν : ℕ → K}

theorem Record.select (a : Record F r t J L K N) (v : J) (z : F) (safe : Covers a.ports v p.U)
    (complete : ∀ m : Job F r t J L K N, m.n = 0 → Covers m.a.ports m.v p.U → m.Solves p ν) :
    ∃ f : Script F r t J L K N, f.Ordered ν 0 p.U ∧ f.Runs a p.P p.g p.H p.U p.M p.D v z ∧
      Fintype.card f.I ≤ p.limit F ^ ((p.U + 1) * (p.M + 1)) := by
  by_cases h : (z, Role.active 0) ∈ (a.rows v).map (fun u => (u.pos, u.role))
  swap
  · refine ⟨Script.pure a, Script.ordered_pure _ (Nat.zero_le _), ?_,
      by rw [Script.card_pure]; exact pow_pos (p.limit_pos F) _⟩
    intro V E T X _ _ R β s src dst match' _ valid _ calm
    apply Script.executes_pure (.refl match' valid) calm
    intro j hj
    refine ⟨hj, ?_⟩
    rintro rfl
    obtain ⟨u, hu, he, n, hn⟩ := hj
    have hn' := calm _ u hu
    rw [hn] at hn'
    change n = 0 at hn'
    apply h
    rw [← match_role (match'.rows v)]
    exact List.mem_map.mpr ⟨u, hu, Prod.ext he (hn.trans (by rw [hn']))⟩
  obtain ⟨e, he, hz, hn⟩ : ∃ e ∈ a.rows v, e.pos = z ∧ e.role = .active 0 := by
    simpa only [List.mem_map, Prod.mk.injEq] using h
  obtain ⟨l, b, hs⟩ := List.append_of_mem he
  let m : Job F r t J L K N :=
    ⟨a.edit v (e::(l++b)), v, e, l++b, 0, by simp [edit], hn⟩
  have bounded : m.Bounded p ν (p.limit F ^ ((p.U + 1) * (p.M + 1))) (fun q => q.s.value p.P) := by
    by_cases h : Nonempty (Task m p)
    · obtain ⟨q⟩ := h
      have e := (q.match'.rows m.v).length_eq
      rw [m.row, List.length_cons] at e
      have len := ((q.room _ .refl) (q.R.vertex m.v)).1
      simp only [Cell.positions, List.length_append, List.length_map] at len
      have lim : m.fuel p ≤ (p.U + 1) * (p.M + 1) := by
        unfold Job.fuel
        rw [show m.n = 0 from rfl, Nat.sub_zero, add_mul]
        omega
      obtain ⟨f, hf, hc, ht⟩ := complete m rfl safe
      exact ⟨f, hf, hc.trans (Nat.pow_le_pow_right (p.limit_pos F) lim), ht⟩
    · exact Job.vacuous (pow_pos (p.limit_pos F) _) (Nat.zero_le _) h _
  obtain ⟨f, hf, hh, ht⟩ := bounded
  refine ⟨f.times (rotSign l e), hf, ?_, hh⟩
  intro V E T X _ _ R β s src dst hm hl hv hroom calm
  let A := pending s \ {(R.vertex v, z)}
  let world : World p a := ⟨T, X, V, E, R, β, s, src, dst, A, hm, hl, hv, hroom⟩
  obtain ⟨xs, ys, u, here, hxs, hu, hys⟩ := split_match (hs ▸ hm.rows v)
  obtain ⟨upd, eqn⟩ := hm.rotate (p := p) hv v xs ys u l b e here hxs hys hu
  let s' := s.reord (R.vertex v) xs [u] ys
  let c : s.Ct := ⟨(s.scene.cell (R.vertex v)).ports, xs++ys⟩
  have loc : s'.scene.cell (R.vertex v) = c.insert u := by simp [s', reord, put, Scene.put, c, Cell.insert]
  have old (j : V) (x : s.St) (hx : x ∈ (s.scene.cell j).stations) (h : (j, x.pos) ≠ (R.vertex v, z)) :
      idle A j x := ⟨calm _ _ hx, fun n hn => ⟨⟨x, hx, rfl, n, hn⟩, h⟩⟩
  have rest : ∀ x ∈ c.stations, idle A (R.vertex v) x := by
    intro x hx
    apply old
    · rw [here]; exact List.perm_middle.mem_iff.mpr (.tail _ hx)
    · have hh := upd.valid.distinct (R.vertex v)
      erw [loc, Cell.positions_insert, List.nodup_cons] at hh
      intro h
      have he := (congrArg Prod.snd h).trans (hu.pos.trans hz).symm
      exact hh.1 (List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, he⟩))
  have away : ∀ j, j ≠ R.vertex v → ∀ x ∈ (s'.scene.cell j).stations, idle A j x := by
    intro j hj x hx
    simp only [s', reord, put, Scene.put, update_of_ne hj] at hx
    exact old j x hx (fun h => hj (congrArg Prod.fst h))
  let q : Task m p := ⟨world.next upd, c, u, loc, rest, away⟩
  have lower : f.Executes p.P p.g p.H p.U R β s' A (s'.value p.P) := ht q
  have he := eqn forms forms_signed
  rw [observe_forms, observe_forms] at he
  rw [he]
  exact (lower.prior upd).times _

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# A bounded-radius motion script

Only a crossing changes the current cell. Every such change decreases
the remaining radius. A continued fusion consumes a stationary mark.
Together these give a bound on the number of steps independent of the
size of the ambient graph.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset Motion Stage
open scoped Classical
variable {F J L K N : Type} [Field F] {r t : ℕ} {p : Params}
  {m : Job F r t J L K N} {ν : ℕ → K}

abbrev Job.choices (m : Job F r t J L K N) (p : Params) (c : F) :=
  Σ z : m.A, Fin (orders m.seams c (m.order p.P) p.g (m.threshold p) z.val)

def Job.degree (m : Job F r t J L K N) (p : Params) (c : F) (i : m.choices p c) : ℤ :=
  (i.2.val : ℤ) - m.order p.P i.1.val

private theorem Task.collector (q : Task m p) :
    ∃ a ∈ m.tail, a.role = .collector := by
  obtain ⟨c, hc, h⟩ := q.move.collector q.valid
  have he : (c.pos, Role.collector) ∈ m.tail.map (fun a => (a.pos, a.role)) := by
    rw [← match_role q.rows.2]
    exact List.mem_map.mpr ⟨c, hc, by rw [h]⟩
  obtain ⟨a, ha, h⟩ := List.mem_map.mp he
  exact ⟨a, ha, congrArg Prod.snd h⟩

private theorem Task.choices_le (q : Task m p) (c : F) :
    Fintype.card (m.choices p c) ≤ p.M * window p.P p.g p.H p.D := by
  have room := q.room _ .refl
  have hd : ∀ i, m.order p.P i ≤ p.P * p.D + p.D := by
    intro i
    have e := q.move.order_le (P := p.P) room i
    change poleOrder _ ((q.s.scene.cell (q.R.vertex m.v)).orderA q.s.scene.level)
      (q.s.scene.cell (q.R.vertex m.v)).orderB q.rest.inserts i ≤ _ at e
    rw [q.orderA, q.orderB, q.inserts] at e
    exact e
  exact orders_card hd (q.move.threshold_le room) (q.sites ▸ (q.move.room room).1)

private theorem Job.interpolate (q₀ : Task m p) (d l : ℕ) [ExpChar F d] (hP : p.P = d ^ l)
    (c : Entry F r t K N) (hc : c ∈ m.tail) :
    ∃ f : m.choices p c.pos → F, ∀ q : Task m p, ∀ x : q.X,
      q.s.value p.P x = ∑ i, f i * m.evalAt p i.1.val (m.degree p c.pos i) q x := by
  rcases p with ⟨P, g, H, U, M, D⟩
  change P = d ^ l at hP
  subst P
  let p : Params := ⟨d ^ l, g, H, U, M, D⟩
  have hc' : c.pos ∈ m.B := List.mem_toFinset.mpr (List.mem_map_of_mem hc)
  have hd : c.pos ∉ m.seams := by
    rw [← q₀.seams]
    exact disjoint_left.mp (q₀.rest.disjoint (q₀.move.distinct q₀.valid).1) (q₀.inserts.symm ▸ hc')
  have hg : m.seams.card ≤ g := by
    have e := q₀.layout.degree (q₀.R.vertex m.v)
    rw [Stage.ports, q₀.here] at e
    rw [← q₀.seams]
    exact (List.toFinset_card_le _).trans ((List.length_map _).le.trans e)
  have hz : m.x.pos ∉ m.A := by rw [← q₀.sites]; exact (q₀.move.distinct q₀.valid).2
  obtain ⟨f, hf⟩ := reconstruct_cells (r := r) (t := t) d l m.d m.e m.A m.B m.seams
    subset_union_left subset_union_right c.pos (mem_union_left _ hc') hd g (m.threshold p) hg m.x.pos hz
  refine ⟨f, fun q x => ?_⟩
  let v := q.R.vertex m.v
  have st : ∀ a ∈ (q.s.scene.cell v).stations, a.pos = m.x.pos ∨ a.pos ∈ m.B := by
    rw [q.here, ← q.inserts]
    exact List.forall_mem_cons.mpr ⟨.inl rfl, fun _ h => .inr (q.rest.mem_inserts h)⟩
  have pt : ∀ i ∈ (q.s.scene.cell v).ports, i.2 ∈ m.A := by
    rw [q.here, ← q.sites]
    exact fun i h => q.rest.seams_sub (q.rest.mem_seams h)
  have e (x : Stack q.X t q.s.hidden) : q.s.scene.value p.P x = ∑ i : m.choices p c.pos,
      f i * q.s.scene.observe p.P v (m.test p.P i.1.val (m.degree p c.pos i)) x :=
    contractGraph_replace _ _ v f _ (fun h hh => hf _ _ q.orderA q.orderB st pt x h (fun i _ => hh _))
  change traceStack t x q.s.hidden (q.s.scene.value p.P) = _
  rw [funext e, trace_sum]
  exact sum_congr rfl fun i _ => trace_mul _ _ _ _ _

variable [Fintype F]

private theorem Job.next (d l : ℕ) [ExpChar F d] (hP : p.P = d ^ l)
    (hF : p.M * (2 * p.D + 1) < Fintype.card F) (hn : m.n < p.U)
    (safe : Covers m.a.ports m.v (p.U - m.n)) (rec : m.Subtasks p ν) : m.Solves p ν := by
  by_cases real : Nonempty (Task m p)
  swap
  · exact Job.vacuous (pow_pos (p.limit_pos F) _) hn.le real _
  obtain ⟨q⟩ := real
  obtain ⟨c, hc, hc'⟩ := q.collector
  obtain ⟨f, hf⟩ := Job.interpolate q d l hP c hc
  have solve (i : m.choices p c.pos) :
      m.Solvable p ν (m.evalAt p i.1.val (m.degree p c.pos i)) := by
    let z := i.1.val
    let j := m.degree p c.pos i
    have hi : i.2.val < orders m.seams c.pos (m.order p.P) p.g (m.threshold p) z := i.2.isLt
    change m.Solvable p ν (m.evalAt p z j)
    by_cases hs : z ∈ m.seams
    · have he : (m.threshold p : ℤ) ≤ -j := by
        conv at hi => rhs; rw [orders, ite_eq_left hs]
        dsimp only [j, z, degree] at *
        omega
      obtain ⟨G, hg, h'⟩ := Gate.of_cover safe hn hs
      rw [← hg]
      exact G.exit d l hP hF _ he q rec hn h'
    conv at hi => rhs; rw [orders, ite_eq_right hs]
    by_cases ht : z = c.pos
    · rw [ite_eq_left ht] at hi
      have he : j ≤ (p.g * m.threshold p : ℕ) := by dsimp only [j, z, degree] at *; omega
      rw [ht]
      exact Job.absorb q rec hn.le safe c hc d l hP j (by rw [ite_eq_left hc']; exact he)
    rw [ite_eq_right ht] at hi
    have he : j ≤ 0 := by dsimp only [j, z, degree] at *; omega
    have hz : z ∈ m.B := (mem_union.mp i.1.property).resolve_right hs
    obtain ⟨u, hu, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
    rw [← heq]
    exact Job.absorb q rec hn.le safe u hu d l hP j (by split_ifs <;> omega)
  have fuel : 0 < m.fuel p := by
    have : 0 < p.U - m.n := by omega
    unfold Job.fuel
    positivity
  obtain ⟨z, hz, hb, h⟩ := Job.combine f _ solve fuel (q.choices_le c.pos)
  exact ⟨z, hz, hb, fun q => by change q.executes z (q.s.value p.P); rw [funext (hf q)]; exact h q⟩

/-- Complete the designated move, or leave the region unchanged if its
original station was already absorbed. The script and weights do not
depend on the interpretation of local indices in the ambient graph. -/
theorem Record.run (a : Record F r t J L K N) (p l : ℕ) [ExpChar F p] (g H U M D : ℕ)
    (hF : M * (2 * D + 1) < Fintype.card F) (v : J) (z : F) (ν : ℕ → K) (safe : Covers a.ports v U) :
    ∃ q : Script F r t J L K N, q.Ordered ν 0 U ∧ q.Runs a (p ^ l) g H U M D v z ∧
      Fintype.card q.I ≤ breadth (p ^ l) g H M D (Nat.card F + 1) ^ ((U + 1) * (M + 1)) := by
  let P : Params := ⟨p ^ l, g, H, U, M, D⟩
  have go (m : Job F r t J L K N) (hn : m.n ≤ U) (hc : Covers m.a.ports m.v (U - m.n)) :
      m.Solves P ν := by
    induction h : m.fuel P using Nat.strong_induction_on generalizing m with
    | h n ih =>
      by_cases he : m.n = U
      · exact Job.expire he
      apply Job.next p l rfl hF (lt_of_le_of_ne hn he) hc
      intro q he hn' safe'
      exact ih _ (he.trans_eq h) q hn' safe' rfl
  exact a.select (p := P) v z safe (fun m he h => go m (by omega) (by simpa [he] using h))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Restricting a named surface record to a local region -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open scoped Classical
variable {F T V E X J L K N J' L' : Type} {r t : ℕ}
  (R : Reference J L N V E T X)

def Reference.region (vertex : J' ↪ V) (edge : L' ↪ E) : Reference J' L' N V E T X :=
  ⟨vertex, edge, R.name, R.key, R.ext, R.empty⟩

def Reference.world := R.region (.refl V) (.refl E)

variable {R} {R' : Reference J' L' N V E T X} {β : V ⊕ ℕ → K}
  {s : Stage F r t T V E X}

theorem Represents.change {u : s.St} {a : Entry F r t K N}
    (h : Represents R β s.hidden u a)
    (hk : R.key = R'.key) (hn : R.name = R'.name) (he : R.ext = R'.ext) :
    Represents R' β s.hidden u a :=
  ⟨h.pos, h.left, h.right, h.role, hn ▸ h.name, h.named, h.known, he ▸ hk ▸ h.label⟩

structure View (G : Record F r t V E K N) (f : J ↪ V) (g : L ↪ E)
    (a : Record F r t J L K N) : Prop where
  rows : ∀ i, G.rows (f i) = a.rows i
  ports : ∀ i, G.ports (f i) = (a.ports i).map (Prod.map g id)
  level : ∀ j, G.level (g j) = a.level j
  footprint : ∀ i, G.footprint (f i) = a.footprint i

variable {G : Record F r t V E K N} {a : Record F r t J L K N}

theorem Matches.view (h : Matches R'.world β s G)
    (v : View G R.vertex R.edge a)
    (hk : R'.key = R.key) (hn : R'.name = R.name) (he : R'.ext = R.ext) :
    Matches R β s a := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => h.known (R.vertex i)⟩
  · rw [← v.rows]
    exact (h.rows (R.vertex i)).imp fun u _ h => h.change (s := s) hk hn he
  · rw [← v.ports]
    have hc := h.ports (R.vertex i)
    change _ = (G.ports (R.vertex i)).map id at hc
    rwa [List.map_id] at hc
  · exact (h.level _).trans (v.level _)
  · exact (h.footprint _).trans (v.footprint _)

theorem View.unique {f : J ↪ V} {g : L ↪ E} {b : Record F r t J L K N}
    (h : View G f g a) (i : View G f g b) : a = b := by
  obtain ⟨ar, ap, al, af⟩ := a
  obtain ⟨br, bp, bl, bf⟩ := b
  congr 1
  · exact funext fun j => (h.rows j).symm.trans (i.rows j)
  · funext j
    exact (g.injective.prodMap Function.injective_id).list_map ((h.ports j).symm.trans (i.ports j))
  · exact funext fun j => (h.level j).symm.trans (i.level j)
  · exact funext fun j => (h.footprint j).symm.trans (i.footprint j)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# Independent scripts on disjoint regions

A wave of local scripts acts by a product of its kernels. Sequential
execution proves this identity, allocating fresh keys in command order.
Each command's output is unaffected by the other commands.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Finset
open scoped Classical

structure Command (F : Type) [Field F] (r t : ℕ) (T V E X K N : Type)
    (P g H U M D : ℕ) (key : V → X → ℕ) where
  vertices : Type
  edges : Type
  ref : Reference vertices edges N V E T X
  shared : ref.key = key
  input : Record F r t vertices edges K N
  action : Script F r t vertices edges K N
  start : vertices
  pos : F
  runs : action.Runs input P g H U M D start pos

variable {F T V E X K N : Type} [Field F] {r t P g H U M D n : ℕ}
  {key : V → X → ℕ} {src dst : E → V}

local notation "Cmd" => Command F r t T V E X K N P g H U M D key
local notation "St" => Stage F r t T V E X

def Command.target (c : Cmd) := (c.ref.vertex c.start, c.pos)

omit [Field F] in
theorem Outside.rekey {B : Set V} {A : Set E} {a b : St} {β γ : V ⊕ ℕ → K}
    {add : List (K × ℕ)} {left right : V → X → ℕ}
    (h : Outside B A left a b β γ add) (he : left = right) : Outside B A right a b β γ add :=
  he ▸ h

namespace Wave

variable (C : Fin n → Command F r t T V E X K N P g H U M D key)

def vertices : Set V := {v | ∃ i, v ∈ Set.range (C i).ref.vertex}
def edges : Set E := {v | ∃ i, v ∈ Set.range (C i).ref.edge}

structure Separate : Prop where
  vertex : ∀ i j, i ≠ j → Disjoint (Set.range (C i).ref.vertex) (Set.range (C j).ref.vertex)
  edge : ∀ i j, i ≠ j → Disjoint (Set.range (C i).ref.edge) (Set.range (C j).ref.edge)

abbrev Index : Type := ∀ i, (C i).action.I

def fresh (a : Index C) := (List.ofFn fun i => (C i).action.fresh (a i)).flatten

/-- Witnesses where each fresh key was created, in command order. -/
def Execution : {n : ℕ} → (C : Fin n → Cmd) → Index C →
    St → St → (V ⊕ ℕ → K) → (V ⊕ ℕ → K) → Prop
  | 0, _, _, s, q, β, γ => s = q ∧ β = γ
  | _ + 1, C, a, s, q, β, γ =>
      ∃ p β', Update P g H U (C 0).ref β β' s p ((C 0).action.result (a 0))
          ((C 0).action.fresh (a 0)) ∧ Execution (Fin.tail C) (Fin.tail a) p q β' γ

structure Finish (s q : St) (β γ : V ⊕ ℕ → K) (a : Index C) : Prop where
  history : Execution C a s q β γ
  reach : s.Reach P g H U q
  valid : q.Valid U
  calm : Calm q
  pending : Local.pending q ⊆ Local.pending s \ Set.range (Command.target ∘ C)
  outside : Outside (vertices C) (edges C) key s q β γ (fresh C a)
  result : ∀ i, Matches (C i).ref γ q ((C i).action.result (a i))

private theorem layout_of_reach {s q : St} (h : s.Reach P g H U q) (hl : s.Layout src dst g) :
    q.Layout src dst g := by
  induction h with
  | refl => exact hl
  | tail _ step ih => exact step.layout ih

variable [Fintype V] [Fintype E]

/-- Local results, scalar weights and independently chosen indices work
simultaneously for all values of the ordinary parameters. -/
theorem execute (h : Separate C) (s : St) (β : V ⊕ ℕ → K)
    (hin : ∀ i, Matches (C i).ref β s (C i).input) (hl : s.Layout src dst g)
    (hv : s.Valid U) (hr : ∀ q, s.Reach P g H U q → q.Room M D) (hc : Calm s) :
    ∃ (q : Index C → St) (γ : Index C → V ⊕ ℕ → K),
      (∀ a, Finish C s (q a) β (γ a) a) ∧
      ∀ x, s.value P x = ∑ a, (∏ i, (C i).action.weight (a i)) * (q a).value P x := by
  induction n generalizing s β with
  | zero =>
    refine ⟨fun _ => s, fun _ => β, fun a => ?_, by simp⟩
    refine ⟨⟨rfl, rfl⟩, .refl, hv, hc, by simp, ?_, fun i => i.elim0⟩
    simp only [fresh, List.ofFn_zero, List.flatten_nil]
    exact ⟨rfl, fun _ _ => rfl, fun i => i.elim0, fun _ _ => rfl, fun _ _ => rfl,
      id, fun _ => rfl, fun _ _ _ => rfl, fun i _ => ((s.scene.cell i).pull_id).symm⟩
  | succ n ih =>
    let B := C 0
    let R := Fin.tail C
    obtain ⟨p, γ, hp, eq⟩ := B.runs B.ref β s src dst (hin 0) hl hv hr hc
    have hs : Separate R :=
      ⟨fun i j hn => h.vertex _ _ (Fin.succ_injective _ |>.ne hn),
        fun i j hn => h.edge _ _ (Fin.succ_injective _ |>.ne hn)⟩
    have he (j : B.action.I) (i : Fin n) : Matches (R i).ref (γ j) (p j) (R i).input := by
      have out := (hp j).1.outside.rekey (B.shared.trans (R i).shared.symm)
      apply (hin i.succ).outside out
      · exact fun v => Set.disjoint_left.mp (h.vertex i.succ 0 (Fin.succ_ne_zero _)) ⟨v, rfl⟩
      · exact fun e => Set.disjoint_left.mp (h.edge i.succ 0 (Fin.succ_ne_zero _)) ⟨e, rfl⟩
    have run (j : B.action.I) :=
      ih R hs (p j) (γ j) (he j) (layout_of_reach (hp j).1.reach hl) (hp j).1.valid
        (fun y hy => hr y ((hp j).1.reach.trans hy)) (hp j).2.1
    choose q δ hq hval using run
    refine ⟨fun a => q (a 0) (Fin.tail a), fun a => δ (a 0) (Fin.tail a), ?_, ?_⟩
    · intro a
      obtain ⟨h₁, _, pending₁⟩ := hp (a 0)
      have h₂ := hq (a 0) (Fin.tail a)
      refine ⟨⟨_, _, h₁, h₂.history⟩, h₁.reach.trans h₂.reach, h₂.valid, h₂.calm, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨hx, hrest⟩ := h₂.pending hx
        obtain ⟨hx, hhead⟩ := pending₁ hx
        refine ⟨hx, ?_⟩
        rintro ⟨i, rfl⟩
        induction i using Fin.cases with
        | zero => exact hhead rfl
        | succ i => exact hrest ⟨i, rfl⟩
      · have a₁ := h₁.outside.mono (B' := vertices C) (A' := edges C)
          (fun _ h => ⟨0, h⟩) (fun _ h => ⟨0, h⟩)
        rw [B.shared] at a₁
        have a₂ := h₂.outside.mono (B' := vertices C) (A' := edges C)
          (fun _ ⟨i, h⟩ => ⟨i.succ, h⟩) (fun _ ⟨i, h⟩ => ⟨i.succ, h⟩)
        rw [fresh, List.ofFn_succ, List.flatten_cons]
        exact a₁.trans a₂
      · intro i
        induction i using Fin.cases with
        | zero =>
          have out := h₂.outside.rekey B.shared.symm
          apply h₁.match'.outside out
          · rintro v ⟨i, hi⟩
            exact Set.disjoint_left.mp (h.vertex i.succ 0 (Fin.succ_ne_zero _)) hi ⟨v, rfl⟩
          · rintro e ⟨i, hi⟩
            exact Set.disjoint_left.mp (h.edge i.succ 0 (Fin.succ_ne_zero _)) hi ⟨e, rfl⟩
        | succ i => exact h₂.result i
    · intro x
      rw [eq x, ← (Fin.consEquiv (fun i => (C i).action.I)).sum_comp, Fintype.sum_prod_type]
      apply sum_congr rfl
      intro j _
      rw [hval, mul_sum]
      apply sum_congr rfl
      intro l _
      simp only [show Fin.consEquiv (fun i => (C i).action.I) (j, l) = Fin.cons j l from rfl,
        Fin.prod_univ_succ, mul_assoc]
      rfl

end Wave
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

section
/-!
# A key stays local in a wave

Every ordinary key seen after a wave was either already present
within the same region or created there. New addresses in each
script correspond to a consecutive interval in the global stack.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open scoped Classical
variable {F T V E X K N J L : Type} [Field F] {r t P g H U M D n : ℕ}
  {key : V → X → ℕ} {β γ : V ⊕ ℕ → K}
  {s q : Stage F r t T V E X} {R : Reference J L N V E T X} {a : Record F r t J L K N}
  {f : List (K × ℕ)} {B : Set V} {A : Set E}

def Known (s : Stage F r t T V E X) := ∀ v j, j ∈ s.footprint v → available s.hidden.length j

private theorem Update.known (h : Update P g H U R β γ s q a f) (hs : Known s) : Known q := by
  intro v j hj
  by_cases hv : v ∈ Set.range R.vertex
  · obtain ⟨i, rfl⟩ := hv
    exact h.match'.known i j hj
  · exact h.outside.known j (hs v j (by rwa [h.outside.footprint v hv] at hj))

/-- The energy stored at a natural-number key. -/
def degree (ns : List ℕ) : V ⊕ ℕ → ℕ
  | .inl _ => 0
  | .inr i => (ns.reverse[i]?).getD 0

omit [Field F] in
theorem Outside.degree_old (h : Outside B A key s q β γ f) {j : V ⊕ ℕ}
    (hj : available s.hidden.length j) : degree q.hidden j = degree s.hidden j := by
  cases j with
  | inl => rfl
  | inr i =>
    change i < s.hidden.length at hj
    simp only [degree, h.history, List.reverse_append, List.reverse_reverse]
    rw [List.getElem?_append_left (by simpa using hj)]

omit [Field F] in
private theorem Outside.degree_new (h : Outside B A key s q β γ f) (i : Fin f.length) :
    degree q.hidden (.inr (s.hidden.length + i.val) : V ⊕ ℕ) = (f.get i).2 := by
  simp only [degree, h.history, List.reverse_append, List.reverse_reverse]
  rw [List.getElem?_append_right (by simp)]
  simp

private theorem Update.fresh {j : V ⊕ ℕ} (h : Update P g H U R β γ s q a f)
    (hold : ¬ available s.hidden.length j) (hnew : available q.hidden.length j) :
    ∃ i : Fin f.length, j = .inr (s.hidden.length + i.val) ∧
      (γ j, degree q.hidden j) = f.get i := by
  cases j with
  | inl => exact (hold trivial).elim
  | inr j =>
    simp only [available, h.outside.length] at hold hnew
    let i : Fin f.length := ⟨j - s.hidden.length, by omega⟩
    have hi : j = s.hidden.length + i.val := by dsimp [i]; omega
    refine ⟨i, congrArg _ hi, ?_⟩
    rw [hi, h.outside.new, h.outside.degree_new]

namespace Wave

variable {C : Fin n → Command F r t T V E X K N P g H U M D key} {a : Index C}

def Together (C : Fin n → Command F r t T V E X K N P g H U M D key) (v w : V) :=
  v = w ∨ ∃ i, v ∈ Set.range (C i).ref.vertex ∧ w ∈ Set.range (C i).ref.vertex

/-- Each key present in a region has an old origin in that same region
or a fresh origin in the script for it. The offset is common to all
keys introduced by any one script. -/
def Origins (C : Fin n → Command F r t T V E X K N P g H U M D key) (a : Index C)
    (s q : Stage F r t T V E X) (β γ : V ⊕ ℕ → K) : Prop :=
  ∃ offset : Fin n → ℕ, ∀ v j, j ∈ q.footprint v →
    (∃ w, Together C v w ∧ j ∈ s.footprint w ∧ γ j = β j ∧ degree q.hidden j = degree s.hidden j) ∨
    ∃ i, v ∈ Set.range (C i).ref.vertex ∧ ∃ k : Fin ((C i).action.fresh (a i)).length,
      j = .inr (offset i + k.val) ∧ (γ j, degree q.hidden j) = ((C i).action.fresh (a i)).get k

theorem Execution.origins {keys : V → X → X → Prop} {ext : T → X → X → Prop}
    (h : Execution C a s q β γ) (sep : Separate C) (ctrl : s.Controls keys ext)
    (known : Known s) : Origins C a s q β γ := by
  induction n generalizing s β with
  | zero =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Fin.elim0, fun v j hj => .inl ⟨v, .inl rfl, hj, rfl, rfl⟩⟩
  | succ n ih =>
    obtain ⟨p, δ, head, tail⟩ := h
    have sep' : Separate (Fin.tail C) :=
      ⟨fun i j hn => sep.vertex _ _ ((Fin.succ_injective _).ne hn),
        fun i j hn => sep.edge _ _ ((Fin.succ_injective _).ne hn)⟩
    obtain ⟨offset, h₁⟩ := ih tail sep' (head.reach.controls ctrl) (head.known known)
    refine ⟨Fin.cons s.hidden.length offset, fun v j hj => ?_⟩
    rcases h₁ v j hj with ⟨w, hvw, hw, hγ, he⟩|⟨i, hv, k, hj, hγ⟩
    · rcases hvw with rfl|⟨i, hv, hw'⟩
      · rcases head.outside.origin head.reach ctrl known hw with ⟨w, hv, hj⟩|⟨hv, hj⟩
        · have ho := known w _ hj
          refine .inl ⟨w, ?_, hj, hγ.trans (head.outside.old _ ho), he.trans (head.outside.degree_old ho)⟩
          exact hv.imp_right (fun h => ⟨0, h⟩)
        · obtain ⟨k, hk, heq⟩ := head.fresh hj (head.known known _ _ hw)
          refine .inr ⟨0, hv, k, ?_, ?_⟩
          · simpa only [Fin.cons_zero] using hk
          · rw [hγ, he]; exact heq
      · have out := Set.disjoint_left.mp (sep.vertex i.succ 0 (Fin.succ_ne_zero i)) hw'
        rw [head.outside.footprint w out] at hw
        have ho := known w _ hw
        exact .inl ⟨w, .inr ⟨i.succ, hv, hw'⟩, hw, hγ.trans (head.outside.old _ ho),
          he.trans (head.outside.degree_old ho)⟩
    · exact .inr ⟨i.succ, hv, k, by simpa only [Fin.cons_succ] using hj, hγ⟩

end Wave
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end
