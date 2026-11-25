import OAI.LinearAlgebra.MatrixExponent.Protocol.Alignment
import OAI.LinearAlgebra.MatrixExponent.Transport.System

/-!
# Wiring a local board expansion into transport banks

The branch selector and every enabled endpoint are embedded injectively.
Invalid codes and nonzero padding must have zero weight. This makes
the two changes of summation indices exact over any field.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Transport Classical

variable {F E : Type} [Field F] {h p W z : ℕ}

abbrev End (m : E → ℕ) := Σ _ : (Σ e, Fin (m e)), Bool

abbrev Links (F : Type) [Field F] [Fintype E] (src dst : E → Site h) (m : E → ℕ) :=
  Board.orders (fun e => Board.link F (src e) (dst e)) m

abbrev Demand (F : Type) [Field F] (σ : Coloring.B h → Coloring.B h) (W : ℕ) :=
  Links F id (Routing.inflate h σ) (fun _ => W)

def opposite {m : E → ℕ} (i : End m) : End m := ⟨i.1, !i.2⟩

structure Placement (src dst : E → Site h) (m : E → ℕ)
    (g : Port h p → ℕ) (a : Orders h p) where
  embed : End m ↪ Port h p
  owner : ∀ i, (embed i).1 = if i.2 then dst i.1.1 else src i.1.1
  cmd : ∀ i, a (embed i) = (true, i.2, embed (opposite i))
  cover : ∀ i ∈ Enabled a, ∃ j, embed j = i
  group : ∀ i, g (embed (opposite i)) = g (embed i)

def Padded (a : Orders h p) (c : Site h → Channels p (2 ^ z)) : Prop :=
  ∀ i ∉ Enabled a, ∀ t, c i.1 (i.2, t) = false

def outside (σ : Coloring.B h → Coloring.B h) (W : ℕ) (x y : Site h → Data W (2 ^ z)) :
    Lines z (End (fun _ : Site h => W)) :=
  fun i t => if i.2 then y (Routing.inflate h σ i.1.1) (i.1.2, t) else x i.1.1 (i.1.2, t)

def Placement.inside {src dst : E → Site h} {m : E → ℕ} {g : Port h p → ℕ} {a : Orders h p}
    (P : Placement src dst m g a) (c : Site h → Channels p (2 ^ z)) : Lines z (End m) :=
  fun i t => c (P.embed i).1 ((P.embed i).2, t)

structure Wiring (S : System F h p W (2 ^ z)) (C : ℕ) (σ : Equiv.Perm (Coloring.B h)) where
  E : Type
  I : Type
  [finiteE : Fintype E]
  [finiteI : Fintype I]
  src : E → Site h
  dst : E → Site h
  m : I → E → ℕ
  proc : (Demand F σ W).Expansion (fun j => Links F src dst (m j))
  choose : I ↪ S.selector.obj
  place : ∀ j, Placement src dst (m j) S.group (commands (S.dispatch (σ, choose j)))
  cost : ∀ j, 2 * (∑ e, m j e) ≤ C * W * 2 ^ h
  agrees : ∀ j x y c, Padded (commands (S.dispatch (σ, choose j))) c → ∀ i,
    S.kernel ((S.dispatch (σ, choose j)) i).1 (x i) (y i) (c i) =
      proc.kernel j i z ((Demand F σ W).view i (outside σ W x y))
        ((Links F src dst (m j)).view i ((place j).inside c))
  invalid : ∀ t x y c, S.value (S.dispatch (σ, t)) x y c ≠ 0 →
    (∃ j, choose j = t) ∧ Padded (commands (S.dispatch (σ, t))) c

attribute [instance] Wiring.finiteE Wiring.finiteI

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Summing over padded banks and selectors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Classical Transport

variable {F E : Type} [Field F] {h p z W C : ℕ} {src dst : E → Site h} {m : E → ℕ}
variable {g : Port h p → ℕ} {a : Orders h p}

private theorem sum_embed {I J : Type} [Fintype I] [Fintype J] (e : I ↪ J) (f : J → F)
    (he : ∀ j, f j ≠ 0 → ∃ i, e i = j) : ∑ j, f j = ∑ i, f (e i) := by
  rw [← Finset.sum_map]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ?_)
  by_contra h
  obtain ⟨i, rfl⟩ := he j h
  exact hj (Finset.mem_map_of_mem _ (Finset.mem_univ _))

private theorem links_eval [Fintype E] (x : Lines z (End m)) :
    (Links F src dst m).eval z x =
      if ∀ j, x ⟨j, false⟩ = x ⟨j, true⟩ then 1 else 0 := by
  change (∏ t, ∏ j : Σ e, Fin (m e), if x ⟨j, false⟩ t = x ⟨j, true⟩ t then 1 else 0) = _
  simp only [Finset.prod_boole, Finset.mem_univ, forall_const]
  congr 1
  exact propext ⟨fun e j => funext (fun t => e t j), fun e t j => congrFun (e j) t⟩

private theorem demand_eval (σ : Coloring.B h → Coloring.B h) (x y : Site h → Data W (2 ^ z)) :
    (Demand F σ W).eval z (outside σ W x y) =
      if ∀ i, x i = y (Routing.inflate h σ i) then 1 else 0 := by
  rw [links_eval]
  congr 1
  apply propext
  constructor
  · intro he i
    funext ⟨j, t⟩
    exact congrFun (he ⟨i, j⟩) t
  · intro he j
    funext t
    exact congrFun (he j.1) (j.2, t)

namespace Placement

variable (P : Placement src dst m g a)

private theorem enabled (i : End m) : P.embed i ∈ Enabled a := by simp [Enabled, P.cmd]

theorem valid (P : Placement src dst m g a) : Valid g a := by
  intro j hj
  obtain ⟨i, rfl⟩ := P.cover j hj
  have he : opposite (opposite i) = i := by rcases i with ⟨k, b⟩; simp [opposite]
  simp only [P.cmd, he]
  exact ⟨P.enabled _, trivial, rfl, P.group i⟩

theorem count [Fintype E] (P : Placement src dst m g a) :
    (Enabled a).card = 2 * (∑ e, m e) := by
  have he : Enabled a = Finset.univ.map P.embed := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨P.cover i, by rintro ⟨k, rfl⟩; exact P.enabled k⟩
  rw [he, Finset.card_map, Finset.card_univ]
  simp [End, Fintype.card_sigma, mul_comm]

private theorem agrees [Fintype E] (c : Site h → Channels p (2 ^ z)) :
    (Links F src dst m).eval z (P.inside c) = if Joins a c then 1 else 0 := by
  rw [links_eval]
  congr 1
  apply propext
  constructor
  · intro he j hj
    obtain ⟨⟨k, b⟩, rfl⟩ := P.cover j hj
    rw [P.cmd]
    cases b
    · exact congrFun (he k)
    · exact congrFun (he k).symm
  · intro he j
    have h := he _ (P.enabled ⟨j, false⟩)
    rw [P.cmd] at h
    exact funext h

private def fill (u : Lines z (End m)) : Site h → Channels p (2 ^ z) :=
  fun i ⟨k, t⟩ => if hi : (i, k) ∈ Enabled a then u (P.cover _ hi).choose t else false

private theorem fill_padded (u : Lines z (End m)) : Padded a (P.fill u) := by
  rintro ⟨i, k⟩ hi t
  simp [fill, hi]

private theorem inside_fill : Function.LeftInverse (P.inside (z := z)) P.fill := by
  intro u
  funext i t
  have hi := P.enabled i
  simp only [inside, fill, Prod.mk.eta, dite_eq_left hi]
  rw [P.embed.injective (P.cover _ hi).choose_spec]

private theorem fill_inside (c : Site h → Channels p (2 ^ z)) (hc : Padded a c) :
    P.fill (P.inside c) = c := by
  funext i ⟨k, t⟩
  unfold fill
  dsimp only
  split
  · rename_i hi
    unfold inside
    rw [(P.cover _ hi).choose_spec]
  · rename_i hi
    exact (hc (i, k) hi t).symm

end Placement

variable {S : System F h p W (2 ^ z)} {σ : Equiv.Perm (Coloring.B h)}

private theorem Wiring.term (q : Wiring S C σ) (j : q.I) (x y : Site h → Data W (2 ^ z)) :
    let v := S.dispatch (σ, q.choose j)
    let V := Links F q.src q.dst (q.m j)
    (∑ c : Site h → Channels p (2 ^ z), S.value v x y c * (if Joins (commands v) c then 1 else 0)) =
      ∑ u, Board.Kernel.prod (Demand F σ W) V (q.proc.kernel j) z (outside σ W x y) u * V.eval z u := by
  let P := q.place j
  let e : Lines z (Links F q.src q.dst (q.m j)).slot ↪ (Site h → Channels p (2 ^ z)) :=
    ⟨P.fill, P.inside_fill.injective⟩
  dsimp only
  rw [sum_embed e]
  · apply Finset.sum_congr rfl
    intro u _
    have hp := P.fill_padded (z := z) u
    change S.value _ x y (P.fill u) * (if Joins _ (P.fill u) then 1 else 0) = _
    rw [← P.agrees (F := F), P.inside_fill u]
    congr 1
    unfold System.value Board.Kernel.prod
    apply Finset.prod_congr rfl
    intro i _
    rw [q.agrees j x y _ hp, P.inside_fill u]
  · intro c hc
    have hp := (q.invalid (q.choose j) x y c (left_ne_zero_of_mul hc)).2
    exact ⟨P.inside c, P.fill_inside c hp⟩

theorem system_correct (hw : ∀ σ, Nonempty (Wiring S C σ)) : S.Correct C := by
  intro σ x y
  obtain ⟨q⟩ := hw σ
  constructor
  · intro t c _ hn
    obtain ⟨⟨j, rfl⟩, _⟩ := q.invalid t x y c hn
    exact ⟨(q.place j).valid, (q.place j).count.le.trans (q.cost j)⟩
  let e := q.choose.trans S.selector.code.toEmbedding
  rw [← demand_eval (F := F) σ x y, q.proc.identity z (outside σ W x y)]
  symm
  rw [sum_embed e]
  · apply Finset.sum_congr rfl
    intro j _
    change (∑ c : Site h → Channels p (2 ^ z),
      let v := S.dispatch (σ, S.selector.code.symm (S.selector.code (q.choose j)))
      S.value v x y c * (if Joins (commands v) c then 1 else 0)) = _
    rw [Equiv.symm_apply_apply]
    exact q.term j x y
  · intro t ht
    obtain ⟨c, _, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
    obtain ⟨⟨j, hj⟩, _⟩ := q.invalid _ x y c (left_ne_zero_of_mul hc)
    exact ⟨j, S.selector.code.eq_symm_apply.mp hj⟩

end OAI.LinearAlgebra.MatrixExponent.Protocol
end
