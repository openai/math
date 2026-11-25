import OAI.Geometry.Hirsch.Tuning

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Stage

open Coins

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {raw fresh : coin.Raw I} {n : ℕ} {w : Board I n} {tag : Stamp Bit I} {k : ℕ} {u : Dials}
  {rule : Rules raw} {old mid q : w.Round} {d : Bool}
  (G : Stage tag u k rule old d) (v : u.Valid) (hk : k < u.h)

def scale (i : I) : u.Scale := (G.ledger v hk (w.place i / u.a^(k+1))).colors u.a u.h u.theta i
def band (mid : w.Round) (i : I) := (G.ledger v hk (w.place i / u.a^(k+1))).band mid i
def pick (mid : w.Round) (i : I) : u.Bin := bucket u.t u.J (raw.pins.mass (G.band v hk mid i))

theorem band_eq {i : I} {j : ℕ} (hi : w.place i ∈ piece (u.a^(k+1)) j) :
    G.band v hk mid i = (G.ledger v hk j).band mid i := by
  change w.place i / u.a^(k+1) = j at hi
  subst j; rfl

theorem key_le (j : ℕ) : (G.ledger v hk j).key ≤ u.key :=
  mul_le_mul_of_nonneg_left (G.rate.le.trans (v.rate_le k)) (by linarith [v.link])

theorem beta_le (j : ℕ) : (G.ledger v hk j).beta ≤ u.beta :=
  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add_left (G.key_le v hk j) _) (by positivity))
    (mul_nonneg (by norm_num) v.mass)

theorem rare (hn : n ≤ u.a^u.h) (hm : mid.Finer old) {c : u.Scale}
    (hl : mid.Links d (fun i => G.scale v hk i = c)) (j : ℕ) (i : I)
    (hi : w.place i ∈ piece (u.a^(k+1)) j) (he : w.Shore d i) :
    raw.pins.mass (((G.ledger v hk j).book mid i (flat (u.D k).limit)).filter
      (fun s => mid.Straddles d s (piece (u.a^(k+1)) j) i)) ≤ u.err := by
  let L := G.ledger v hk j
  have suff : ∀ i, G.scale v hk i = c → w.place i ∈ piece (u.a^(k+1)) j → L.colors u.a u.h u.theta i = c := by
    intro x h hx
    change w.place x / u.a^(k+1) = j at hx
    exact (congrArg (fun z => (G.ledger v hk z).colors u.a u.h u.theta x) hx.symm).trans h
  apply L.straddlers hm (by have := v.base; omega) hn v.scale
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (G.beta_le v hk j) (by norm_num)) v.compare)
    ((add_le_add_left (G.key_le v hk j) _).trans v.discard) (color := c) ?_ hi he
  refine ⟨fun i h => suff _ (hl.east i h),fun i h => ?_⟩
  obtain ⟨y,hy,hm,hv,hh⟩ := hl.west i h
  exact ⟨y,hy,hm,hv,suff _ hh⟩

variable (foil : ∀ j : Fin u.J, Foil coin tag (k+1) raw.pins.rate u.L (price u.t j))

def bars (mid : w.Round) (i : I) : Finset Bit :=
  match G.pick v hk mid i with
  | none => ∅
  | some j => (foil j).bits (G.band v hk mid i)

theorem support (mid : w.Round) (i : I) (b : Bit) (h : b ∈ G.bars v hk foil mid i) :
    ¬tag.pin b ∧ b ∈ tag.scope w (k+1) (u.a^(k+1)) i := by
  unfold bars at h
  split at h
  · simp at h
  · rename_i j _
    let L := G.ledger v hk (w.place i / u.a^(k+1))
    exact (foil j).visible _ i (fun _ hs => L.support rfl (L.band_sub hs)) b h

theorem barrier_bound (mid : w.Round) (i : I) :
    Real.exp (-8*u.L) ≤ coin.weight (G.bars v hk foil mid i) := by
  unfold bars
  split
  · simp [Coins.weight,v.lambda]
  · rename_i j h
    exact (foil j).low _ (bucket_high h).2.le

variable (hf : tag.Fresh fresh k)

def advance (mid : w.Round) := hf.advance G.view (G.bars v hk foil mid) (G.support v hk foil mid)

theorem visible_next (mid : w.Round) : tag.Visible w (G.advance v hk foil hf mid) (k+1) (u.a^(k+1)) :=
  hf.visible G.view _ _

theorem reliable_next (mid : w.Round) :
    (G.advance v hk foil hf mid).Reliable w.place u.K (u.margin (k+1)) (u.cost (k+1)) := by
  rw [Dials.margin,pow_succ (Real.exp _)]
  exact hf.reliable G.view _ _ (Real.exp_pos _) (by simp [v.lambda]) (G.barrier_bound v hk foil mid) (G.checked v)

variable (hide s : Finset I) (hs : s ⊆ hide)

def draw := hf.draw G.view (G.gate v hk.le) rfl hide s hs

theorem thin (x : Table Bit) : (G.advance v hk foil hf mid).watch hide s x ⊆ (G.draw v hk hf hide s hs).thin x :=
  fun g hg => (hf.watched G.view _ rfl hide s hs _ _ x g hg).1

theorem switched (hn : n ≤ u.a^u.h) (hm : mid.Finer old) (hq : q.Finer mid) {c : u.Scale}
    (hl : mid.Links d (fun i => G.scale v hk i = c)) {bin : Fin u.J}
    (hl' : q.Links d (fun i => G.pick v hk mid i = some bin)) (j : ℕ) :
    (G.ledger v hk j).Switched (G.draw v hk hf hide s hs) mid q (fun i => G.pick v hk mid i = some bin)
      ((G.advance v hk foil hf mid).watch hide s) (price u.t bin) u.err (Real.exp (-u.L)) u.U := by
  have hlow := price_low v.tpos bin.val
  have ht := v.tpos
  have key : 0 ≤ u.key := (G.ledger v hk j).positive.2.1.trans (G.key_le v hk j)
  refine ⟨hm,hq,hl',G.thin v hk foil hf hide s hs,G.crude v hide s hs j,G.rare v hk hn hm hl j,
    ?_,(foil bin).positive,?_,?_,(Real.exp_pos _).le,?_⟩
  · intro i hi hp
    rw [← G.band_eq v hk hi]
    exact (bucket_high hp).1
  · change u.err + u.loss ≤ _
    linarith [v.err_pos,v.discard,v.rare]
  · nlinarith [G.beta_le v hk j,v.compare,v.err_pos,v.rare,v.scale]
  intro B hB
  refine ⟨_,(foil bin).high B hB,?_,fun g hh R =>
    (foil bin).independent B (G.visible_next v hk foil hf mid) hide s q _ d R g hh⟩
  intro g hg hp hsub x hx
  have hh := (hf.watched G.view (G.gate v hk.le) rfl hide s hs _ _ x g hx).2
  change All (G.bars v hk foil mid g) x at hh
  rw [bars,hp,G.band_eq v hk hg] at hh
  exact fun b hb => hh _ (Finset.image_mono _ hsub hb)

end OAI.Geometry.Hirsch.Layer.Board.Stage
