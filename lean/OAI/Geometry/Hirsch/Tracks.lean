import OAI.Geometry.Hirsch.LocalBooks

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

variable {u : Dials} {I : Type} [Fintype I] {Q Q' : Network u I} {e : Equiv.Perm I}
  {p R k : ℕ} {v : u.Valid} {c : u.History k}

def reach (u : Dials) (k : ℕ) := Matches.span u (u.D k)

def radius (u : Dials) : ℕ → ℕ
  | 0 => 1
  | k+1 => radius u k + reach u k + reach u k + 2 + reach u k + 2

theorem radius_mono (u : Dials) : Monotone (radius u) := by
  apply monotone_nat_of_le_succ
  intro k; rw [radius]; omega

def checkRadius (u : Dials) (k : ℕ) := radius u k + reach u k
def midRadius (u : Dials) (k : ℕ) := checkRadius u k + reach u k + 2

structure Tracks (e : Equiv.Perm I) (p : ℕ) (g : Q.Process v k c) (g' : Q'.Process v k c) : Prop where
  pins : g.raw.pins.Equivariant g'.raw.pins e (u.tables e)
  round : Q.Matches Q' e p (radius u k) g.round g'.round
  pass : Q.Related Q' e p (radius u k) (u.tables e) g.rule.pass g'.rule.pass

namespace Tracks

variable {g : Q.Process v k c} {g' : Q'.Process v k c} (h : Tracks e p g g') {i : I}

include h in
theorem checked : Q.Related Q' e p (checkRadius u k) (u.tables e) g.checked.pass g'.checked.pass := by
  intro i hi x
  have hD := (u.D k).order
  have cost := Matches.bound u (D := u.D k) (show flat (u.D k).step ≤ flat (u.D k).max from
    fun _ => show (u.D k).step ≤ (u.D k).max by have := (u.D k).order; unfold Depths.near at *; omega)
  have hh := hi.cut (show radius u k + 1 + total u (flat (u.D k).step) ≤ checkRadius u k by
    unfold checkRadius reach; omega)
  have eq := (hh.cut (show radius u k + 1 ≤ _ by omega)).place
  let d := u.east k c
  have bad : ∀ x, Stage.bad u k g.rule g.round d i x ↔ Stage.bad u k g'.rule g'.round d (e i) (u.tables e x) := by
    intro x
    simp only [Stage.bad,Stamp.bad,Round.Cover,home,← eq]
    apply h.round.covers (Nat.le_succ _) hh
    intro j hj
    simp only [Coins.Rules.watch,Coins.Raw.force_empty,Finset.mem_sdiff,Stamp.hidden,
      Finset.mem_filter,Finset.mem_univ,true_and,hj.place,eq,h.pass _ (hj.cut (Nat.le_succ _)) x]
  have base := h.pass i (hh.cut (by omega)) x
  have hs := h.pins.screen u.tests bad x
  simp only [Process.checked,Stage.screened,Coins.Rules.mem,Coins.Rules.screen,← and_assoc] at *
  exact and_congr base hs

variable (hk : k < u.h) (s : u.Scale) (b : u.Bin)

include h in
theorem scale (hi : Q.Agree Q' e p (checkRadius u k + reach u k) i) :
    g.stage.scale v hk i = g'.stage.scale v hk (e i) := by
  have eq := (hi.cut (show 1 ≤ _ by unfold reach Matches.span; omega)).place
  let j := Q.w.place i / u.a^(k+1)
  let L := g.stage.ledger v hk j
  let L' := g'.stage.ledger v hk j
  have hr := h.round.up (show radius u k ≤ checkRadius u k by unfold checkRadius; omega)
  have hh : ∀ z, e.finsetCongr.finsetCongr (L.close i z) = L'.close (e i) z :=
    fun z => Matches.close h.checked L L' hr hi z
  have hs : L.colors u.a u.h u.theta i = L'.colors u.a u.h u.theta (e i) := by
    funext t
    simp only [Ledger.colors,h.pins.mass,hh]
  exact hs.trans (congrArg (fun a => (g'.stage.ledger v hk (a/u.a^(k+1))).colors u.a u.h u.theta (e i)) eq)

include h in
theorem mid (hp : 2*k < p) :
    Q.Matches Q' e p (midRadius u k) (g.mid hk s) (g'.mid hk s) := by
  apply h.round.refine (a := u.ticket hk c s none) hp (S := checkRadius u k + reach u k)
  · intro i hi; rw [h.scale hk hi]
  · unfold checkRadius; omega

include h in
theorem band (hp : 2*k < p) (hi : Q.Agree Q' e p (midRadius u k + reach u k) i) :
    e.finsetCongr.finsetCongr (g.stage.band v hk (g.mid hk s) i) = g'.stage.band v hk (g'.mid hk s) (e i) := by
  have eq := (hi.cut (show 1 ≤ _ by unfold midRadius; omega)).place
  let j := Q.w.place i / u.a^(k+1)
  have h₁ : Q.w.place i ∈ piece (u.a^(k+1)) j := rfl
  have h₂ : Q'.w.place (e i) ∈ piece (u.a^(k+1)) j := eq ▸ h₁
  rw [g.stage.band_eq v hk h₁,g'.stage.band_eq v hk h₂]
  apply (h.mid hk s hp).band (h.checked.up (by unfold midRadius; omega)) _ _ hi

include h in
theorem pick (hp : 2*k < p) (hi : Q.Agree Q' e p (midRadius u k + reach u k) i) :
    g.stage.pick v hk (g.mid hk s) i = g'.stage.pick v hk (g'.mid hk s) (e i) := by
  unfold Stage.pick
  rw [h.pins.mass,h.band hk s hp hi]

include h in
theorem last (hp : 2*k+1 < p) :
    Q.Matches Q' e p (radius u (k+1)) (g.last hk s b) (g'.last hk s b) := by
  apply (h.mid hk s (by omega)).refine (a := u.ticket hk c s (some b)) hp (S := midRadius u k + reach u k)
  · intro i hi; rw [h.pick hk s (by omega) hi]
  · omega

include h in
theorem bars (hp : 2*k < p) (hi : Q.Agree Q' e p (midRadius u k + reach u k) i) (x : Table (u.Cell I)) :
    Coins.All (g.stage.bars v hk (v.foil hk g.stage.rate) (g.mid hk s) i) x ↔
    Coins.All (g'.stage.bars v hk (v.foil hk g'.stage.rate) (g'.mid hk s) (e i)) (u.tables e x) := by
  unfold Stage.bars
  rw [h.pick hk s hp hi,← h.band hk s hp hi]
  split
  · simp [Coins.All]
  · rename_i j hj
    simp only [Coins.All,Foil.bits,Finset.forall_mem_image,Equiv.finsetCongr_apply,Finset.forall_mem_map]
    apply forall_congr'; intro a
    apply imp_congr_right; intro _
    exact iff_of_eq (congrArg (· = true) (u.tables_apply e x (⟨k+1,by omega⟩,.inr (j,a))).symm)

include h in
theorem succ (hp : 2*k+1 < p) : Tracks e p (g.succ hk s b) (g'.succ hk s b) := by
  have atom := v.atom_same e (⟨k+1,by omega⟩ : Fin (u.h+1))
  refine ⟨⟨(g.succ hk s b).stage.rate.trans (g'.succ hk s b).stage.rate.symm,v.invariant e,?_⟩,
    h.last hk s b hp,?_⟩
  · intro i x
    simp only [Process.succ,Coins.Raw.join_success,Finset.mem_inter]
    exact and_congr (h.pins.success _ _) (atom _ _)
  intro i hi x
  have hh := hi.cut (show midRadius u k + reach u k ≤ radius u (k+1) by
    unfold midRadius checkRadius; rw [radius]; omega)
  have hg := h.checked i (hh.cut (by unfold midRadius; omega)) x
  have hb := h.bars hk s (by omega) hh x
  simp only [Process.succ,Stage.advance,Stamp.Fresh.advance,Coins.Rules.next_pass]
  exact and_congr hg (and_congr (atom i x) hb)

end Tracks
end OAI.Geometry.Hirsch.Layer.Board.Network
