import OAI.Geometry.Hirsch.Footprint

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Forest

variable {client : Program} {A : Type} [Nonempty A] {B V h H N : ℕ}
  (tree : Forest client.Coord (Upgrade V A) (h + 2*H))

abbrev device {Row : Type} [Fintype Row] (block : Blocking (Port client.Coord B V) Row) : Package where
  prog := (tree.compiled B).program
  Row := Row
  block := block

structure Modules (ep : Episodes N) (B overhead : ℕ) where
  Row : Type
  [finiteRow : Fintype Row]
  block : Blocking (Port client.Coord B V) Row
  paint : Coloring (tree.device block) client B
  time : Fin N → Fin B → ℝ
  interior : ∀ idx b, time idx b ∈ Ioo (ep.left idx) (ep.right idx)
  eps : ℝ
  positive : 0 < eps
  probe : ∀ delta : Row → ℝ, (∀ row, 0 ≤ delta row ∧ delta row < eps) →
    ∀ idx b usable,
      let sys := block.restriction usable ((block.slice (time idx b)).rhs + paint.vary true delta)
      ∀ pt ∈ sys.body.extremePoints ℝ,
        tree.physical.Descent usable b (paint.represented b (Subtype.val '' sys.active pt))
  anchor : ∀ idx pt, pt = ep.left idx ∨ pt = ep.right idx →
    paint.Anchor pt (2 * eps) (2 * V * Fintype.card client.Coord)
  groupBound : ∀ b i, (paint.group b i).ncard ≤ 2 * V
  red : ∀ b i row, row ∈ paint.group b i → tree.physical.Footprint b b i 3 (block.support row)
  support : ∀ row, ∃ b d i, tree.physical.Footprint b d i (6*V) (block.support row)
  rows : Fintype.card Row ≤ overhead * N * (B * Fintype.card client.Coord)^3

attribute [instance] Modules.finiteRow

theorem schedules [Nonempty (Upgrade V A)] {overhead : ℕ} (ho : 4*V ≤ overhead)
    (supply : ∀ (prog : Program) (tree : Forest prog.Coord (Upgrade V A) (h+2*H)),
      0 < Fintype.card prog.Coord → ∀ B, 0 < B → ∀ ep : Episodes N,
      Nonempty (tree.Modules ep B overhead)) :
    (bank A H).Schedules (bank (Upgrade V A) (h+2*H)) N V overhead (6*V + 2*(h+2*H+1)) := by
  rintro prog ⟨src,hv,ha⟩ hm B hb ep
  obtain ⟨mod⟩ := supply prog src hm B hb ep
  have he : prog.closure = src.program.closure := by
    funext s
    unfold Program.closure
    rw [ha]
  let samples : Samples prog ep B V := {
    pkg := src.device mod.block, paint := mod.paint, time := mod.time, interior := mod.interior,
    eps := mod.eps, positive := mod.positive, anchor := mod.anchor, groupBound := mod.groupBound,
    probe := by
      intro delta hd idx b usable hu sys pt hp
      rw [hv]
      exact src.compile_viable usable b _ hu (mod.probe delta hd idx b usable pt hp),
    spanBound := by
      intro b coords pick hp
      rw [he]
      exact src.compile_union b coords _ (fun i hi => mod.red b i _ (hp i hi)) }
  apply samples.schedule
  refine ⟨(src.compiled B).accepts,?_,mod.rows,?_⟩
  · change Fintype.card (Port prog.Coord B V) ≤ _
    simp only [Port,Position,Fintype.card_prod,Fintype.card_option,Fintype.card_fin,Fintype.card_bool]
    calc
      _ ≤ Fintype.card prog.Coord * ((2*B) * (2*V)) := by gcongr; omega
      _ = 4*V * (B * Fintype.card prog.Coord) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ ho
  · intro row
    obtain ⟨b,d,i,hf⟩ := mod.support row
    exact src.compile_span b d i hf

def ModuleTheorem : Prop :=
  ∀ rate : ℕ, ∃ L V overhead : ℕ, 2 ≤ L ∧ 0 < V ∧ (2*V)^rate ≤ L ∧ 4*V ≤ overhead ∧
    ∀ (h H : ℕ), 0 < h → ∀ (A : Type) [Nonempty A] (prog : Program)
      (tree : Forest prog.Coord (Upgrade V A) (h+2*H)), 0 < Fintype.card prog.Coord →
      ∀ B, 0 < B → ∀ ep : Episodes (L^h), Nonempty (tree.Modules ep B overhead)

end OAI.Geometry.Hirsch.Forest
