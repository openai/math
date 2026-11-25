import OAI.Computability.BorderVNP.CubeHostScatterCache
import OAI.Computability.BorderVNP.CubeCableHostScatterRun

/-! # Skipping empty, internal and nonowned cable intervals before the bit traversal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The two directory comparisons and the owner test precede the physical bit loop. -/
def visit (side : Bool) : Code := .seq readRow (.ifEq 15 0 .nop (.ifEq 31 32 .nop
  (.seq (readOwner side) (.ifEq 35 29 (.seq (cache side) scatterBits) .nop))))

/-- Constant upper bound for reading one endpoint, with no contribution from its bit span. -/
def visitOverhead (side : Bool) := readRow.slots+(readOwner side).slots+(cache side).slots+6

private theorem branch {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {a b : Code} {s : Bank w} {m : Memory w} {ticks : ℕ} {P : NatState → Prop} (x y : Reg)
    (h : BoundedRun pub macros (if s x = s y then a else b) s m ticks P) :
    BoundedRun pub macros (.ifEq x y a b) s m (1+ticks) P := by
  obtain ⟨es,t,mt,r,hc,hp⟩ := h
  exact ⟨_,t,mt,Runs.ifEq r, (show 1+traceCost es ≤ 1+ticks from Nat.add_le_add_left hc 1),hp⟩

private def Restored (l : Layout) (before mem : ℕ → ℕ) (i : ℕ) (side : Bool) (z : NatState) : Prop :=
  l.Ready z ∧ z.reg 13 = i ∧ z.mem = l.copyEnd before mem i side

private theorem inactive {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before mem : ℕ → ℕ) (i : ℕ) (side : Bool) (s : Bank w) (m : Memory w)
    (ready : l.Ready (.ofWords s m)) (idx : (s 13).val = i) (hm : readings m = mem)
    (hn : ¬l.Owned before i side) {ticks : ℕ} (room : 1 ≤ ticks) :
    BoundedRun pub macros .nop s m ticks (Restored l before mem i side) := by
  apply ((Code.nop).runFixed pub macros s m trivial).mono room
  rintro _ rfl
  refine ⟨ready,idx,?_⟩
  change readings m = _
  funext a
  simp [Layout.copyEnd,hn,hm]

private theorem owned_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before mem : ℕ → ℕ) (fit : l.Fits w before) {i : ℕ} (hi : i < l.count) (side : Bool)
    (s : Bank w) (m : Memory w) (owner : Owner l before i side (.ofWords s m))
    (hm : readings m = mem) (frozen : l.Frozen before mem) (yes : l.Owned before i side) :
    BoundedRun pub macros (.seq (cache side) scatterBits) s m
      ((cache side).slots+(2+l.bits before i side*(scatterStep.slots+1))) (Restored l before mem i side) := by
  have fr : l.Frozen before (readings m) := hm.symm ▸ frozen
  have c := run_cache pub macros l before fit hi side s m owner fr yes
  apply c.seq
  intro u mu hu
  let f := l.cached before i side
  have sep (j : ℕ) (hj : j < f.width) := fit.source_outside hi yes j hj
  have inner := run_scatterBits pub macros f (fit.cached hi yes) sep u mu hu.2.2.1
  apply inner.mono (by simp [Layout.bits,yes,f,Layout.cached])
  rintro z ⟨kept,_,hz⟩
  refine ⟨fun j hj => (kept j (by omega) (by intro e; subst j; norm_num at hj)).trans (hu.1 j hj),
    (kept 13 (by decide) (by decide)).trans hu.2.1,?_⟩
  have he : readings mu = mem := (show readings mu = readings m from hu.2.2.2).trans hm
  exact hz.trans ((congrArg (fun m' => f.image m' f.width) he).trans (frozen.image_eq hi yes))

/-- One physical endpoint requires bounded metadata time and one constant-cost bit copy per
owned bit. Internal cables, padding rows and foreign cells incur only metadata time. -/
theorem run_visit {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (before : ℕ → ℕ) (fit : l.Fits w before) {i : ℕ} (hi : i < l.count) (side : Bool)
    (s : Bank w) (m : Memory w) (ready : l.Ready (.ofWords s m)) (idx : (s 13).val = i)
    (frozen : l.Frozen before (readings m)) :
    BoundedRun pub macros (visit side) s m (visitOverhead side+l.bits before i side*(scatterStep.slots+1))
      (fun z => l.Ready z ∧ z.reg 13 = i ∧ z.mem = l.copyEnd before (readings m) i side) := by
  let P := Restored l before (readings m) i side
  let ticks := (cache side).slots+(2+l.bits before i side*(scatterStep.slots+1))
  let go := Code.seq (readOwner side) (.ifEq 35 29 (.seq (cache side) scatterBits) .nop)
  let live := Code.ifEq 31 32 .nop go
  let tail := Code.ifEq 15 0 .nop live
  have run := (run_readRow pub macros l before fit hi s m ready idx frozen).seq
    (b := tail) (t := 1+(1+((readOwner side).slots+(1+ticks)))) (Q := P) (fun u mu hh => by
      have h0 : (u 0).val = 0 := hh.1.ready 0 (by decide)
      have hmem : readings mu = readings m := hh.2
      have fr : l.Frozen before (readings mu) := hmem.symm ▸ frozen
      have width : (u 15).val = l.width before i := hh.1.fields.1
      have src : (u 31).val = l.cell before i false := hh.1.fields.2.1
      have dst : (u 32).val = l.cell before i true := hh.1.fields.2.2
      apply branch 15 0
      by_cases empty : l.width before i = 0
      · rw [ite_eq_left (Fin.ext (width.trans (empty.trans h0.symm)))]
        exact inactive pub macros l before (readings m) i side u mu hh.1.ready hh.1.index hmem
          (fun ho => ho.1 empty) (by omega)
      · rw [ite_eq_right (fun e => empty (width.symm.trans ((congrArg Fin.val e).trans h0)))]
        apply branch 31 32
        by_cases coloc : l.cell before i false = l.cell before i true
        · rw [ite_eq_left (Fin.ext (src.trans (coloc.trans dst.symm)))]
          exact inactive pub macros l before (readings m) i side u mu hh.1.ready hh.1.index hmem
            (fun ho => ho.2.1 coloc) (by omega)
        · rw [ite_eq_right (fun e => coloc (src.symm.trans ((congrArg Fin.val e).trans dst)))]
          apply (run_readOwner pub macros l before fit hi side u mu hh.1 fr empty coloc).seq
          intro v mv hv
          have hmem' : readings mv = readings m := (show readings mv = readings mu from hv.2).trans hmem
          have howner : (v 35).val = l.owner before i side := hv.1.owner
          have hteam : (v 29).val = l.team := hv.1.ready 29 (by decide)
          apply branch 35 29
          by_cases owner : l.owner before i side = l.team
          · rw [ite_eq_left (Fin.ext (howner.trans (owner.trans hteam.symm)))]
            exact owned_run pub macros l before (readings m) fit hi side v mv hv.1 hmem' frozen ⟨empty,coloc,owner⟩
          · rw [ite_eq_right (fun e => owner (howner.symm.trans ((congrArg Fin.val e).trans hteam)))]
            exact inactive pub macros l before (readings m) i side v mv hv.1.ready hv.1.index hmem'
              (fun h => owner h.2.2) (by dsimp [ticks]; omega))
  apply run.mono _ fun _ => id
  dsimp [ticks,visitOverhead]
  omega

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
