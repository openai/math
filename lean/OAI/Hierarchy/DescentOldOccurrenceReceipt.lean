import OAI.Hierarchy.DescentOldOccurrenceSlots
import OAI.Hierarchy.DescentOldOccurrenceFields

namespace OAI
/-! # Physical original edge at each typed source-pool position -/

namespace Hierarchy.DescentOldOccurrenceRAM
open DescentSixParty DescentPacking ProtocolRAMPortRanks
open scoped BigOperators Classical
noncomputable section
variable {F P C : Type} [Field F] [Fintype C] [DecidableEq C] {d : ℕ} {bits : P→ℕ}
    (W : MarkedWorld F d P bits) (home : W.graph.Site→C) (color : W.graph.Site→Bool)
local notation "N" => W.graph
local notation "T" => nativeTraffic N W.core home
local notation "bin" => Fintype.equivFin C
local notation "site" => Fintype.equivFin W.graph.Site
local notation "edge" => Fintype.equivFin W.graph.Edge

def globalStart (side : Bool) (c : C) :=
  count (fun f=>f∈W.core ∧ color (W.graph.src f)=side ∧ bin (home (W.graph.src f)) < bin c)

def order (side : Bool) :=
  DescentTerminalSortRAM.order (origin W (edge).symm home (bin).toEmbedding color side)
    (middle W (edge).symm (site).symm home (bin).toEmbedding side)
    (lower W (edge).symm (site).symm home (bin).toEmbedding side)

omit [Field F] [DecidableEq C] in
theorem position (side : Bool) (e : (N).Edge) (keep : e∈W.core) (shade : color ((N).src e)=side) :
    let x := (N).src e
    let c := home x
    let _v := home ((N).dst e)
    let first := fun f : (N).Edge => if side then (bin (home ((N).dst f))).val else (site ((N).src f)).val
    let next := fun f : (N).Edge => if side then (site ((N).src f)).val else (bin (home ((N).dst f))).val
    ((order W home color side).symm (edge e)).val =
      globalStart W home color side c +
      count (fun f=>active N W.core home color c side f ∧ first f < first e) +
      count (fun f=>active N W.core home color c side f ∧ first f=first e ∧ next f < next e) +
      count (fun f=>active N W.core home color c side f ∧ first f=first e ∧ next f=next e ∧ edge f < edge e) := by
  classical
  let ix := Fintype.equivFin (N).Edge
  let sx := Fintype.equivFin (N).Site
  let bx := Fintype.equivFin C
  let good (f : (N).Edge) := f ∈ W.core ∧ color ((N).src f) = side
  let col (f : (N).Edge) := bx (home ((N).src f))
  let k0 := origin W ix.symm home bx.toEmbedding color side
  let k1 := middle W ix.symm sx.symm home bx.toEmbedding side
  let k2 := lower W ix.symm sx.symm home bx.toEmbedding side
  let firstKey (f : (N).Edge) :=
    if side then (bx (home ((N).dst f))).val else (sx ((N).src f)).val
  let nextKey (f : (N).Edge) :=
    if side then (sx ((N).src f)).val else (bx (home ((N).dst f))).val
  have transport (p : Fin (Fintype.card (N).Edge) → Prop) (q : (N).Edge → Prop)
      (h : ∀ f, p (ix f) ↔ q f) : count p = count q := by
    apply count_equiv ix.symm p q
    intro i
    simpa only [Equiv.apply_symm_apply] using h (ix.symm i)
  have yesKey (f : (N).Edge) (hf : good f) : k0 (ix f) = (col f).castSucc := by
    change f ∈ W.core ∧ color ((N).src f) = side at hf
    simp [k0, origin, hf, col]
  have noKey (f : (N).Edge) (hf : ¬good f) : k0 (ix f) = Fin.last (Fintype.card C) := by
    change ¬(f ∈ W.core ∧ color ((N).src f) = side) at hf
    simp [k0, origin, hf]
  have head := yesKey e ⟨keep, shade⟩
  have ltKey (f : (N).Edge) : k0 (ix f) < k0 (ix e) ↔
      f ∈ W.core ∧ color ((N).src f) = side ∧ col f < col e := by
    rw [head]
    by_cases hf : good f
    · rw [yesKey f hf, Fin.castSucc_lt_castSucc_iff]
      exact ⟨fun h => ⟨hf.1, hf.2, h⟩, fun h => h.2.2⟩
    · rw [noKey f hf]
      exact ⟨fun h => ((not_lt_of_ge (Fin.le_last _)) h).elim,
        fun h => (hf ⟨h.1, h.2.1⟩).elim⟩
  have eqKey (f : (N).Edge) : k0 (ix f) = k0 (ix e) ↔
      active N W.core home color (home ((N).src e)) side f := by
    rw [head]
    by_cases hf : good f
    · rw [yesKey f hf, Fin.castSucc_inj]
      exact ⟨fun h => ⟨hf.1, bx.injective h, hf.2⟩,
        fun h => congrArg (fun c : C => bx c) h.2.1⟩
    · rw [noKey f hf]
      exact ⟨fun h => ((ne_of_lt (Fin.castSucc_lt_last (col e))) h.symm).elim,
        fun h => (hf ⟨h.1, h.2.2⟩).elim⟩
  have val1 (f : (N).Edge) : (k1 (ix f)).val = firstKey f := by
    by_cases hs : side = true <;> simp [k1, middle, firstKey, hs, sourceKey, targetKey]
  have val2 (f : (N).Edge) : (k2 (ix f)).val = nextKey f := by
    by_cases hs : side = true <;> simp [k2, lower, nextKey, hs, sourceKey, targetKey]
  have lt1 (f : (N).Edge) : k1 (ix f) < k1 (ix e) ↔ firstKey f < firstKey e := by
    simp only [Fin.lt_def, val1]
  have eq1 (f : (N).Edge) : k1 (ix f) = k1 (ix e) ↔ firstKey f = firstKey e := by
    simp only [Fin.ext_iff, val1]
  have lt2 (f : (N).Edge) : k2 (ix f) < k2 (ix e) ↔ nextKey f < nextKey e := by
    simp only [Fin.lt_def, val2]
  have eq2 (f : (N).Edge) : k2 (ix f) = k2 (ix e) ↔ nextKey f = nextKey e := by
    simp only [Fin.ext_iff, val2]
  dsimp only
  unfold order globalStart
  rw [count_four_lex]
  apply congrArg₂ Nat.add
  · apply congrArg₂ Nat.add
    · apply congrArg₂ Nat.add
      · exact transport _ _ ltKey
      · exact transport _ _ (fun f => and_congr (eqKey f) (lt1 f))
    · exact transport _ _ (fun f => and_congr (eqKey f) (and_congr (eq1 f) (lt2 f)))
  · exact transport _ _ (fun f => and_congr (eqKey f) (and_congr (eq1 f) (and_congr (eq2 f) Iff.rfl)))

variable (c : C) (B : ℕ)
local notation "thin" => thinList home color c
local notation "thick" => thickList home color c
local notation "pk" => slabPacking T B thin thick

omit [Field F] [Fintype C] in
theorem original_mem (a : Atom T) : PairRAM.original N W.core home a∈W.core :=
  ((graphAtom (coreGraph N W.core) (fun e=>home (W.graph.dst e.val)) (coreId N W.core)).symm a).property

omit [Field F] [Fintype C] in
theorem original_src (a : Atom T) : W.graph.src (PairRAM.original N W.core home a)=a.1 :=
  graphAtom_src (coreGraph N W.core) (fun f => home (W.graph.dst f.val)) a (coreId N W.core)

omit [Field F] [Fintype C] in
theorem original_dest (a : Atom T) : home (W.graph.dst (PairRAM.original N W.core home a))=a.2.1 :=
  graphAtom_dest (coreGraph N W.core) (fun f => home (W.graph.dst f.val)) a (coreId N W.core)

omit [Field F] in
theorem thick_position (v : C) (o : ThickPool T thick v) :
    let a : Atom T := ⟨(thick).get o.1,v,o.2⟩
    ((order W home color true).symm (edge (PairRAM.original N W.core home a))).val =
      globalStart W home color true c+PairRAM.thickOffset N W.core home color c v+
      (thickPoolOrder T thick v o).val := by
  let u : (N).Site := (thick).get o.1
  let a : Atom T := ⟨u,v,o.2⟩
  let e := PairRAM.original N W.core home a
  have src : (N).src e=u := original_src W home a
  have dst : home ((N).dst e)=v := original_dest W home a
  have colored : home u=c ∧ color u=true :=
    (mem_colorSites (U := (N).Site) home color true c u).mp (List.get_mem (thick) o.1)
  have full := position W home color true e (original_mem W home a)
    (by simpa only [src] using colored.2)
  simp only [ite_true,src,dst,colored.1,Fin.val_inj,Equiv.apply_eq_iff_eq] at full
  have lastCount : o.2.val = count (fun f=>f∈W.core ∧ (N).src f=u ∧
      home ((N).dst f)=v ∧ edge f < edge e) := unit_eq N W.core home a
  have packed : (thickPoolOrder T thick v o).val =
      «prefix» (fun i : Fin (thick).length => T ((thick).get i) v) Fin.val o.1 + o.2.val := rfl
  have outside := outsideThick N W.core home color c v
  have earlier := thick_site N W.core home color c v o.1
  have inside : count (fun f=>active N W.core home color c true f ∧ home ((N).dst f)=v ∧
      (N).src f=u ∧ edge f < edge e) =
      count (fun f=>f∈W.core ∧ (N).src f=u ∧ home ((N).dst f)=v ∧ edge f < edge e) := by
    apply count_congr
    intro f
    by_cases same : (N).src f=u <;> simp [active,same,colored.1,colored.2,and_comm]
  change ((order W home color true).symm (edge e)).val = _
  rw [full, outside, packed, earlier, lastCount]
  rw [inside]
  simp only [Fin.lt_def, Nat.add_assoc, u]

omit [Field F] in
theorem thin_position (j : Locations (pk).decisions)
    (o : ThinPool T ((pk).decisions.get j).1) :
    let a : Atom T := ⟨((pk).decisions.get j).1.get o.1, o.2⟩
    ((order W home color false).symm ((Fintype.equivFin W.graph.Edge)
      (PairRAM.original W.graph W.core home a))).val =
      globalStart W home color false c + PairRAM.rawOffset W.graph W.core home color B c j +
        (thinPoolOrder T ((pk).decisions.get j).1 o).val := by
  rcases o with ⟨i, v, t⟩
  let xs : List W.graph.Site := ((pk).decisions.get j).1
  let u : W.graph.Site := xs.get i
  let a : Atom T := ⟨u, v, t⟩
  let e : W.graph.Edge := PairRAM.original W.graph W.core home a
  let siteOrd := Fintype.equivFin W.graph.Site
  let destOrd := Fintype.equivFin C
  let edgeOrd := Fintype.equivFin W.graph.Edge
  let base := globalStart W home color false c
  let off := PairRAM.rawOffset W.graph W.core home color B c j
  let localSite := «prefix» (fun k : Fin xs.length => live T (xs.get k)) Fin.val i
  let localDest := «prefix» (T u) (fun b : C => (destOrd b).val) v
  let bySite := count (fun f : W.graph.Edge => active W.graph W.core home color c false f ∧
    siteOrd (W.graph.src f) < siteOrd u)
  let byDest := count (fun f : W.graph.Edge => active W.graph W.core home color c false f ∧
    W.graph.src f = u ∧ destOrd (home (W.graph.dst f)) < destOrd v)
  let byEdge := count (fun f : W.graph.Edge => active W.graph W.core home color c false f ∧
    W.graph.src f = u ∧ home (W.graph.dst f) = v ∧ edgeOrd f < edgeOrd e)
  have hsrc : W.graph.src e = u := original_src W home a
  have hdst : home (W.graph.dst e) = v := original_dest W home a
  have inBlocks : u ∈ ((pk).decisions.map Prod.fst).flatten := by
    apply List.mem_flatten.mpr
    exact ⟨xs, List.mem_map.mpr ⟨(pk).decisions.get j, List.get_mem _ j, rfl⟩,
      List.get_mem xs i⟩
  have member : u ∈ thin :=
    (congrArg (fun ys : List W.graph.Site => u ∈ ys) (thin_stream T B thin thick)).mp inBlocks
  have colored : home u = c ∧ color u = false :=
    (mem_colorSites home color false c u).mp member
  have shade : color (W.graph.src e) = false := (congrArg color hsrc).trans colored.2
  have rawPosition := position W home color false e (original_mem W home a) shade
  have pos : ((order W home color false).symm (edgeOrd e)).val =
      base + bySite + byDest + byEdge := by
    simpa only [base, bySite, byDest, byEdge, siteOrd, destOrd, edgeOrd, Bool.false_eq_true,
      ite_false, hsrc, hdst, colored.1, Fin.val_inj, Equiv.apply_eq_iff_eq, Fin.lt_def] using rawPosition
  have sites : off + localSite = bySite := thin_site W.graph W.core home color c B j i
  have destinations : localDest = count (fun f : W.graph.Edge => f ∈ W.core ∧
      W.graph.src f = u ∧ destOrd (home (W.graph.dst f)) < destOrd v) :=
    thin_destination W.graph W.core home u v
  have unit : t.val = count (fun f : W.graph.Edge => f ∈ W.core ∧ W.graph.src f = u ∧
      home (W.graph.dst f) = v ∧ edgeOrd f < edgeOrd e) := unit_eq W.graph W.core home a
  have cross (q : W.graph.Edge → Prop) :
      count (fun f => active W.graph W.core home color c false f ∧ W.graph.src f = u ∧ q f) =
      count (fun f => f ∈ W.core ∧ W.graph.src f = u ∧ q f) := by
    apply count_congr
    intro f
    by_cases hs : W.graph.src f = u
    · simp [active, hs, colored.1, colored.2]
    · simp [hs]
  have destCount : byDest = localDest :=
    (cross (fun f => destOrd (home (W.graph.dst f)) < destOrd v)).trans destinations.symm
  have edgeCount : byEdge = t.val :=
    (cross (fun f => home (W.graph.dst f) = v ∧ edgeOrd f < edgeOrd e)).trans unit.symm
  have pool : (thinPoolOrder T xs ⟨i, v, t⟩).val = localSite + (localDest + t.val) := by
    change «prefix» (fun k : Fin xs.length => Fintype.card (Σ b : C, Fin (T (xs.get k) b)))
        Fin.val i + (localDest + t.val) = localSite + (localDest + t.val)
    simp only [Fintype.card_sigma, Fintype.card_fin, localSite, live]
  change ((order W home color false).symm (edgeOrd e)).val =
    base + off + (thinPoolOrder T xs ⟨i, v, t⟩).val
  calc
    _ = base + bySite + byDest + byEdge := pos
    _ = base + (off + localSite) + localDest + t.val := by rw [← sites, destCount, edgeCount]
    _ = base + off + (localSite + (localDest + t.val)) := by simp only [Nat.add_assoc]
    _ = _ := congrArg (fun k => base + off + k) pool.symm

end
end Hierarchy.DescentOldOccurrenceRAM

end OAI
