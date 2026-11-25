import OAI.Computability.MultitapeWeakETH.ResidueSweep
import OAI.Computability.MultitapeWeakETH.RetainedBranches
import OAI.Computability.MultitapeWeakETH.TerminalContraction

/-! # A uniform modular count for a bounded-occurrence width-three input -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords PairSimulation LocalHistory Filter
open NetworkKernel TerminalWords TerminalGatherGeometry DyadicBudget TemplateArithmetic FactorizedCompression
open Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse SparseDFSRefinement
open scoped Classical NumberField
noncomputable section

variable {R : Type} [CommRing R] {m : ℕ} {basis : Module.Basis (Fin m) ℤ R} (ops : ResidueOps basis)

private theorem wires_eq {a g : ℕ} (Y : State a g) (q : Sweep) (w : ℕ) (data : SharedData)
    (factor : LocalSumQuery SiteQuery → Rep) (v : Y.network.Site → R)
    (width : q.width = tally w) (size : q.sites = Iter.lineup (tally Y.positions))
    (values : ∀ u, residue basis w (Sweep.vertex factor ((q,data),tally ((siteOrder Y).entries.symm u).val)) =
        Ideal.Quotient.mk (modulus R w) (v u)) :
    Ideal.Quotient.mk (modulus R w) (decodeCoordinates basis (Sweep.wires ops factor (q,data))) =
      Ideal.Quotient.mk (modulus R w) (∏ u, v u) := by
  let o := siteOrder Y
  have length : Y.positions = o.length := by
    change Fintype.card Y.network.Site = o.length
    simpa only [Fintype.card_fin] using (Fintype.card_congr o.entries).symm
  change residue basis w (prodReps ops (q.width,_)) = _
  rw [width,prodReps_eq,size,length,Iter.lined,List.map_ofFn,List.map_ofFn,List.prod_ofFn,map_prod]
  apply Eq.trans _ (o.entries.prod_comp (fun u => Ideal.Quotient.mk (modulus R w) (v u)))
  apply Finset.prod_congr rfl
  intro i _
  have t := values (o.entries i)
  change residue basis w (Sweep.vertex factor ((q,data),tally (o.entries.symm (o.entries i)).val)) = _ at t
  rw [Equiv.symm_apply_apply] at t
  exact t

private theorem map_double_sum {ι : Type} {J : ι → Type} [Fintype ι] [∀ i, Fintype (J i)]
    {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (x y : (i : ι) → J i → A)
    (same : ∀ i j, φ (x i j) = φ (y i j)) :
    φ (∑ i, ∑ j, x i j) = φ (∑ i, ∑ j, y i j) := by
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => same i j))

variable {k K : Type} [_root_.Field k] [_root_.Field K] [NumberField K] {S : BlockSchedule k}
    (B : S.Templates) {hist : ℕ} (order : B.Entry ≃ Fin hist) (f : B.Entry → K) (hf : B.IsSolution f)
    (d : ℤ) (clear : ∀ i, IsIntegral ℤ ((d:K)*f i))
    (basis : Module.Basis (Fin m) ℤ (𝓞 K))

def formulaSweep (volume : Tally) (n w hint : ℕ) (body : Bits.Word) : Sweep :=
  let depth := searchWidth (2*(4*stepSize B)) volume
  (((volume,tally n,body),tally w,depth),Iter.lineup (tally (sites B (gridIndex B volume))),candidates (depth,tally hint))

attribute [local irreducible] BlockProgram.script BlockProgram.layout OnlineWorkspace.table source scale entryMemory

include order f hf clear

set_option maxHeartbeats 2400000 in
/-- A single polynomial tape routine accepts an explicit pool and modulus
width. Its result is the scaled model count modulo the selected power of two. -/
theorem sparse_residue :
    ∃ run : Sweep → Rep, Poly run ∧ ∀ᶠ N : ℕ in atTop, ∀ volume : Tally, volume.length=N →
      ∀ {n bound : ℕ} (F : RawCNF n), Valid 3 F → SAT.OccurrenceAtMost bound (ExecCNF.formulaSet F) →
        2*n+8*(n*bound)+1 ≤ N →
        let L := (searchWidth (2*(4*stepSize B)) volume).length
        let M := L*sites B (gridIndex B volume)
        ∀ w hint, 2^L ≤ 2*hint →
          let result := run (formulaSweep B volume n w hint (SparseCountProgram.encodeBody F))
          FitsWidth m w result ∧ (2:𝓞 K)^w ∣
            ((d^M*(SAT.count (ExecCNF.formulaSet F):ℤ) : ℤ) : 𝓞 K) - decodeCoordinates basis result := by
  obtain ⟨ops⟩ := residue_ops basis
  obtain ⟨localRead,localCost,locals⟩ := private_enumeration B order f hf
  obtain ⟨shared,outerCost,outer⟩ := terminal_branches (V:=𝓞 K) B f hf
  let factor := sumLocal order f d clear basis ops localRead
  let total := Sweep.total ops factor shared
  let run (q : Sweep) := ops.add (q.width,constant basis 0,total q)
  have cost := Sweep.total_poly ops factor shared (sumLocal_poly order f d clear basis ops localRead localCost) outerCost
  refine ⟨run,((show Poly (fun q : Sweep => q.1.2.1) by fun_prop).pair ((Code.Poly.const _).pair cost)).compose ops.add_cost,?_⟩
  filter_upwards [locals,outer] with N lp sp
  intro volume len n bound F valid occ small L M w hint fit result
  let s := gridIndex B volume
  let E := gridExecution B f hf volume
  let _ : Fintype E.Choices := choiceFintype E
  let q := formulaSweep B volume n w hint (SparseCountProgram.encodeBody F)
  have depth : q.budget = tally L := (recover_tally _).symm
  have pool : q.pool = candidates (tally L,tally hint) := congrArg (fun a => candidates (a,tally hint)) depth
  have width : q.width = tally w := rfl
  obtain ⟨P,count,parse⟩ := lp volume len F valid occ small
  obtain ⟨log,stored,outerSum⟩ := sp volume len
  let φ := Ideal.Quotient.mk (modulus (𝓞 K) w)
  let weight (data : SharedData) := decodeCoordinates basis (Sweep.wires ops factor (q,data))
  have aggregate := congrArg φ (outerSum weight)
  have atSite (z : E.Choices) (bits : (e : (E.finalState z).network.Edge) → (E.finalState z).network.Payload e) :=
    parse z (log z) (stored z)
  let value := terminalFactor B f hf d clear volume P L
  have correct (z : E.Choices) (p : (e : (E.finalState z).network.Edge) → (E.finalState z).network.Payload e) :
      let Y := E.finalState z
      let data : SharedData := ((writes (log z),widths Y,inverse Y),List.ofFn ((payload Y).symm p))
      φ (weight data) = φ (∏ u, value z p u) := by
    intro Y data
    let bits := (payload Y).symm p
    apply wires_eq ops Y q w data factor (value z p) width
    · exact congrArg (fun j => Iter.lineup (tally j)) (terminal_size B f hf s z).1
    · intro u
      let Q := gridParsers B f hf volume z P
      let a := half Y bits u
      obtain ⟨names,counts,_,_,parseAt⟩ := atSite z p u bits
      let arg : SiteQuery := ((q.formula,data),tally ((siteOrder Y).entries.symm u).val)
      have eval := sumLocal_eq order f d clear basis ops localRead w L L hint fit arg Q u a names counts parseAt
      change residue basis w (factor (((q.width,q.budget),arg),q.pool)) = _
      rw [width,depth,pool]
      apply eval.trans
      have halfEq : a = sharedHalf Y p u := by
        change sharedHalf Y (payload Y ((payload Y).symm p)) u = _
        rw [Equiv.apply_symm_apply]
      exact congrArg φ (congrArg (integralLocal f d clear Q L L u) halfEq)
  have all := terminal_contraction B f hf d clear volume P L _ count (fun z p u => by
    let Y := E.finalState z
    obtain ⟨_,_,len,deg,_⟩ := atSite z p u ((payload Y).symm p)
    have heq : TerminalGatherGeometry.half Y ((payload Y).symm p) u = sharedHalf Y p u := by
      change sharedHalf Y (payload Y ((payload Y).symm p)) u = _
      rw [Equiv.apply_symm_apply]
    rw [heq] at len deg
    exact ⟨len,deg⟩)
  have ends : residue basis w (total q) = φ ((d^M*(SAT.count (ExecCNF.formulaSet F):ℤ) : ℤ) : 𝓞 K) := by
    apply (Sweep.total_eq ops factor shared q w L hint width pool fit).trans
    apply aggregate.trans
    apply Eq.trans _ (congrArg φ all)
    exact map_double_sum φ _ _ correct
  refine ⟨ops.add_fit w _ _,?_⟩
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  change φ _ = residue basis w (ops.add (tally w,constant basis 0,total q))
  rw [ops.add_eq,← ends]
  simp [residue,constant_eq]

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
