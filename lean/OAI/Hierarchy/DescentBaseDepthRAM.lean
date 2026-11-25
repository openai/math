import OAI.Hierarchy.DescentBaseDepthLayout
import OAI.Hierarchy.DescentMeasuredBaseGeometry

namespace OAI
/-! # Readback of every computed base depth from the old physical census
and increasing native adjacency rows -/
noncomputable section
namespace Hierarchy.DescentBaseProfile.DepthRAM.Layout
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentColonies
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical BigOperators

variable {w : ℕ} (L : Layout) (ns : Native.Neighbors L.H) (weights : Native.Rows L.H L.N)
variable (m : Memory w)

structure Source : Prop where
  mass : ∀v : Fin L.H,∀i : Fin L.N,m (L.weights+v.val*L.N+i.val)=((weights[v.val])[i.val]:Word w)
  neighbor : ∀v : Fin L.H,∀q : Fin L.Δ,m (L.edges+v.val*L.Δ+q.val)=(number ((ns[v.val])[q.val]?):Word w)

theorem sum_read (safe : L.Fits w) (source : Source L ns weights m) (v : Fin L.H) :
    L.sums.memory m L.H (L.base 0+v.val)=(Native.totalWeight weights v:Word w) := by
  let f (i : ℕ) := if hi : i<L.N then (weights[v.val])[i] else 0
  change L.sums.memory m L.H (L.sums.out + v.val) = _
  rw [L.sums.read m L.H v.val v.isLt (((L.sums.expr v.val).fits_of_inputEnd (L.sum_span safe v.isLt)
    (by have:=L.end_room safe (j:=0) (by omega);change L.base 0<_;omega)))]
  change (rowSum (L.weights+v.val*L.N) L.N).eval m 0=_
  rw [rowSum_read m _ _ f 0 (fun i hi=>by simpa [f,hi] using source.mass v ⟨i,hi⟩)]
  rw [Native.totalWeight_eq,←Fin.sum_univ_eq_sum_range f L.N]
  simp [f]

theorem initial_read (safe : L.Fits w) (source : Source L ns weights m)
    (totals : ∀v,Native.totalWeight weights v<2^w) (v : Fin L.H) :
    L.output m 0 (L.base 1+v.val)=((Native.seeds weights L.S L.lo L.M)[v.val]:Word w) := by
  have room:=L.end_room safe (j:=1) (by omega)
  have seen : ((L.seed w).expr v.val).Fits w (L.seed w).out :=
    ((L.seed w).expr v.val).fits_of_inputEnd (L.seed_span safe v.isLt) (by change L.base 1<_;omega)
  change (L.seed w).memory (L.sums.memory m L.H) L.H ((L.seed w).out+v.val)=_
  rw [(L.seed w).read _ _ _ v.isLt seen]
  simpa [seed,Native.seeds] using probe_read (L.sums.memory m L.H) (L.base 0+v.val)
    (Native.totalWeight weights v) L.lo L.M 0 L.S 0 (totals v) (L.sum_read ns weights m safe source v)

theorem seed_retained (safe : L.Fits w) (s : ℕ) (v : Fin L.H) :
    L.output m s (L.base 1+v.val)=L.output m 0 (L.base 1+v.val) := by
  induction s with
  | zero=>rfl
  | succ s ih=>
    have low:=L.base_mono (show 2≤ s+2 by omega)
    have inside : L.base 1+v.val<L.base (s+2) := calc
      L.base 1+v.val < L.base 1+2^L.hostBits := Nat.add_lt_add_left (v.isLt.trans_le safe.sites) _
      _ = L.base 2 := (L.base_succ 1).symm
      _ ≤ L.base (s+2) := low
    exact ((L.step s).before _ _ _ inside).trans ih

theorem probe_depth (W fuel d p : ℕ) : (Native.probe W fuel d p).1≤d+fuel := by
  induction fuel generalizing d p with
  | zero=>simp [Native.probe]
  | succ fuel ih=>
    simp only [Native.probe]
    split
    · omega
    · have h:=ih (d+1) (p+p);omega

theorem next_sup (v : Fin L.H) (values : Fin L.H→ℕ) (cap : (ns[v.val]).length≤L.Δ)
    (fit : L.Δ≤2^L.degreeBits) :
    largest (fun q=>((ns[v.val])[q]?).elim 0 values) L.degreeBits 0=(ns[v.val]).toFinset.sup values := by
  apply le_antisymm
  · apply largest_le
    intro q _ _
    cases h : (ns[v.val])[q]? with
    | none=>exact Nat.zero_le _
    | some j=>exact Finset.le_sup (f:=values) (List.mem_toFinset.mpr (List.mem_of_getElem? h))
  · apply Finset.sup_le
    intro j hj
    obtain ⟨q,hq,eq⟩:=List.mem_iff_getElem.mp (List.mem_toFinset.mp hj)
    have h:=le_largest (fun q=>((ns[v.val])[q]?).elim 0 values) L.degreeBits 0 q (Nat.zero_le _)
      (by have:=hq.trans_le (cap.trans fit);omega)
    simpa [List.getElem?_eq_getElem hq,eq] using h

theorem profile_read (safe : L.Fits w) (source : Source L ns weights m)
    (totals : ∀v,Native.totalWeight weights v<2^w) (degree : ∀v : Fin L.H,(ns[v.val]).length≤L.Δ)
    (s : ℕ) (hs : s≤L.M) (v : Fin L.H) :
    L.output m s (L.base (s+1)+v.val)=
      ((Native.sweeps ns (Native.seeds weights L.S L.lo L.M) L.g s)[v.val]:Word w) := by
  let seeds:=Native.seeds weights L.S L.lo L.M
  let near:=fun j : Fin L.H=>(ns[j.val]).toFinset
  let old (n : ℕ) := relax near (fun j : Fin L.H=>seeds[j.val]) L.g n
  have small (u : Fin L.H) : seeds[u.val]≤ max L.lo L.M := by
    have h:=probe_depth (Native.totalWeight weights u) L.M 0 L.S
    simpa [seeds,Native.seeds] using (max_le_max_left L.lo (by simpa using h))
  have below (n : ℕ) (u : Fin L.H) : old n u<2^w := (relax_le near small L.g n u).trans_lt safe.depths
  induction s generalizing v with
  | zero=>exact L.initial_read ns weights m safe source totals v
  | succ s ih=>
    have previous (u : Fin L.H) : L.output m s (L.base (s+1)+u.val)=(old s u:Word w) := by
      simpa only [old,near,seeds,Native.sweeps_read] using ih (by omega) u small below
    have hh := L.end_room safe (j:=0) (by omega)
    have room:=L.end_room safe (j:=s+2) (by omega)
    have stepFit : ((L.step s).expr v.val).Fits w (L.step s).out := ((L.step s).expr v.val).fits_of_inputEnd (L.step_span safe v.isLt s)
      (by change L.base (s+2)<_;omega)
    change (L.step s).memory (L.output m s) L.H ((L.step s).out+v.val)=_
    rw [(L.step s).read _ _ _ v.isLt stepFit]
    let value (q : ℕ) := ((ns[v.val])[q]?).elim 0 (fun u=>old s u-L.g)
    have peerRead (q : ℕ) : (L.peer s v.val q).eval (L.output m s) 0=(value q:Word w) := by
      unfold peer
      split
      next hq=>
        have h:=Nat.mul_le_mul_right L.Δ (show v.val+1≤L.H from v.isLt)
        simp only [Nat.succ_mul] at h
        exact neighbor_read _ _ _ _ _ _ _ (by omega) safe.sites safe.propagation
          ((L.static m s _ (by have:=safe.edges;omega)).trans (source.neighbor v ⟨q,hq⟩)) (old s) (below s) previous
      next hq =>
        have absent : (ns[v.val])[q]? = none :=
          List.getElem?_eq_none ((degree v).trans (Nat.le_of_not_gt hq))
        simp [value, Expr.eval, absent]
    have bounded (q : ℕ) : value q<2^w := by
      unfold value
      cases (ns[v.val])[q]? with
      | none=>exact Nat.two_pow_pos _
      | some u=>exact (Nat.sub_le _ _).trans_lt (below s u)
    have mx:=L.next_sup ns v (fun u=>old s u-L.g) (degree v) safe.degree
    have supBound : largest value L.degreeBits 0<2^w := by
      apply Nat.lt_of_le_of_lt (largest_le _ _ (x:=2^w-1) (fun q _ _=>by have:=bounded q;omega))
      have:=Nat.two_pow_pos w;omega
    change (maximum (cell (L.base 1+v.val)) (tournament (L.peer s v.val) L.degreeBits 0)).eval _ 0=_
    rw [max_read _ _ _ _ (seeds[v.val]) (largest value L.degreeBits 0)
      ((cell_read ..).trans ((L.seed_retained m safe s v).trans (L.initial_read ns weights m safe source totals v)))
      (tournament_read _ _ _ value _ _ peerRead bounded) ((small v).trans_lt safe.depths) supBound,
      Native.sweeps_read]
    exact congrArg (fun z : ℕ => ((max seeds[v.val] z : ℕ) : Word w)) mx

/-- The old physical census and old sparse adjacency determine every stored
new depth. No layout-dependent input or depth advice enters the CPU. -/
theorem run (safe : L.Fits w) (source : Source L ns weights m)
    (totals : ∀v,Native.totalWeight weights v<2^w) (degree : ∀v : Fin L.H,(ns[v.val]).length≤L.Δ) :
    (L.cpu w L.M).Exec m (L.output m L.M) (L.clocks w L.M) ∧
    ∀v : Fin L.H,L.output m L.M (L.base (L.M+1)+v.val)=((Native.profile ns weights L.S L.g L.lo L.M)[v.val]:Word w) :=
  ⟨L.execute m safe _ le_rfl,L.profile_read ns weights m safe source totals degree _ le_rfl⟩

end Hierarchy.DescentBaseProfile.DepthRAM.Layout
end

end OAI
