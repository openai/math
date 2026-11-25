import OAI.Hierarchy.DescentBaseDepth
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Computing the smoothed profile using integer loads and two depth buffers -/

namespace Hierarchy.DescentBaseProfile.Native
open scoped BigOperators
variable {H N : ℕ}

/-- Bounded linear scan of dyadic thresholds. The running threshold doubles
at each step. The second output counts comparisons of actual integer loads. -/
def probe (W : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0,d,_ => (d,0)
  | i+1,d,p => if W≤p then (d,1) else
      let result := probe W i (d+1) (p+p)
      (result.1,result.2+1)

theorem probe_comparisons (W fuel d p : ℕ) : (probe W fuel d p).2≤fuel := by
  induction fuel generalizing d p with
  | zero => rfl
  | succ i ih =>
    by_cases pay : W≤p
    · simp [probe,pay]
    · simpa [probe,pay] using Nat.succ_le_succ (ih (d+1) (p+p))

private theorem probe_finds (W S fuel d goal : ℕ) (lo : d≤goal) (hi : goal≤d+fuel)
    (pay : W≤S*2^goal) (first : ∀j,d≤j → j<goal → ¬W≤S*2^j) :
    (probe W fuel d (S*2^d)).1=goal := by
  induction fuel generalizing d with
  | zero => simp [probe];omega
  | succ n ih =>
    by_cases done : d=goal
    · subst d
      simp [probe,pay]
    · simp only [probe,ite_eq_right (first d le_rfl (by omega))]
      rw [show S*2^d+S*2^d=S*2^(d+1) by ring]
      exact ih (d+1) (by omega) (by omega) (fun j dj under=>first j (by omega) under)

private theorem pay_iff (W d : ℕ) {S : ℕ} (live : 0<S) :
    W≤S*2^d ↔ (W:ℝ)/S≤(2:ℝ)^d := by
  have sp : (0:ℝ)<S := by exact_mod_cast live
  constructor
  · intro h
    apply (div_le_iff₀ sp).2
    exact_mod_cast (show W≤2^d*S by simpa only [mul_comm] using h)
  · intro h
    have h' : W≤2^d*S := by exact_mod_cast (div_le_iff₀ sp).mp h
    simpa only [mul_comm] using h'

theorem probe_seed (W lo M : ℕ) {S : ℕ} (live : 0<S) (enough : W≤S*2^M) :
    max lo (probe W M 0 S).1=seedDepth lo ((W:ℝ)/S) ((pay_iff W M live).mp enough) := by
  classical
  let h : ∃j : ℕ,(W:ℝ)/S≤(2:ℝ)^j := ⟨M,(pay_iff W M live).mp enough⟩
  let j := Nat.find h
  have hj : j≤M := Nat.find_min' h ((pay_iff W M live).mp enough)
  have found := probe_finds W S M 0 j (Nat.zero_le _) (by simpa only [Nat.zero_add] using hj)
    ((pay_iff W j live).mpr (Nat.find_spec h)) (fun i _ early affordable =>
      Nat.find_min h early ((pay_iff W i live).mp affordable))
  change max lo (probe W M 0 S).1 = max lo j
  simpa using congrArg (max lo) found

abbrev Rows (H N : ℕ) := Vector (Vector ℕ N) H
abbrev Neighbors (H : ℕ) := Vector (List (Fin H)) H

def totalWeight (weight : Rows H N) (v : Fin H) :=
  (List.ofFn (fun j : Fin N => (weight[v.val])[j.val])).sum

theorem totalWeight_eq (weight : Rows H N) (v : Fin H) :
    totalWeight weight v=∑ j : Fin N,(weight[v.val])[j.val] := by
  rw [totalWeight,List.sum_ofFn]

/-- The stored seed buffer is shared across every smoothing sweep. -/
def seeds (weight : Rows H N) (S lo M : ℕ) : Vector ℕ H :=
  Vector.ofFn (fun v => max lo (probe (totalWeight weight v) M 0 S).1)

private def largest (f : Fin H → ℕ) (row : List (Fin H)) :=
  row.foldr (fun w m=>max (f w) m) 0

private theorem largest_eq (f : Fin H → ℕ) (row : List (Fin H)) :
    largest f row=row.toFinset.sup f := by
  induction row with
  | nil => simp [largest]
  | cons w rest ih => simpa [largest] using congrArg (max (f w)) ih

/-- Each outgoing row is materialized as a vector before the next sweep
begins; an entry reads only its original seed and the old neighbor buffer. -/
def sweeps (ns : Neighbors H) (initial : Vector ℕ H) (g : ℕ) : ℕ → Vector ℕ H
  | 0 => initial
  | n+1 =>
    let old := sweeps ns initial g n
    Vector.ofFn (fun v => max (initial[v.val]) (largest (fun w=>old[w.val]-g) (ns[v.val])))

theorem sweeps_read (ns : Neighbors H) (initial : Vector ℕ H) (g n : ℕ) (v : Fin H) :
    (sweeps ns initial g n)[v.val]=relax (fun w : Fin H=>(ns[w.val]).toFinset)
      (fun w : Fin H=>initial[w.val]) g n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [sweeps,relax,largest_eq,ih]

def profile (ns : Neighbors H) (weight : Rows H N) (S g lo M : ℕ) :=
  sweeps ns (seeds weight S lo M) g M

theorem profile_read (ns : Neighbors H) (weight : Rows H N) {S : ℕ} (live : 0<S)
    (g lo M : ℕ) (room : ∀v,totalWeight weight v≤S*2^M) (v : Fin H) :
    (profile ns weight S g lo M)[v.val] =
      depth (fun w : Fin H=>(ns[w.val]).toFinset)
        (fun w => seedDepth lo ((totalWeight weight w:ℝ)/S) ((pay_iff _ _ live).mp (room w))) g M v := by
  have same : (fun w : Fin H => (seeds weight S lo M)[w.val]) =
      (fun w => seedDepth lo ((totalWeight weight w:ℝ)/S) ((pay_iff _ _ live).mp (room w))) := by
    funext w
    simpa only [seeds,Vector.getElem_ofFn,Fin.eta] using probe_seed (totalWeight weight w) lo M live (room w)
  simp only [profile,sweeps_read,depth,same]

/-- The output cells of the implementation meet all the normalized capacity,
growth, smoothness and total-count estimates for the actual integer input. -/
theorem profile_bounds (ns : Neighbors H) (weight : Rows H N)
    (sym : ∀v w : Fin H,w∈ns[v.val] ↔ v∈ns[w.val])
    {Δ g lo M S : ℕ} (degree : ∀v : Fin H,(ns[v.val]).length≤Δ) (spread : 2*Δ≤2^g)
    (hg : 0<g) (loM : lo≤M) (live : 0<S) (room : ∀v,totalWeight weight v≤S*2^M) :
    let p := profile ns weight S g lo M
    (∀v : Fin H,lo≤p[v.val] ∧ p[v.val]≤M ∧ (totalWeight weight v:ℝ)/S≤2^p[v.val]) ∧
    (∀ v w : Fin H,w∈ns[v.val] → p[w.val]≤p[v.val]+g) ∧
    (∑ v : Fin H,(2:ℝ)^p[v.val])≤4*((H:ℝ)*2^lo+∑v,(totalWeight weight v:ℝ)/S) := by
  have paid := normalized_profile_value (fun w:Fin H=>(ns[w.val]).toFinset)
    (fun v w=>by simpa using sym v w)
    (fun v=> (List.toFinset_card_le _).trans (degree v)) spread hg loM
    (fun v=>(totalWeight weight v:ℝ)/S) (fun v=>by positivity) (fun v=>(pay_iff _ _ live).mp (room v))
  simpa only [profile_read ns weight live g lo M room,Fintype.card_fin,List.mem_toFinset] using paid

/-- Integer denominators already common to every traffic entry cancel from
the allocation decisions. In particular the returned vector pays the physical
base count against the sum of the input loads in the same integer units. -/
theorem physical_profile (ns : Neighbors H) (weight : Rows H N)
    (sym : ∀v w : Fin H,w∈ns[v.val] ↔ v∈ns[w.val]) {Δ g lo M S : ℕ}
    (degree : ∀v : Fin H,(ns[v.val]).length≤Δ) (spread : 2*Δ≤2^g)
    (hg : 0<g) (loM : lo≤M) (live : 0<S) (room : ∀v,totalWeight weight v≤S*2^M) :
    let p := profile ns weight S g lo M
    (∀v : Fin H,lo≤p[v.val] ∧ p[v.val]≤M ∧ totalWeight weight v≤S*2^p[v.val]) ∧
    (∀ v w : Fin H,w∈ns[v.val] → p[w.val]≤p[v.val]+g) ∧
    S*(∑v : Fin H,2^p[v.val])≤4*(H*2^lo*S+∑v,totalWeight weight v) := by
  let p := profile ns weight S g lo M
  obtain ⟨fits,along,total⟩ := profile_bounds ns weight sym degree spread hg loM live room
  refine ⟨fun v=>⟨(fits v).1,(fits v).2.1,(pay_iff _ _ live).mpr (fits v).2.2⟩,along,?_⟩
  have sp : (0:ℝ)<S := by exact_mod_cast live
  have converted : (S:ℝ)*(∑v,(totalWeight weight v:ℝ)/S)=∑v,(totalWeight weight v:ℝ) := by
    rw [←Finset.sum_div]
    field_simp
  change (∑v : Fin H,(2:ℝ)^p[v.val])≤4*((H:ℝ)*2^lo+∑v,(totalWeight weight v:ℝ)/S) at total
  have all := mul_le_mul_of_nonneg_left total sp.le
  have pay : (S:ℝ)*(∑v : Fin H,(2:ℝ)^p[v.val])≤4*((H:ℝ)*2^lo*S+∑v,(totalWeight weight v:ℝ)) := by
    linarith only [all,converted]
  exact_mod_cast pay

/-- The seed scan always succeeds before the last admissible dyadic depth
for the actual per-old-block range bound, at S=2^f B and M=L-f. -/
theorem dyadic_room {L : ℕ} (weight : Rows H (2^L)) (f B : ℕ) (lo : f≤L)
    (limit : ∀ (v : Fin H) (j : Fin (2^L)),(weight[v.val])[j.val]≤B) (v : Fin H) :
    totalWeight weight v≤(2^f*B)*2^(L-f) := by
  rw [totalWeight_eq]
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => limit v j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at total
  apply total.trans_eq
  calc 2^L*B = (2^f*2^(L-f))*B := by rw [←pow_add,show f+(L-f)=L by omega]
       _ = _ := by ring

/-- Charge the input cells once, the integer seed comparisons at their actual
stopping times, and the one seed lookup plus all neighbor fetches at every
cell of each of the M two-buffer sweeps. The active space is three H-word
vectors (the fixed seeds, and the two successive depth vectors). -/
def profileReads (ns : Neighbors H) (weight : Rows H N) (S M : ℕ) :=
  H*N + (∑v,(probe (totalWeight weight v) M 0 S).2) +
    M*(∑ v : Fin H,(1+(ns[v.val]).length))

theorem profileReads_bound (ns : Neighbors H) (weight : Rows H N) (S M Δ : ℕ)
    (degree : ∀v : Fin H,(ns[v.val]).length≤Δ) :
    profileReads ns weight S M≤ H*N + H*M + M*(H*(1+Δ)) := by
  unfold profileReads
  have seedsPaid := Finset.sum_le_sum (s:=Finset.univ)
    (fun v _ => probe_comparisons (totalWeight weight v) M 0 S)
  have sweepPaid := Finset.sum_le_sum (s:=Finset.univ)
    (fun v _ => Nat.add_le_add_left (degree v) 1)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at seedsPaid sweepPaid
  exact Nat.add_le_add (Nat.add_le_add_left seedsPaid _) (Nat.mul_le_mul_left _ sweepPaid)

end Hierarchy.DescentBaseProfile.Native

end OAI
