import OAI.Hierarchy.DescentPackedSingletonDepth
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Isolated padded hosts do not affect the finite native reset depth sweeps -/
namespace Hierarchy.DescentPackedSingletonDepth.Canvas
open DescentColonies DescentBaseProfile
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {α : Type*} {H P n k Δ D w : ℕ}

def extend (_small : H≤P) (val : Fin H→α) (empty : α) (v : Fin P) :=
  if live : v.val<H then val ⟨v.val,live⟩ else empty

@[simp] theorem extend_real (small : H≤P) (val : Fin H→α) (empty : α) (v : Fin H) :
    extend small val empty (v.castLE small)=val v := by simp [extend,v.isLt]

def weights (small : H≤P) (old : Native.Rows H n) : Native.Rows P n :=
  Vector.ofFn (extend small (fun v=>old[v.val]) (Vector.replicate n 0))

def peers (small : H≤P) (old : Native.Neighbors H) : Native.Neighbors P :=
  Vector.ofFn (extend small (fun v=>(old[v.val]).map (Fin.castLE small)) [])

@[simp] theorem peers_real (small : H≤P) (old : Native.Neighbors H) (v : Fin H) :
    (peers small old)[(v.castLE small).val]=(old[v.val]).map (Fin.castLE small) := by
  simp [peers, extend, v.isLt]

theorem weights_real (small : H≤P) (old : Native.Rows H n) (v : Fin H) :
    (weights small old)[(v.castLE small).val]=old[v.val] := by simp [weights,extend,v.isLt]

theorem total_real (small : H≤P) (old : Native.Rows H n) (v : Fin H) :
    Native.totalWeight (weights small old) (v.castLE small)=Native.totalWeight old v := by
  simp only [Native.totalWeight_eq,weights_real]

theorem room (small : H≤P) (old : Native.Rows H n) (bound : ∀v,Native.totalWeight old v<2^w)
    (v : Fin P) : Native.totalWeight (weights small old) v<2^w := by
  by_cases live:v.val<H
  · let t:Fin H:=⟨v.val,live⟩
    exact lt_of_eq_of_lt (total_real small old t) (bound t)
  · simp [Native.totalWeight_eq,weights,extend,live]

theorem degree (small : H≤P) (old : Native.Neighbors H) (cap : ∀v:Fin H,(old[v.val]).length≤Δ)
    (slots : Δ≤D) (v : Fin P) : ((peers small old)[v.val]).length≤D := by
  by_cases live:v.val<H
  · simpa [peers,extend,live] using (cap ⟨v.val,live⟩).trans slots
  · simp [peers,extend,live]

theorem relax_real (small : H≤P) (ns : Native.Neighbors H) (seeds : Fin H→ℕ) (padded : Fin P→ℕ)
    (agree : ∀v,padded (v.castLE small)=seeds v) (g t : ℕ) (v : Fin H) :
    relax (fun s : Fin P=>((peers small ns)[s.val]).toFinset) padded g t (v.castLE small)=
      relax (fun s : Fin H=>(ns[s.val]).toFinset) seeds g t v := by
  induction t generalizing v with
  | zero=>exact agree v
  | succ t ih=>
    let real (s:Fin H):=relax (fun z : Fin H=>(ns[z.val]).toFinset) seeds g t s-g
    let full (s:Fin P):=relax (fun z : Fin P=>((peers small ns)[z.val]).toFinset) padded g t s-g
    have each (x : Fin H) : full (x.castLE small) = real x :=
      congrArg (fun a : ℕ => a - g) (ih x)
    have map_sup (xs : List (Fin H)) :
        (xs.map (Fin.castLE small)).toFinset.sup full = xs.toFinset.sup real := by
      induction xs with
      | nil => simp
      | cons x xs hx => simp only [List.map_cons, List.toFinset_cons, Finset.sup_insert, each, hx]
    change max (padded (v.castLE small)) (((peers small ns)[(v.castLE small).val]).toFinset.sup full) =
      max (seeds v) ((ns[v.val]).toFinset.sup real)
    rw [agree v, peers_real small ns v, map_sup]

theorem depth_real (small : H≤P) (ns : Native.Neighbors H) (old : Native.Rows H (2^k))
    (δ r f B : ℕ) (v : Fin H) :
    measuredDepth (peers small ns) (weights small old) δ r f B (v.castLE small)=measuredDepth ns old δ r f B v := by
  unfold measuredDepth Native.profile
  rw [Native.sweeps_read (peers small ns) _ _ _ (v.castLE small), Native.sweeps_read ns _ _ _ v]
  apply relax_real
  intro x
  simpa only [Native.seeds, Vector.getElem_ofFn, Fin.eta] using
    congrArg (fun mass : ℕ => max (k-r) (Native.probe mass (k-f) 0 (2^f*B)).1) (total_real small old x)

theorem depth_le (ns : Native.Neighbors P) (old : Native.Rows P (2^k))
    (δ r f B : ℕ) (v : Fin P) : measuredDepth ns old δ r f B v≤k := by
  unfold measuredDepth Native.profile
  rw [Native.sweeps_read]
  apply relax_le
  intro t
  have bound : (Native.probe (Native.totalWeight old t) (k-f) 0 (2^f*B)).1 ≤ k-f := by
    simpa only [Nat.zero_add] using
      DepthRAM.Layout.probe_depth (Native.totalWeight old t) (k-f) 0 (2^f*B)
  simpa only [Native.seeds, Vector.getElem_ofFn, Fin.eta] using
    max_le (Nat.sub_le k r) (bound.trans (Nat.sub_le k f))

/-- The physical row width is D. The smoothing step is the old graph's actual propagation exponent. -/
def layout (P D k r f B decay totals edges scratch : ℕ) : DepthRAM.Layout :=
  {DescentPackedSingletonDepth.layout P D k r f B totals edges scratch with g:=decay}

end
end Hierarchy.DescentPackedSingletonDepth.Canvas

end OAI
