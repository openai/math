import OAI.Hierarchy.DescentRotorAttachments
import OAI.LinearAlgebra.SpectralBooks.PortWiring

namespace OAI
/-! # The physical graph of the local attachment path -/

namespace Hierarchy.DescentRotor.Attachment
open LinearAlgebra.SpectralBooks
open scoped Classical BigOperators
noncomputable section

variable {n : ℕ}

/-- The two unary ends and one tap per row. -/
abbrev Site (n : ℕ) := Bool ⊕ Fin n

def prevSite (k : Fin (n+1)) : Site n := Fin.cases (.inl false) Sum.inr k

def nextSite (k : Fin (n+1)) : Site n := Fin.lastCases (.inl true) Sum.inr k

/-- Internal wire k crosses from tap k-1 to tap k with the two ends of the path
handling the first and last wires. -/
def path (n : ℕ) : PortGraph (Site n) (Fin (n+1)) := ⟨prevSite,nextSite⟩

/-- Including the external row, the two ends have one port each and every tap
has three distinct ports. -/
abbrev LocalPort (s : Site n) := (path n).Port s ⊕ {i : Fin n // Sum.inr i=s}

private theorem prev_injective : Function.Injective (prevSite (n:=n)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [prevSite]
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [prevSite]

private theorem next_injective : Function.Injective (nextSite (n:=n)) := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [nextSite]
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [nextSite]

theorem path_ports_le_three (s : Site n) : Fintype.card (LocalPort s)≤3 := by
  let color : LocalPort s → Fin 3
    | .inl p => if p.val.2 then 0 else 1
    | .inr _ => 2
  apply (Fintype.card_le_of_injective color ?_).trans (by simp)
  intro a b eq
  rcases a with ⟨⟨a,ba⟩,ha⟩ | ⟨a,ha⟩ <;> rcases b with ⟨⟨b,bb⟩,hb⟩ | ⟨b,hb⟩
  · apply congrArg Sum.inl
    apply Subtype.ext
    cases ba <;> cases bb <;> simp [color] at eq ⊢
    · exact prev_injective (ha.trans hb.symm)
    · exact next_injective (ha.trans hb.symm)
  · cases ba <;> simp [color] at eq
  · cases bb <;> simp [color] at eq
  · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj (ha.trans hb.symm)))

/-- Each tap and each singleton end is a real vertex, including n=0. -/
theorem card_sites (n : ℕ) : Fintype.card (Site n)=n+2 := by simp [Site,Nat.add_comm]

private def outward (k : Fin (n+1)) : (path n).Port (prevSite k) := ⟨(k,false),rfl⟩

variable {A : Fin n → Type*} {K : Type*} [CommSemiring K]

/-- At a tap, the coefficient uses one boundary word and its two adjacent path
wires. At the first unary end it evaluates the site's original table. -/
def localTable (table : ((i : Fin n) → A i) → K) (x : (i : Fin n) → A i) :
    (s : Site n) → (path n).State (fun _ => (i : Fin n) → A i) s → K
  | .inl false, h => table (h (outward 0))
  | .inl true, _ => 1
  | .inr i, h => tap i (x i)
      (h ⟨(i.castSucc,true),by simp [path,PortGraph.vertex,nextSite]⟩)
      (h ⟨(i.succ,false),rfl⟩)

/-- The physical graph's sum over all shared internal path wires exactly
recovers the original coefficient, with every exterior row kept separate. -/
theorem path_contraction [∀ i,Fintype (A i)] (table : ((i : Fin n) → A i) → K) (x : (i : Fin n) → A i) :
    (path n).contraction (A:=fun _ => (i : Fin n) → A i) (localTable table x)=table x := by
  rw [← spine_eq table x]
  unfold PortGraph.contraction spine
  apply Finset.sum_congr (by ext q; simp only [Finset.mem_univ])
  intro a _
  rw [Fintype.prod_sum_type,Fintype.prod_bool]
  simp [localTable,PortGraph.atVertex,outward]

end
end Hierarchy.DescentRotor.Attachment

end OAI
