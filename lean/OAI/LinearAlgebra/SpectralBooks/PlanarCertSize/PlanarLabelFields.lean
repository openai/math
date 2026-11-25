import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPortViews

/-! # Numbered darts in vertex face certificates

The local face entry for a dart gives the vertex name and one-based port number
of the reported minimum, followed by its forward distance. Vacant port slots
carry three zeros.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarCertSize

variable {V E : Type*} (G : PortGraph V E) (num : G.FourPortNumbering) (name : V → ℕ)

/-- A vertex name and one-based port number identify a dart. -/
def dartCode (p : E × Bool) : ℕ × ℕ :=
  (name (G.vertex p.1 p.2), (num _ ⟨p, rfl⟩).val + 1)

theorem dartCode_injective (hn : Function.Injective name) :
    Function.Injective (dartCode G num name) := by
  have eq_ports {v w : V} (p : G.Port v) (q : G.Port w) (hv : v = w)
      (hp : (num v p).val + 1 = (num w q).val + 1) : p.val = q.val := by
    subst w
    exact congrArg Subtype.val ((num v).injective (Fin.ext (Nat.succ.inj hp)))
  intro p q h
  exact eq_ports ⟨p, rfl⟩ ⟨q, rfl⟩ (hn (congrArg Prod.fst h)) (congrArg Prod.snd h)

variable (report : E × Bool → (E × Bool) × ℕ)

/-- Read the report for the dart at a numbered slot; pad unused slots by zeros. -/
noncomputable def slotFace (v : V) (i : Fin 4) : ℕ × ℕ × ℕ :=
  match Function.partialInv (num v) i with
  | none => (0, 0, 0)
  | some p =>
    let (m, d) := report p.val
    let c := dartCode G num name m
    (c.1, c.2, d)

@[simp] theorem slotFace_port {v : V} (p : G.Port v) :
    slotFace G num name report v (num v p) =
      ((dartCode G num name (report p.val).1).1,
       (dartCode G num name (report p.val).1).2, (report p.val).2) := by
  simp only [slotFace, Function.partialInv_left (num v).injective p]

@[simp] theorem slotFace_none (v : V) (i : Fin 4) (h : ¬∃ p, num v p = i) :
    slotFace G num name report v i = (0, 0, 0) := by
  simp [slotFace, Function.partialInv, h]

/-- The collection of local slot fields determines the entire dart report. -/
theorem slotFace_injective (hn : Function.Injective name) :
    Function.Injective (slotFace G num name) := by
  intro f g he
  funext p
  let q : G.Port (G.vertex p.1 p.2) := ⟨p, rfl⟩
  have h := congrFun (congrFun he (G.vertex p.1 p.2)) (num _ q)
  simp only [slotFace_port] at h
  have hc := congrArg (fun a : ℕ × ℕ × ℕ => (a.1, a.2.1)) h
  exact Prod.ext (dartCode_injective G num name hn hc) (congrArg (fun a => a.2.2) h)

end PlanarCertSize

end SpectralBooks
end LinearAlgebra
end OAI
