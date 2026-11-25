import OAI.Computability.BorderVNP.CrossingNetwork

/-!
# Degree and volume of bit networks

A bit wire has one binary index. A loop supplies two local ports at its
site, and an open wire supplies one local port at its attachment site.
The volume counts vertices and wires, including the external wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}

/-- Volume of a network with one bit on every cable and every external port. -/
def bitVolume (N : Network D P bits) : ℕ :=
  Fintype.card N.Site + Fintype.card N.Edge + Fintype.card P

open scoped Classical in
/-- Degree counts incidences, even if the two ends of a cable have the same site. -/
noncomputable def bitDegree (N : Network D P bits) (v : N.Site) : ℕ :=
  (Finset.univ.filter (fun e : P ⊕ N.Edge × Bool =>
    Sum.elim N.attach (fun eb => if eb.2 then N.dst eb.1 else N.src eb.1) e = v)).card

/-- Each index carries a single bit, and no site has more than three ports. -/
def Trivalent (N : Network D P (fun _ => 1)) : Prop :=
  (∀ e, N.width e = 1) ∧ ∀ v, N.bitDegree v ≤ 3

end Crossing.Network

end BorderVNP
end Computability
end OAI
