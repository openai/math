import OAI.Hierarchy.TaggedWireExpansion
import OAI.Hierarchy.TaggedWireRoutes
import OAI.Hierarchy.ProtocolRAMRepairHistogram

namespace OAI
/-! # A native repair pass as a simultaneous ordinary-sum tensor transition -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAM ProtocolRAM.RepairHistogram AdaptiveProbe
open Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing

variable {F : Type*} [Field F] {S n g W t : ℕ}
    {J : Fin t → Type} [∀ j,Fintype (J j)]

theorem chordWidths_add {E : Type} [Fintype E]
    (G : PortGraph (Fin S) E) (u v : E → ℕ) :
    G.chordWidths (fun e=>u e+v e) = G.chordWidths u+G.chordWidths v := by
  classical
  let : DecidableEq E := Classical.decEq E
  simp only [PortGraph.chordWidths,chordWidth_scaled,add_smul,Finset.sum_add_distrib]

theorem chordWidths_le {E : Type} [Fintype E] (G : PortGraph (Fin S) E)
    {u v : E→ℕ} (fund : ∀ e,u e≤v e) : G.chordWidths u ≤ G.chordWidths v := by
  have eqn : v = fun e=>u e+(v e-u e) := funext fun e=>(Nat.add_sub_of_le (fund e)).symm
  calc
    G.chordWidths u ≤ G.chordWidths u+G.chordWidths (fun e=>v e-u e) := le_self_add ..
    _ = G.chordWidths v := (chordWidths_add ..).symm.trans (congrArg G.chordWidths eqn.symm)

/-- Physical commodity rows can be parallel and a scheduled packet may debit
the same commodity more than once. The native sparse scatter aggregates all
of them before projecting to the common tensor's unordered chord widths. -/
def native_repair (G : PortGraph (Fin S) (Fin g)) (bank : Bank) (p : Columns)
    (src : ℕ) (state : (∀j,J j) → Memory W) (stock : Fin g → ℕ)
    (demand : Fin t → Widths S) (inst : ∀ j,J j → Widths S)
    (tiles : ∀ j,Expansion (ChordGraph.raw F (demand j)) (J j) (inst j))
    (debits : Fin g → ℕ) (debited : (∑ j,demand j)=G.chordWidths debits)
    (selected : ∀ c e, OuterBank.resourceBits (kind bank p (state c))
      (consumedBits (n:=n) p (state c)) e=debits e)
    (credits : ∀ c, (∑ j,inst j (c j)) = G.chordWidths
      (OuterBank.resourceBits (kind bank p (state c)) (installedBits (n:=n) p (state c))))
    (before : ∀ c, ∀ i : Fin g, (state c (bank.base+i.val)).val = stock i)
    (fund : ∀ i,debits i ≤ stock i) (sep : bank.base+g ≤ src)
    (room : ∀ c i,stock i + OuterBank.resourceBits (kind bank p (state c))
      (installedBits (n:=n) p (state c)) i<2^W) :
    Round F (G.chordWidths stock) (∀j,J j)
      (fun c=>G.chordWidths (RepairHistogram.raw bank p src n (state c))) := by
  have allocated : (∑ j,demand j) ≤ G.chordWidths stock := debited ▸ chordWidths_le G fund
  have realise (c : ∀j,J j) : (G.chordWidths stock - ∑ j,demand j) + ∑ j,inst j (c j) =
      G.chordWidths (RepairHistogram.raw bank p src n (state c)) := by
    let gain : Fin g → ℕ := OuterBank.resourceBits (kind bank p (state c)) (installedBits (n:=n) p (state c))
    have law (i : Fin g) : stock i+gain i=RepairHistogram.raw bank p src n (state c) i+debits i := by
      have H := RepairHistogram.balance bank p src n (state c) i sep
        (by rw [selected c i,before c i]; exact fund i)
        (by rw [before c i]; exact room c i)
      simpa only [before c i,selected c i,gain] using H
    have parallel := congrArg G.chordWidths (funext law)
    rw [chordWidths_add,chordWidths_add,←debited,←credits c] at parallel
    apply add_right_cancel (b:=∑ j,demand j)
    calc
      _ = (G.chordWidths stock-∑ j,demand j + ∑ j,demand j) + ∑ j,inst j (c j) := by ac_rfl
      _ = _ := (congrArg (· + ∑ j,inst j (c j)) (tsub_add_cancel_of_le allocated)).trans parallel
  exact (funext realise) ▸ repair _ demand inst allocated tiles

/-- A consumed or installed row is either a named commodity with a measured
canonical ordinal, or an ordinary physical edge. Its entire width is placed
in exactly one of the two graphs, even when many rows name one commodity. -/
theorem split_occurrences {R I : Type} [Fintype R] [Fintype I]
    (G : PortGraph (Fin S) I) (key : R→Option I) (bits : R→ℕ) (one : R→Widths S)
    (located : ∀r i,key r=some i→ one r=pairWidth (G.tail i) (G.head i)) :
    (∑r,bits r • one r) = G.chordWidths (OuterBank.resourceBits key bits) +
      ∑ r,if key r=none then bits r • one r else 0 := by
  classical
  simp only [PortGraph.chordWidths,chordWidth_scaled,OuterBank.resourceBits,Finset.sum_smul]
  rw [Finset.sum_comm,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  cases h : key r with
  | none => simp []
  | some i => simp [located r i h,ite_smul]

/-- A mixed repair puts surviving commodity bits back in the live stock bank,
places paid links (including broadcasts) on the permanent graph, and debits
the fixed public catalyst reserve. All three components share the same
named-site tensor. Parallel and repeated resource incidences are summed. -/
def passive {A : Type} [Fintype A] (G : PortGraph (Fin S) (Fin g)) (K : PortGraph (Fin S) A)
    (carried : Widths S) (stock debits : Fin g→ℕ) (reserve consume : A→ℕ) :=
  carried+G.chordWidths (fun i=>stock i-debits i)+K.chordWidths (fun a=>reserve a-consume a)

omit [(j : Fin t) → Fintype (J j)] in
theorem mixed_shapes {A E : Type} [Fintype A] [Fintype E]
    (G : PortGraph (Fin S) (Fin g)) (K : PortGraph (Fin S) A) (P : PortGraph (Fin S) E)
    (bank : Bank) (p : Columns) (src : ℕ) (state : (∀j,J j)→Memory W)
    (stock debits : Fin g→ℕ) (reserve consume : A→ℕ) (paid : (∀j,J j)→E→ℕ)
    (carried : Widths S) (demand : Fin t→Widths S) (inst : ∀j,J j→Widths S)
    (sourceShape : (∑j,demand j)=G.chordWidths debits+K.chordWidths consume)
    (targetShape : ∀c,(∑j,inst j (c j)) =
      G.chordWidths (OuterBank.resourceBits (kind bank p (state c)) (installedBits (n:=n) p (state c)))+
        P.chordWidths (paid c))
    (selected : ∀ c e,OuterBank.resourceBits (kind bank p (state c)) (consumedBits (n:=n) p (state c)) e=debits e)
    (before : ∀c,∀i : Fin g,(state c (bank.base+i.val)).val=stock i)
    (fund : ∀ i,debits i ≤ stock i) (held : ∀a,consume a≤reserve a) (sep : bank.base+g ≤ src)
    (room : ∀c i,stock i+OuterBank.resourceBits (kind bank p (state c))
      (installedBits (n:=n) p (state c)) i<2^W) :
    let rest := passive G K carried stock debits reserve consume
    rest+∑j,demand j = carried+G.chordWidths stock+K.chordWidths reserve ∧
    ∀ c : ∀j,J j, rest+∑j,inst j (c j) =
      carried+P.chordWidths (paid c)+G.chordWidths (RepairHistogram.raw bank p src n (state c))+
        K.chordWidths (fun a=>reserve a-consume a) := by
  let rem := fun i=>stock i-debits i
  let free := fun a=>reserve a-consume a
  let rest := carried+G.chordWidths rem+K.chordWidths free
  have returnStock : G.chordWidths rem+G.chordWidths debits=G.chordWidths stock := by
    rw [←chordWidths_add]
    exact congrArg G.chordWidths (funext fun i=>Nat.sub_add_cancel (fund i))
  have returnCap : K.chordWidths free+K.chordWidths consume=K.chordWidths reserve := by
    rw [←chordWidths_add]
    exact congrArg K.chordWidths (funext fun a=>Nat.sub_add_cancel (held a))
  have entry : rest+∑j,demand j=carried+G.chordWidths stock+K.chordWidths reserve := by
    rw [sourceShape,←returnStock,←returnCap]
    dsimp [rest]
    ac_rfl
  have terminal (c : ∀j,J j) : rest+∑j,inst j (c j) =
      carried+P.chordWidths (paid c)+G.chordWidths (RepairHistogram.raw bank p src n (state c))+
        K.chordWidths free := by
    let gain : Fin g → ℕ := OuterBank.resourceBits (kind bank p (state c)) (installedBits (n:=n) p (state c))
    have credit : G.chordWidths rem + G.chordWidths gain=G.chordWidths (RepairHistogram.raw bank p src n (state c)) := by
      rw [←chordWidths_add]
      apply congrArg G.chordWidths
      funext i
      have bal := RepairHistogram.balance bank p src n (state c) i sep
        (by rw [selected c i,before c i]; exact fund i)
        (by rw [before c i]; exact room c i)
      rw [before c i,selected c i] at bal
      change stock i+gain i=_+debits i at bal
      change stock i-debits i+gain i=_
      have := fund i
      omega
    rw [targetShape,←credit]
    change (carried+G.chordWidths rem+K.chordWidths free)+(G.chordWidths gain+P.chordWidths (paid c))=_
    ac_rfl
  exact ⟨entry,terminal⟩

def mixed_repair {A E : Type} [Fintype A] [Fintype E]
    (G : PortGraph (Fin S) (Fin g)) (K : PortGraph (Fin S) A) (P : PortGraph (Fin S) E)
    (bank : Bank) (p : Columns) (src : ℕ) (state : (∀j,J j)→Memory W)
    (stock debits : Fin g→ℕ) (reserve consume : A→ℕ) (paid : (∀j,J j)→E→ℕ)
    (carried : Widths S) (demand : Fin t→Widths S) (inst : ∀j,J j→Widths S)
    (tiles : ∀j,Expansion (ChordGraph.raw F (demand j)) (J j) (inst j))
    (sourceShape : (∑j,demand j)=G.chordWidths debits+K.chordWidths consume)
    (targetShape : ∀c,(∑j,inst j (c j)) =
      G.chordWidths (OuterBank.resourceBits (kind bank p (state c)) (installedBits (n:=n) p (state c)))+
        P.chordWidths (paid c))
    (selected : ∀ c e,OuterBank.resourceBits (kind bank p (state c)) (consumedBits (n:=n) p (state c)) e=debits e)
    (before : ∀c,∀i : Fin g,(state c (bank.base+i.val)).val=stock i)
    (fund : ∀ i,debits i ≤ stock i) (held : ∀a,consume a≤reserve a) (sep : bank.base+g ≤ src)
    (room : ∀c i,stock i+OuterBank.resourceBits (kind bank p (state c))
      (installedBits (n:=n) p (state c)) i<2^W) :
    Round F (carried+G.chordWidths stock+K.chordWidths reserve) (∀j,J j)
      (fun c=>carried+P.chordWidths (paid c)+G.chordWidths (RepairHistogram.raw bank p src n (state c))+
        K.chordWidths (fun a=>reserve a-consume a)) := by
  obtain ⟨entry,terminal⟩ := mixed_shapes (n:=n) G K P bank p src state stock debits reserve consume
    paid carried demand inst sourceShape targetShape selected before fund held sep room
  let rest := passive G K carried stock debits reserve consume
  exact entry ▸ (funext terminal) ▸ withRemainder demand inst tiles rest rest (restrict_refl _)


end Hierarchy.WireTelescope

end
end OAI
