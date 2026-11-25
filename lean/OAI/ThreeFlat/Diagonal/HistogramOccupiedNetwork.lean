import OAI.ThreeFlat.Diagonal.HistogramPartyPointers
import OAI.ThreeFlat.Diagonal.HistorySupplyPointers

namespace OAI
/-! # A physical ordered kernel for an occupied motif at one site -/

namespace ThreeFlat.Diagonal.HistogramTileNetwork

noncomputable section

open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector MotifKernel MotifOuterTerms MotifBinaryPacking
open scoped Classical BigOperators

variable {J E S H Z F : Type} [Field F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] [Fintype Z] [DecidableEq Z] {k d r s p c a : ℕ}
variable (D : PortGraph J E) (G : Supply J S) (place : J → Z) (v : Z)
  (w base : E → ℕ) (sw : H → S → ℕ) (code : H ↪ Fin (2^k)) (id : H ≃ Fin s) (z : Histogram H r)
  (edges : Fin a ≃ Absorbed (ports G) place v) (parts : Fin c ≃ {j // place j=v})

abbrev Label (z : Histogram H r) (sw : H → S → ℕ) (k : ℕ) (e : S) :=
  (Fin r → Fin (2^k)) × Fin (2^histWidth sw z e)

def order : PrivateOrder (ports G) place v (Label z sw k) where
  count := a
  edge := edges
  width e := histWidth sw z e + r*k
  binary e := (SlotRefinement.selectorWord r k (histWidth sw z e)).trans (word _).symm

variable {e n : Fin c → ℕ} (supply : ∀ i, Fin (e i) ≃ (ports G).Port (parts i).val)
  (demand : ∀ i, Fin (n i) ≃ D.Port (parts i).val)
  (fits : ∀ i q u, sw q (supply i u).1.1 ≤ d)
  (M : ∀ z j, D.State (fun e => Fin (2^base e)) j → (ports G).State (fun a => Fin (2^sw z a)) j → F)
  (C : BitNetwork F ((r*d)+(r*d+r*d))) (Ccount : BitNetwork F (r+(r+r)))

section
variable {place v}

def hd (i : Fin c) : Header (D.Port (parts i).val) H (fun q => base q.1.1) k (n i) := ⟨demand i,code⟩

abbrev localNet (i : Fin c) := partyNetwork D G (parts i).val base
    (hd D base code parts demand i) (supply i) sw (fits i) M id z C Ccount

end

variable (old : ∀ i, (q : D.Port (parts i).val) → Fin (w q.1.1) → BitSource (order G place v sw z edges (k:=k)).bits p)
  (cross : (x : ExternalAt (ports G) place v) → Fin (histWidth sw z x.val.val+r*k) → Fin p)

def localWire (i : Fin c) := partyPointer D G (parts i).val base w (hd D base code parts demand i)
  (supply i) sw z (old i) ((order G place v sw z edges (k:=k)).partySource cross (parts i)) (d:=d)

noncomputable def occupied := BitNetwork.Ordered.glue
  (fun i => localNet D G base sw code id z parts supply demand fits M C Ccount i)
  (localWire D G place v w base sw code z edges parts supply demand old cross)

omit [Nonempty J] [Fintype E] [Fintype Z] in
/-- Every occupied party reads the selected owner-local demand word and
the appropriate absorbed or crossing word. Summed variables are precisely
the binary encoding of the absorbed wires; inactive parties never occur. -/
theorem occupied_eval (hpad : ∀ x, w x ≤ base x*r)
    (hC : ∀ M X Y, C.eval (Fin.append M (Fin.append X Y)) = if Y=Routing.StableCompaction.compact M X then 1 else 0)
    (hcount : ∀ M X Y, Ccount.eval (Fin.append M (Fin.append X Y)) = if Y=Routing.StableCompaction.compact M X then 1 else 0)
    (pin : Fin p → Bool) (x : ∀ j, D.State (fun a => Fin (2^w a)) j)
    (shared : WiresAt (ports G).tail (ports G).head place (I:=Label z sw k) none)
    (oldOK : ∀ i q t g, (old i q t).read g pin = (x (parts i).val q).val.testBit t.val)
    (crossOK : ∀ a t, pin (cross a t) = (SlotRefinement.selectorWord r k _ (shared a.val)).val.testBit t.val) :
    (occupied D G place v w base sw code id z edges parts supply demand fits M C Ccount old cross).eval pin =
      groupedFactor (ports G) place (fun j => histogramKernel D G w base hpad sw code M z j (x j)) v shared := by
  unfold occupied
  apply group_network _ _ _ _ (order G place v sw z edges) parts
  intro i g
  let O := order G place v sw z edges (k:=k)
  let y := portAt (ports G) (parts i).val (atParty (ports G).tail (ports G).head place (parts i).val shared
    ((parts i).property.symm ▸ O.decode g))
  have readNew (q : (ports G).Port (parts i).val) (t : Fin (histWidth sw z q.1.1+r*k)) :
      (O.partySource cross (parts i) q t).read g pin = (SlotRefinement.selectorWord r k _ (y q)).val.testBit t.val :=
    O.partySource_read cross pin g shared crossOK (parts i) q t
  rw [show (fun j => (localWire D G place v w base sw code z edges parts supply demand old cross i j).read g pin) = _ from
    partyPointer_read D G (parts i).val base w (hd D base code parts demand i) (supply i) sw z (old i) _ hpad pin g
      (x (parts i).val) y (fun a b => oldOK i a b g) readNew]
  exact party_eval D G (parts i).val base (hd D base code parts demand i) (supply i) sw (fits i) M id z C Ccount
    w hpad hC hcount _ _

end

end ThreeFlat.Diagonal.HistogramTileNetwork

end OAI
