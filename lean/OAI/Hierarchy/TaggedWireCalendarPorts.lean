import OAI.Hierarchy.TaggedWireHistoryRoles

namespace OAI
/-! # One immutable public site port per chronological state bit -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open LinearAlgebra.SpectralBooks ChordGraph ProtocolRAM.Calendar
open scoped Classical BigOperators

variable {S : ℕ} {X Q : Type} (slot : Event→Slot X) (wire : X→Widths S)
variable (cells : ∀x,(Σs,SiteBit (wire x) s) ↪ Q)

private def distribute {I : Type} (A B : I→Type) : (Σs,A s ⊕ B s) ≃ (Σs,A s) ⊕ (Σs,B s) where
  toFun | ⟨s,.inl a⟩=>.inl ⟨s,a⟩ | ⟨s,.inr b⟩=>.inr ⟨s,b⟩
  invFun | .inl ⟨s,a⟩=>⟨s,.inl a⟩ | .inr ⟨s,b⟩=>⟨s,.inr b⟩
  left_inv := by rintro ⟨s,(a|b)⟩ <;> rfl
  right_inv := by rintro (⟨s,a⟩|⟨s,b⟩) <;> rfl

private def prepend {n : ℕ} : Q ⊕ (Fin n × Q) ↪ Fin (n+1) × Q where
  toFun | .inl q=>(0,q) | .inr (i,q)=>(i.succ,q)
  inj' := by
    rintro (q|⟨i,q⟩) (p|⟨j,p⟩) eq
    · exact congrArg Sum.inl (congrArg Prod.snd eq)
    · exact (Fin.succ_ne_zero _ (congrArg Prod.fst eq).symm).elim
    · exact (Fin.succ_ne_zero _ (congrArg Prod.fst eq)).elim
    · change (i.succ,q)=(j.succ,p) at eq
      obtain ⟨hi,hq⟩:=Prod.mk.inj eq
      exact congrArg Sum.inr (Prod.ext (Fin.succ_inj.mp hi) hq)

/-- Time zero receives the actual first state; the unique occurrence of a
later state is shared by its incoming and outgoing local operators. -/
def timeline : ∀es x (j : Path slot es x),
    PartyBit slot wire es x j ↪ Fin (es.length+1) × Q
  | [],x,_=>
    let first : PartyBit slot wire [] x PUnit.unit ↪ Σs,SiteBit (wire x) s :=
      (Equiv.sigmaCongrRight (fun s=>Equiv.sumEmpty (SiteBit (wire x) s) Empty)).toEmbedding
    (first.trans (cells x)).trans (Function.Embedding.sectR (0 : Fin 1) _)
  | e::es,x,j=>
    (distribute _ _).toEmbedding.trans
      (((cells x).sumMap (timeline es ((slot e).next x j.1) j.2)).trans prepend)

theorem timeline_head (es : List Event) (x : X) (j : Path slot es x) (s : Fin S) (b : SiteBit (wire x) s) :
    timeline slot wire cells es x j ⟨s,.inl b⟩=(0,cells x ⟨s,b⟩) := by cases es <;> rfl

theorem timeline_tail (e : Event) (es : List Event) (x : X) (j : Path slot (e::es) x)
    (s : Fin S) (b : LaterBit slot wire s (e::es) x j) :
    let rest:=timeline slot wire cells es ((slot e).next x j.1) j.2 ⟨s,b⟩
    timeline slot wire cells (e::es) x j ⟨s,.inr b⟩=(rest.1.succ,rest.2) := rfl

theorem timeline_site (parent : Q→Fin S) (atSite : ∀x a,parent (cells x a)=a.1) :
    ∀es x j (b : PartyBit slot wire es x j),parent (timeline slot wire cells es x j b).2=b.1
  | [],x,_j,⟨s,.inl b⟩=>atSite x ⟨s,b⟩
  | [],_,_,⟨_,.inr v⟩=>nomatch v
  | _::_,x,_,⟨s,.inl b⟩=>atSite x ⟨s,b⟩
  | e::es,x,j,⟨s,.inr b⟩=>timeline_site parent atSite es ((slot e).next x j.1) j.2 ⟨s,b⟩

def timelineFin [Fintype Q] (es : List Event) (x : X) (j : Path slot es x) :
    PartyBit slot wire es x j ↪ Fin ((es.length+1)*Fintype.card Q) :=
  (timeline slot wire cells es x j).trans (((Equiv.refl _).prodCongr (Fintype.equivFin Q)).trans finProdFinEquiv).toEmbedding

theorem sum_timeline [Fintype Q] {F : Type*} [CommSemiring F] (es : List Event) (x : X) (j : Path slot es x)
    (φ : (Fin ((es.length+1)*Fintype.card Q)→Bool)→F) :
    let live:=timelineFin slot wire cells es x j
    (∑a,if ∀i,a i=true→i∈Set.range live then φ a else 0)=
      ∑z : SiteChoices slot wire es x j,φ (placedBits slot wire es x j live z) :=
  sum_party_states slot wire es x j _ _

end Hierarchy.WireTelescope.CalendarTape

namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph WireTelescope CalendarTape AdaptiveProbe ReportSockets
open scoped Classical BigOperators

variable {h W k attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
  (marked : Marks h W k attempts) (unique : Exclusive marked)

def statePlace {n : ℕ} (rows : Fin n≃Source S π depth marked) (bits : Fin n→ℕ)
    (cap : Public S h W k attempts→ℕ) (fit : ∀i side,bits i≤cap (named S π depth marked unique rows (i,side))) :
    (Σs,SiteBit (installedWidths (sorted S π depth marked ∘ rows) bits) s) ↪ (Σp,Fin (cap p)) :=
  NamedAperture.place _ bits (named S π depth marked unique rows) cap fit

theorem statePlace_site {n : ℕ} (rows : Fin n≃Source S π depth marked) (bits : Fin n→ℕ)
    (cap : Public S h W k attempts→ℕ) (fit : ∀i side,bits i≤cap (named S π depth marked unique rows (i,side)))
    (a : Σs,SiteBit (installedWidths (sorted S π depth marked ∘ rows) bits) s) :
    name (site S (statePlace S π depth marked unique rows bits cap fit a).1)=a.1 :=
  NamedAperture.owned _ bits _ cap fit (fun p=>name (site S p)) (named_site S π depth marked unique rows) a

private theorem sum_capped {I : Type} (sumEnum cardEnum : Fintype I) (value : I→ℕ) (bound count : ℕ)
    (fee : ∀i,value i≤bound) (room : @Fintype.card I cardEnum≤count) :
    (@Finset.univ I sumEnum).sum value≤count*bound := by
  cases Subsingleton.elim cardEnum sumEnum
  let := sumEnum
  calc
    _ ≤ ∑_i : I,bound := Finset.sum_le_sum fun i _=>fee i
    _ = Fintype.card I*bound := by simp
    _ ≤ _ := Nat.mul_le_mul_right bound room

theorem local_capacity (cap : Public S h W k attempts→ℕ) (B : ℕ) (fit : ∀p,cap p≤B) (v : Site h (2^W) k) :
    (∑p : Incident.Fiber (site S (attempts:=attempts)) v,cap p.val) ≤
      (Incident.room k S.degree attempts+(1+2*k)+1)*B := by
  let I := Incident.Fiber (site S (h:=h) (W:=W) (k:=k) (attempts:=attempts)) v
  have count := HistoryRoles.site_card (h:=h) (W:=W) (k:=k) (attempts:=attempts) S v
  exact sum_capped (I:=I) _ _ (fun p=>cap p.val) B _ (fun p=>fit p.val) count

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end
end OAI
