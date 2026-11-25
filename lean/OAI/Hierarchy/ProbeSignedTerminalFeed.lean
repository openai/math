import OAI.Hierarchy.ProbeSignedTerminal

namespace OAI
/-! # Actual source, tree selector, ordinary role and binary counter pin addresses -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Routing Diagonal MotifOuterTerms MotifBinaryPacking TraceCircuit
open scoped Classical BigOperators Fin.CommRing

variable {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B] {k r pub cap : ℕ}
  [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}

namespace SiteHardware
variable {i : Fin k}

abbrev Open (i : Fin k) (cap pub : ℕ) := BitSource (Fintype.card (Sockets i)*cap) pub

def tap (i : Fin k) (s : Sockets i) (j : ℕ) : Open i cap pub :=
  if h : j<cap then .hidden (finProdFinEquiv ((Fintype.equivFin _ s),⟨j,h⟩)) else .constant false

def «public» (u : Fin pub⊕Bool) : Open i cap pub := Sum.elim .pin .constant u

def halves {a g : Widths k} (i : Fin k) (x : State a i) (z : State g i) :
    Fin (Fintype.card (Sockets i)*cap)→Bool :=
  blocks _ _ (fun s j=>Sum.elim (fun p=>(x p).val.testBit j.val)
    (fun p=>(z p).val.testBit j.val) ((Fintype.equivFin (Sockets i)).symm s))

omit [Nonempty (Fin k)] in
theorem tap_read {a g : Widths k} (i : Fin k) (x : State a i) (z : State g i)
    (v : Fin pub→Bool) (s : Sockets i) (j : ℕ) (room : j<cap) :
    (tap i s j).read (halves (cap:=cap) i x z) v =
      Sum.elim (fun p=>(x p).val.testBit j) (fun p=>(z p).val.testBit j) s := by
  simp [tap,halves,room,BitSource.read]

omit [Nonempty (Fin k)] in
theorem public_read (u : Fin pub⊕Bool) (v : Fin pub→Bool) (raw : Fin (Fintype.card (Sockets i)*cap)→Bool) :
    («public» (i:=i) u).read raw v=Sum.elim v id u := by cases u <;> rfl
end SiteHardware

open SiteHardware (word_bit)

private theorem flat_word {a b : ℕ} (c : Fin (2^(a*b))) (i : Fin a) (j : Fin b) :
    (blocks a b).symm ((word _).symm c) i j=c.val.testBit (finProdFinEquiv (i,j)).val := by
  have e:=congrFun ((blocks a b).apply_symm_apply ((word _).symm c)) (finProdFinEquiv (i,j))
  simpa only [blocks_at,word_bit] using e

variable (P : Packet F edge req) (G : PortGraph (Fin k) B)
  (i : Fin k) (p : (portGraph k).Port i)

/-- A public linear aperture that accommodates the entire selector suffix
and all ordinary input/output digits, before reading any histogram. -/
def Packet.aperturePerCopy (P : Packet F edge req) (B : Type) [Fintype B] (i : Fin k) :=
  Fintype.card B*P.selectorBits+SiteHardware.widthCap (SiteHardware.localWidth P i)

omit [Nonempty (Fin k)] in
theorem Packet.aperture_room (P : Packet F edge req) (G : PortGraph (Fin k) B) (i : Fin k)
    (s : (portGraph k).Port i) (r : ℕ) :
    G.chordWidths (fun _=>r*P.selectorBits) s.val.1+
      r*SiteHardware.widthCap (SiteHardware.localWidth P i)≤r*P.aperturePerCopy B i := by
  let t:=r*P.selectorBits
  have one (e : B) : G.chordWidth e t s.val.1≤t := by
    unfold PortGraph.chordWidth
    split_ifs <;> simp [Finsupp.single_apply] <;> split_ifs <;> omega
  have all : G.chordWidths (fun _=>t) s.val.1≤Fintype.card B*t := by
    simp only [PortGraph.chordWidths,Finsupp.finsetSum_apply]
    exact (Finset.sum_le_sum (fun e _=>one e)).trans_eq (by simp)
  rw [Packet.aperturePerCopy,Nat.mul_add]
  exact Nat.add_le_add_right (all.trans_eq (by dsimp [t];ac_rfl)) _

def Packet.localTap (i : Fin k) (p : (portGraph k).Port i) (q : Widths k) :
    SiteHardware.LocalPins P i r→SiteHardware.Open i cap pub
  | .inl jt => SiteHardware.tap i (.inr p) (finProdFinEquiv jt).val
  | .inr (.inl s,j) => SiteHardware.tap i (.inl s) j.val
  | .inr (.inr s,j) => SiteHardware.tap i (.inr s) (q s.val.1+j.val)

def Packet.terminalFeed (_fit : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) p.val.1)
    (counter : Fin P.terms→Fin (Nat.clog 2 (r+1))→Fin pub⊕Bool) :
    Fin (Fintype.card (BroadcastPins.Bits (G.chordWidths (fun _=>r*P.selectorBits)) i)+
      ((r*P.selectorBits+P.terms*Nat.clog 2 (r+1))+Fintype.card (SiteHardware.LocalPins P i r)))→
      SiteHardware.Open i cap pub :=
  let q:=G.chordWidths (fun _=>r*P.selectorBits)
  let selector (j : Fin (r*P.selectorBits)) : SiteHardware.Open i cap pub:=SiteHardware.tap i (.inr p) j.val
  let tree (j : Fin (Fintype.card (BroadcastPins.Bits q i))) : SiteHardware.Open i cap pub :=
    let b:=(Fintype.equivFin (BroadcastPins.Bits q i)).symm j
    SiteHardware.tap i (.inr b.1) b.2.val
  let fields (j : Fin (P.terms*Nat.clog 2 (r+1))) : SiteHardware.Open i cap pub :=
    let ab:=finProdFinEquiv.symm j
    SiteHardware.«public» (counter ab.1 ab.2)
  Fin.append tree (Fin.append (Fin.append selector fields) (P.localTap i p q ∘ (Fintype.equivFin _).symm))

omit [Nonempty (Fin k)] in
private theorem code_at {t : ℕ} (a q : Widths k) (i : Fin k) (p : (portGraph k).Port i)
    (fit : t≤q p.val.1) (z : State (a+q) i) (j : Fin t) :
    (BroadcastPins.candidate q i p (splitPortState a q i z).2 t).val.testBit j.val=(z p).val.testBit j.val := by
  change (((splitPortState a q i z).2 p).val%2^t).testBit j.val=_
  simp only [Nat.testBit_mod_two_pow,j.isLt,decide_true,Bool.true_and]
  exact split_selector_bit a q i z p ⟨j.val,j.isLt.trans_le fit⟩

theorem Packet.terminalFeed_value (rt : Fin k) (h : Histogram (Fin P.terms) r)
    (fit : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) p.val.1)
    (counter : Fin P.terms→Fin (Nat.clog 2 (r+1))→Fin pub⊕Bool)
    (v : Fin pub→Bool) (x : State (P.inputWidths r) i)
    (z : State (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits)) i)
    (capRoom : ∀s : (portGraph k).Port i,G.chordWidths (fun _=>r*P.selectorBits) s.val.1+
      r*SiteHardware.widthCap (SiteHardware.localWidth P i)≤cap)
    (meter : ∀a j,Sum.elim v id (counter a j)=SelectorShelf.bits h _ a j) :
    (P.terminal G i p fit).eval (fun t=>(P.terminalFeed G i p fit counter t).read
      (SiteHardware.halves (cap:=cap) i x z) v)=P.broadcastMatrix rt r G h i x z := by
  let q:=G.chordWidths (fun _=>r*P.selectorBits)
  let yz:=splitPortState (P.outputWidths h) q i z
  let c:=BroadcastPins.candidate q i p yz.2 (r*P.selectorBits)
  have qroom (s : (portGraph k).Port i) : q s.val.1≤cap := (Nat.le_add_right _ _).trans (capRoom s)
  have rootBit (j : Fin (r*P.selectorBits)) : (SiteHardware.tap i (.inr p) j.val).read
      (SiteHardware.halves (cap:=cap) i x z) v=((word _).symm c) j := by
    rw [SiteHardware.tap_read i x z v _ _ (j.isLt.trans_le (fit.trans (qroom p))),word_bit]
    exact (code_at (P.outputWidths h) q i p fit z j).symm
  rw [←P.terminal_eval rt G h i p fit x z]
  apply congrArg (P.terminal G i p fit).eval
  funext t
  refine Fin.addCases (fun l=>?_) (fun t=>Fin.addCases (fun t=>?_) (fun u=>?_) t) t
  · let b:=(Fintype.equivFin (BroadcastPins.Bits q i)).symm l
    simp only [terminalFeed,Fin.append_left]
    change (SiteHardware.tap i (.inr b.1) b.2.val).read _ v=(yz.2 b.1).val.testBit b.2.val
    rw [SiteHardware.tap_read i x z v _ _ (b.2.isLt.trans_le (qroom b.1))]
    exact (split_selector_bit _ _ _ _ _ b.2).symm
  · refine Fin.addCases (fun l=>?_) (fun f=>?_) t
    · simp only [terminalFeed,Fin.append_right,Fin.append_left,SelectorShelf.pins,Equiv.apply_symm_apply]
      exact rootBit l
    · obtain ⟨⟨a,j⟩,rfl⟩:=finProdFinEquiv.surjective f
      simp [terminalFeed,SelectorShelf.pins,SiteHardware.public_read,meter,-Fin.natAdd_eq_addNat]
      exact congrArg (fun t : Fin P.terms × Fin (Nat.clog 2 (r+1)) =>
        SelectorShelf.bits h _ t.1 t.2) (finProdFinEquiv.symm_apply_apply (a,j))
  · let b:=(Fintype.equivFin (SiteHardware.LocalPins P i r)).symm u
    simp only [terminalFeed,Fin.append_right,Function.comp_apply]
    change (P.localTap i p q b).read (SiteHardware.halves (cap:=cap) i x z) v=P.rawSiteView h i c x yz.1 b
    cases eq:b with
    | inl jt =>
      rcases jt with ⟨a,j⟩
      simpa only [Packet.localTap,Packet.rawSiteView,word_bit,flat_word] using rootBit (finProdFinEquiv (a,j))
    | inr sj =>
      rcases sj with ⟨s,j⟩
      cases s with
      | inl s =>
        apply SiteHardware.tap_read i x z v (.inl s) j.val
        have m:=capRoom s
        omega
      | inr s =>
        change (SiteHardware.tap i (.inr s) (q s.val.1+j.val)).read _ v=(yz.1 s).val.testBit j.val
        rw [SiteHardware.tap_read i x z v _ _ (lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) (capRoom s))]
        exact (split_payload_bit _ _ _ _ _ _).symm

/-- All local sockets are wired at actual fixed bit offsets. A caller supplies
the low control words and the stable packer's scalar bit readings on the
genuine original half-ports. No equality of circuit values is assumed. -/
theorem Packet.signed (rt : Fin k) (h : Histogram (Fin P.terms) r) {n d b : ℕ}
    (fit : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) p.val.1)
    (counter : Fin P.terms→Fin (Nat.clog 2 (r+1))→Fin pub⊕Bool)
    (S : ApertureCompactor.SocketRight (Fintype.card (SiteHardware.Sockets i)) n d b pub)
    (v : Fin pub→Bool) (width : Fin (Fintype.card (SiteHardware.Sockets i))→Fin n→ℕ)
    (raw : Fin (Fintype.card (SiteHardware.Sockets i))→Fin (n*d)→Bool)
    (x : State (P.inputWidths r) i) (z : State (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits)) i)
    (bound : ∀s a,width s a≤d) (room : d<2^b)
    (addr : ∀s j,Sum.elim v id (S.widths s j)=blocks n b (fun a=>TraceWords.bits (width s a:Computability.VPVNP.BurstRAM.Word b)) j)
    (input : ∀s j,Sum.elim v id (S.inputs s j)=raw s j)
    (capRoom : ∀s : (portGraph k).Port i,G.chordWidths (fun _=>r*P.selectorBits) s.val.1+
      r*SiteHardware.widthCap (SiteHardware.localWidth P i)≤n*d)
    (meter : ∀a j,Sum.elim v id (counter a j)=SelectorShelf.bits h _ a j)
    (clean : ∀s,ApertureCompactor.canonical (width s) (raw s))
    (chord : ∀s j,Routing.StableCompaction.compact (ApertureMask.mask (width s)) (raw s) j=
      Sum.elim (fun p=>(x p).val.testBit j.val) (fun p=>(z p).val.testBit j.val)
        ((Fintype.equivFin (SiteHardware.Sockets i)).symm s)) :
    (S.attach (P.terminal G i p fit) (P.terminalFeed G i p fit counter)).eval v=P.broadcastMatrix rt r G h i x z := by
  rw [S.attach_value _ _ v width raw bound room addr input,ite_eq_left clean]
  have hs : blocks _ _ (fun s=>Routing.StableCompaction.compact (ApertureMask.mask (width s)) (raw s))=
      SiteHardware.halves (cap:=n*d) i x z := congrArg (blocks _ _) (funext (fun s=>funext (chord s)))
  rw [hs]
  exact P.terminalFeed_value G i p rt h fit counter v x z capRoom meter

end Hierarchy.Probe
end

end OAI
