import OAI.Hierarchy.DescentDatedRegisteredOperandTags
import OAI.Hierarchy.DescentOrdinaryArgumentsBefore
import OAI.Hierarchy.DescentDatedPublicGrain
import OAI.Hierarchy.DescentDatedOriginPlan

namespace OAI
/-! # From the actual operand gather through the eight route fields to the scalar resolver -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedPriorOperand DescentSIMDLookup DescentOperandVectorArena DescentOperandStateBanks
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) {D k K cap w : ℕ} (floor : ℕ)
def chosenGrain : Cell (v.resolver.size+2) := (DescentDatedPublicGrain.amount v.schedule v.gadget.b v.age:ℕ)
def nativeSide:=v.origin.side (v.routedStart floor)
def nativeRoute:=v.origin.route (v.routedStart floor)
def nativeArgs:=v.operandBanks floor (v.nativeSide floor) (v.nativeRoute floor)
def grainPhase (w : ℕ) : NativePhase w :=
  ⟨DescentDatedPublicGrain.program v.resolver w (v.origin.grainBase (v.routedStart floor)) v.chosenGrain,
   DescentDatedPublicGrain.ticks v.resolver,
   DescentDatedPublicGrain.image v.resolver (v.origin.grainBase (v.routedStart floor)) v.chosenGrain,
   DescentDatedPublicGrain.cheap v.resolver w _ v.chosenGrain⟩

abbrev OriginSources (v : PhysicalOrdinary F P) :=Fin v.resolver.jobs→Fin 8→Expr

def rasterPhase (src : OriginSources v) (w : ℕ) : NativePhase w :=
  let ps:=v.origin.outputs src (v.routedStart floor)
  ⟨program w ps,clock ps,result ps,@ProtocolRAM.program_cheap _ _⟩

def resolvePhase (w : ℕ) (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2) : NativePhase w :=
  let bounds:=v.origin.ports_fit (v.routedStart floor) w ((v.resolver.floor_le _).trans_lt fit)
  ⟨v.operandProgram (v.nativeArgs floor) w floor,v.operandTicks (v.nativeArgs floor) floor,
    v.operandState (v.nativeArgs floor) floor,
    (v.operand_any_from_vector floor _ _ (fun _=>0) shape bounds.1 bounds.2 fit wide).2.2⟩

/-- The field sources are read after the true vector gather and the original
preparation body. The sixth column has its own single padded bank. -/
def routedArguments (C : References v.vector D k K cap) (src : OriginSources v) (prepare : NativePhase w)
    (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2) : NativePhase w :=
  ((((C.phase w (v.vectorStart floor)).seq prepare).seq (v.grainPhase floor w)).seq (v.rasterPhase floor src w)).seq
      (v.resolvePhase floor w shape fit wide)

theorem routed_order :
    v.vectorStart floor≤v.routedStart floor ∧ v.routedStart floor≤v.origin.grainBase (v.routedStart floor) ∧
    v.origin.grainBase (v.routedStart floor)≤v.origin.outputBase (v.routedStart floor) ∧
    v.origin.outputBase (v.routedStart floor)≤v.normalizedEnd floor ∧ v.normalizedEnd floor≤v.endAddress floor :=by
  refine ⟨v.vector_before floor,Nat.le_add_right ..,Nat.le_add_right ..,?_,v.resolver.floor_le _⟩
  change _ ≤ v.routedStart floor+(v.origin.preparationWords+v.resolver.span+(v.resolver.jobs*8)*v.resolver.span)
  dsimp only [OriginPlan.outputBase,OriginPlan.grainBase]
  omega

theorem routed_run (C : References v.vector D k K cap) (src : OriginSources v) (prepare : NativePhase w)
    (gather : C.Room w (v.vectorStart floor)) (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (source : ∀j f,(src j f).Fits w (v.origin.outputBase (v.routedStart floor)))
    (cpu : ∀m,prepare.Runs m ∧ ∀i,i<v.routedStart floor ∨ v.origin.grainBase (v.routedStart floor)≤ i→prepare.image m i=m i)
    (m : Memory w) :
    (v.routedArguments floor C src prepare shape fit wide).Runs m ∧
    ∀i,i<v.vectorStart floor ∨ v.endAddress floor≤ i→(v.routedArguments floor C src prepare shape fit wide).image m i=m i:=by
  obtain ⟨a,b,c,d,e⟩:=v.routed_order floor
  let p:=C.phase w (v.vectorStart floor)
  let q:=v.grainPhase floor w
  let r:=v.rasterPhase floor src w
  have go:=C.any (v.vectorStart floor) m gather
  have early:=cpu (p.image m)
  let initial:=prepare.image (p.image m)
  have grain : q.Runs initial :=DescentDatedPublicGrain.run v.resolver _ v.chosenGrain initial (d.trans_lt (e.trans_lt fit))
  have raster:=v.origin.publish src (v.routedStart floor) (q.image initial) (e.trans_lt fit) source
  have ports:=v.origin.ports_fit (v.routedStart floor) w (e.trans_lt fit)
  have solve:=v.operand_any_from_vector floor _ _ (r.image (q.image initial)) shape ports.1 ports.2 fit wide
  constructor
  · exact NativePhase.seq_runs _ _ _ (NativePhase.seq_runs _ _ _ (NativePhase.seq_runs _ _ _
      (NativePhase.seq_runs _ _ _ go.1 early.1) grain) raster.1) solve.1
  · intro i hi
    have h₁:=go.2 i (hi.imp_right (((b.trans c).trans (d.trans e)).trans ·))
    have h₂:=early.2 i (hi.imp (·.trans_le a) ((c.trans (d.trans e)).trans ·))
    have h₃:=DescentDatedPublicGrain.frame v.resolver _ v.chosenGrain initial i
      (hi.imp (·.trans_le (a.trans b)) ((d.trans e).trans ·))
    have h₄:=raster.2.2.1 i (hi.imp (·.trans_le ((a.trans b).trans c)) (e.trans ·))
    have h₅:=solve.2.1 i (hi.imp_left (·.trans_le (((a.trans b).trans c).trans d)))
    exact h₅.trans (h₄.trans (h₃.trans (h₂.trans h₁)))

open DescentPriorOperandColumns DescentPackedColony

/-- Target digits of the real eight output columns in their physical order. -/
def routeTarget (s : Fin v.resolver.jobs→Fin v.resolver.hosts→Fin v.resolver.groups→Side v.resolver.size)
    (roles : Fin v.resolver.jobs→Fin 3→Fin v.resolver.hosts→Fin v.resolver.groups→Cell (v.resolver.size+2))
    (j : Fin v.resolver.jobs) (f : Fin 8) (h : Fin v.resolver.hosts) (g : Fin v.resolver.groups) : Cell (v.resolver.size+2) :=
  if hf:f.val<5 then (s j h g).digits ⟨f.val,by omega⟩ else roles j ⟨f.val-5,by omega⟩ h g

private theorem grain_digit {k : ℕ} (value : Cell (k+2)) (s : Side k) (f : Fin 6) (low : f.val < 5) :
    (DescentDatedPublicGrain.withGrain value s).digits f = s.digits f := by
  fin_cases f <;> first | rfl | exact False.elim ((by decide : ¬(5:ℕ)<5) low)

/-- Recover the route digits from native expressions before the grain and
field scans. The completed scalar keys include the mask on the final row. -/
theorem routed_keys_of_sources_tagged (C : References v.vector D k K cap) (src : OriginSources v)
    (prepare : NativePhase w) (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (m : Memory w) (books : Books v.resolver) (typed : BookTags books)
    (s : Fin v.resolver.jobs→Fin v.resolver.hosts→Fin v.resolver.groups→Side v.resolver.size)
    (roles : Fin v.resolver.jobs→Fin 3→Fin v.resolver.hosts→Fin v.resolver.groups→Cell (v.resolver.size+2))
    (digits : ∀j h g,11*(roles j 1 h g).val+(roles j 2 h g).val<2^(v.resolver.size+2))
    (pos : 0<v.resolver.lanes)
    (pages : ∀x p,Reads ((v.nativeArgs floor).previous x p) (books x p) v.resolver.lanes ((C.phase w (v.vectorStart floor)).image m))
    (preserved : ∀i,i<v.routedStart floor →prepare.image ((C.phase w (v.vectorStart floor)).image m) i=
        (C.phase w (v.vectorStart floor)).image m i)
    (bounded : ∀j f,(src j f).Fits w (v.origin.grainBase (v.routedStart floor)))
    (measured : ∀j f,DescentPackedZip.Source (src j f) (v.routeTarget s roles j f) v.resolver.lanes
      (prepare.image ((C.phase w (v.vectorStart floor)).image m))) :
    let raw:=decodedBooks books (fun j h g=>DescentDatedPublicGrain.withGrain v.chosenGrain (s j h g)) roles digits
    ∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) j)
      (fun h g=>DescentPackedOperand.word ((raw j).compiled h g)) v.resolver.lanes
      ((v.routedArguments floor C src prepare shape fit wide).image m) :=by
  intro raw
  obtain ⟨a,b,c,d,e⟩:=v.routed_order floor
  let T:=v.routedStart floor
  let G:=v.origin.grainBase T
  let O:=v.origin.outputBase T
  let gathered:=(C.phase w (v.vectorStart floor)).image m
  let initial:=prepare.image gathered
  let mid:=DescentDatedPublicGrain.image v.resolver G v.chosenGrain initial
  let out:=(v.rasterPhase floor src w).image mid
  have pre : ∀j f,(src j f).Fits w O:=fun j f=>ProtocolRAMGeneratedWrite.fits_mono _ c (bounded j f)
  have pub:=v.origin.publish src T mid (e.trans_lt fit) pre
  have scan : ∀j f,Reads (v.origin.page T j f) (v.routeTarget s roles j f) v.resolver.lanes out:=by
    intro j f p
    let row:=DescentSIMDLookup.row v.resolver.hosts v.resolver.groups v.resolver.lanes p
    exact (pub.2.1 j f row).trans <| (eval_below _ _ initial mid (bounded j f)
      (fun i hi=>DescentDatedPublicGrain.frame _ G _ initial i (.inl hi))).trans (measured j f p)
  have old : ∀x p,Reads ((v.nativeArgs floor).previous x p) (books x p) v.resolver.lanes out:=by
    intro x p row
    obtain ⟨port,capacity⟩:=from_previous_placed v.resolver v.vector (v.vectorStart floor)
      shape.operands shape.blocks shape.hosts shape.groups shape.lanes ((v.routed_le floor).trans_lt (e.trans_lt fit)) x p
    let addr:=((v.nativeArgs floor).previous x p).base+(DescentSIMDLookup.row _ _ _ row).val
    have below : addr<T:= (Nat.add_lt_add_left ((DescentSIMDLookup.row _ _ _ row).isLt.trans_le capacity) _).trans_le port.2.2
    exact (pub.2.2.1 addr (.inl (below.trans_le (b.trans c)))).trans <|
      (DescentDatedPublicGrain.frame _ G _ initial addr (.inl (below.trans_le b))).trans <|
      (preserved addr below).trans (pages x p row)
  have sides : ∀j f,Reads (v.nativeSide floor j f)
      (fun h g=>(DescentDatedPublicGrain.withGrain v.chosenGrain (s j h g)).digits f) v.resolver.lanes out:=by
    intro j f
    by_cases low:f.val<5
    · have q:=scan j ⟨f.val,by omega⟩
      have target : v.routeTarget s roles j ⟨f.val,by omega⟩ = fun h g => (s j h g).digits f := by
        funext h g
        exact dite_eq_left low
      simpa only [nativeSide,OriginPlan.side,T,dite_eq_left low,grain_digit _ _ _ low,target] using q
    · have last : f=5:=Fin.ext (by change f.val=5;omega)
      subst f
      intro p
      have lowAddr : (v.origin.grain T).base+(row _ _ _ p).val<O:=
        Nat.add_lt_add_left ((row _ _ _ p).isLt.trans_le (DescentDatedPublicGrain.capacity v.resolver G)) _
      exact (pub.2.2.1 _ (.inl lowAddr)).trans
        (DescentDatedPublicGrain.row_read v.resolver G v.chosenGrain initial p)
  have tags : ∀j f,Reads (v.nativeRoute floor j f) (roles j f) v.resolver.lanes out:=by
    intro j f
    have ge : ¬(Fin.natAdd 5 f).val < 5 := by simp [Fin.natAdd]
    have target : v.routeTarget s roles j (Fin.natAdd 5 f) = roles j f := by
      funext h g
      simp only [routeTarget,dite_eq_right ge]
      congr 2
      simp [Fin.natAdd]
    simpa only [nativeRoute,OriginPlan.route,T,target] using scan j (Fin.natAdd 5 f)
  have registered := registered_digits_tagged (v.nativeArgs floor) books
    (fun j h g=>DescentDatedPublicGrain.withGrain v.chosenGrain (s j h g)) roles digits
    typed out old sides tags
  have ports:=v.origin.ports_fit T w (e.trans_lt fit)
  exact Banks.run_words_tagged _ books _ roles digits _ (v.operand_early floor _ _ shape fit ports.1 ports.2)
    registered fit pos wide

theorem routed_keys_of_sources (C : References v.vector D k K cap) (src : OriginSources v)
    (prepare : NativePhase w) (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (m : Memory w) (books : Books v.resolver) (typed : BookPointers books)
    (s : Fin v.resolver.jobs→Fin v.resolver.hosts→Fin v.resolver.groups→Side v.resolver.size)
    (roles : Fin v.resolver.jobs→Fin 3→Fin v.resolver.hosts→Fin v.resolver.groups→Cell (v.resolver.size+2))
    (digits : ∀j h g,11*(roles j 1 h g).val+(roles j 2 h g).val<2^(v.resolver.size+2))
    (pos : 0<v.resolver.lanes)
    (pages : ∀x p,Reads ((v.nativeArgs floor).previous x p) (books x p) v.resolver.lanes ((C.phase w (v.vectorStart floor)).image m))
    (preserved : ∀i,i<v.routedStart floor →prepare.image ((C.phase w (v.vectorStart floor)).image m) i=
        (C.phase w (v.vectorStart floor)).image m i)
    (bounded : ∀j f,(src j f).Fits w (v.origin.grainBase (v.routedStart floor)))
    (measured : ∀j f,DescentPackedZip.Source (src j f) (v.routeTarget s roles j f) v.resolver.lanes
      (prepare.image ((C.phase w (v.vectorStart floor)).image m))) :
    let raw:=ofBooks books typed (fun j h g=>DescentDatedPublicGrain.withGrain v.chosenGrain (s j h g)) roles digits
    ∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) j)
      (fun h g=>DescentPackedOperand.word ((raw j).compiled h g)) v.resolver.lanes
      ((v.routedArguments floor C src prepare shape fit wide).image m) :=
  v.routed_keys_of_sources_tagged floor C src prepare shape fit wide m books typed.tags s roles digits pos
    pages preserved bounded measured

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
