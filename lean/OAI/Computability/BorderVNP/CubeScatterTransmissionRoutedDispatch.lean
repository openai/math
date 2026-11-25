import OAI.Computability.BorderVNP.CubeScatterTransmissionRouted

/-! # Reading the complete routed transmission in the native callback order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.Assignment.Routed

open Physical Physical.NativeAssignments

variable {n d blocks b h K s : ℕ} {Team : Type*} [DecidableEq Team]
variable (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
variable (code : Team ↪ ℕ) (layouts : Team → TeamRowPrepare.Layout) (packetBase singleBase : Team → ℕ)

/-- Chronological private word consumed by the native row dispatcher for this team. -/
def dispatchWord (q : NativeAssignments.Routed (b := b) (s := s) owners) (t : Team) : List Bool :=
  TeamRows.choices (layouts t) (TeamRows.wordOwner (code ∘ owners q.1))
    ((bankData q.2 (packetBase t) (singleBase t)).privateTapeAt (layouts t))

/-- The raw private part of the complete encoding equals the literal physical callback tape. -/
theorem encode_tapes (dims : ∀ t, (layouts t).d = d) (ids : ∀ t, (layouts t).teamID = code t)
    (q : NativeAssignments.Routed (b := b) (s := s) owners) :
    (encode owners q).tapes = dispatchWord owners code layouts packetBase singleBase q := by
  funext t
  exact nativeWordsEquiv_teamRows code q.2 t (layouts t) (dims t) (ids t) (packetBase t) (singleBase t)

/-- Literal observation of an execution at the common transmission and all private callback tapes. -/
def Realizes (q : NativeAssignments.Routed (b := b) (s := s) owners) (z : Words n d Team) : Prop :=
  trueDeclaration b s q.1 = z.declaration ∧
    sharedWords (trueDeclaration b s q.1) (physicalShared owners q) = z.shared ∧
    dispatchWord owners code layouts packetBase singleBase q = z.tapes

/-- Replacing the semantic coordinates by the exact row streams gives the same observable record. -/
theorem realizes_iff (dims : ∀ t, (layouts t).d = d) (ids : ∀ t, (layouts t).teamID = code t)
    (q : NativeAssignments.Routed (b := b) (s := s) owners) (z : Words n d Team) :
    Realizes owners code layouts packetBase singleBase q z ↔ encode owners q = z := by
  rw [Realizes,← encode_shared owners q,← encode_tapes owners code layouts packetBase singleBase dims ids q]
  change ((encode owners q).declaration = z.declaration ∧ _) ↔ _
  exact (Words.ext_iff (x := encode owners q) (y := z)).symm

/-- There is exactly one full routed assignment realizing the native shared
transmissions and actual private callbacks of a valid collection of tapes. -/
theorem accepts_iff_unique_dispatch (dims : ∀ t, (layouts t).d = d) (ids : ∀ t, (layouts t).teamID = code t)
    (z : Words n d Team) :
    Accepts b s owners z ↔ ∃! q, Realizes (b := b) (s := s) owners code layouts packetBase singleBase q z := by
  simp_rw [realizes_iff owners code layouts packetBase singleBase dims ids]
  exact accepts_iff_existsUnique owners z

/-- The inverse of the complete tape bijection gives the actual physical streams
and private callbacks and uniquely determines the routed evaluator input. -/
theorem recovered_dispatch (dims : ∀ t, (layouts t).d = d) (ids : ∀ t, (layouts t).teamID = code t)
    (z : {z : Words n d Team // Accepts b s owners z}) :
    let q := (wordsEquiv owners b s).symm z
    Realizes owners code layouts packetBase singleBase q z.val ∧
      ∀ q', Realizes owners code layouts packetBase singleBase q' z.val → q' = q := by
  intro q
  have eq : encode owners q = z.val := congrArg Subtype.val ((wordsEquiv owners b s).apply_symm_apply z)
  have ok := (realizes_iff owners code layouts packetBase singleBase dims ids q z.val).mpr eq
  exact ⟨ok,fun q' hq' => ((accepts_iff_unique_dispatch owners code layouts packetBase singleBase dims ids z.val).mp
    z.property).unique hq' ok⟩

/-- A raw broadcast whose decoded coordinate and dense rows supply a valid
transmission is the canonical binary broadcast of the recovered selectors. -/
theorem recovered_broadcast (z : {z : Words n d Team // Accepts b s owners z})
    (raw : Broadcast n d (declarationCap n d blocks b h s))
    (axis : readCode _ raw.1 = z.val.declaration.1.val)
    (rows : ∀ pair j, readCode _ (raw.2 pair j) = z.val.declaration.2 pair j) :
    let q := (wordsEquiv owners b s).symm z
    raw = broadcast b s q.1 := by
  intro q
  have eq : encode owners q = z.val := congrArg Subtype.val ((wordsEquiv owners b s).apply_symm_apply z)
  have decl : trueDeclaration b s q.1 = z.val.declaration := congrArg Words.declaration eq
  apply (passesBroadcast_iff ..).mp
  refine ⟨z.val.declaration.1,axis,?_⟩
  apply (passesLengths_iff ..).mpr
  change (z.val.declaration.1,fun pair j => readCode _ (raw.2 pair j)) = trueDeclaration b s q.1
  rw [decl]
  exact Prod.ext rfl (funext fun pair => funext (rows pair))

/-- A single decoded shared payload suffices to check the lengths of arbitrary
private tapes. Uniqueness of the common decoder transfers those lengths to
every possible witness in the definition of acceptance. -/
theorem accepts_of_decoded (z : Words n d Team) (a : DeclaredShared blocks b h K s z.declaration)
    (emits : sharedWords z.declaration a = z.shared)
    (sizes : ∀ t, (z.tapes t).length =
      (teamPrivateKeys b s a.1.val z.declaration.1 (owners a.1.val) t).length) : Accepts b s owners z := by
  have pass := emits ▸ sharedWords_accept z.declaration a
  refine ⟨pass,?_⟩
  intro a' emits' t
  have same := ((sharedWords_iff z.declaration z.shared).mp pass).unique emits' emits
  exact same ▸ sizes t

private theorem decoded_selector (q : NativeAssignments.Routed (b := b) (s := s) owners) {decl : LengthDeclaration n d}
    (a : DeclaredShared blocks b h K s decl) (declaration : decl = trueDeclaration b s q.1)
    (emits : sharedWords decl a = (encode owners q).shared) : a.1.val = q.1 := by
  subst decl
  have ok := sharedWords_accept _ (physicalShared owners q)
  have same := ((sharedWords_iff _ _).mp ok).unique (emits.trans (encode_shared owners q)) rfl
  exact congrArg (fun x => x.1.val) same

/-- An actual common decoder result and arbitrary proper-length private words
force exactly one complete routed assignment. Its selector tuple is precisely
the one decoded from the returned common RAM lists. -/
theorem unique_dispatch_of_decoded (dims : ∀ t, (layouts t).d = d) (ids : ∀ t, (layouts t).teamID = code t)
    (z : Words n d Team) (a : DeclaredShared blocks b h K s z.declaration)
    (emits : sharedWords z.declaration a = z.shared)
    (sizes : ∀ t, (z.tapes t).length =
      (teamPrivateKeys b s a.1.val z.declaration.1 (owners a.1.val) t).length) :
    ∃! q : NativeAssignments.Routed (b := b) (s := s) owners, q.1 = a.1.val ∧
      Realizes owners code layouts packetBase singleBase q z := by
  have ok := accepts_of_decoded owners z a emits sizes
  obtain ⟨q,real,unique⟩ := (accepts_iff_unique_dispatch owners code layouts packetBase singleBase dims ids z).mp ok
  have eq := (realizes_iff owners code layouts packetBase singleBase dims ids q z).mp real
  have sel := decoded_selector owners q a real.1.symm (emits.trans (congrArg Words.shared eq).symm)
  exact ⟨q,⟨sel.symm,real⟩,fun q' hq' => unique q' hq'.2⟩

end Cube.Scatter.Assignment.Routed

end BorderVNP
end Computability
end OAI
