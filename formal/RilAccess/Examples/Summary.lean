import RilAccess.Call.Summary

namespace RilAccess.CoreSummary.Examples

def saved : SourceInstance := ⟨⟨.allocation, 1⟩, 4, 1, 5⟩
def child : SourceInstance := ⟨⟨.module, 2⟩, 0, 2, 0⟩
def inserted : SourceInstance := ⟨⟨.allocation, 3⟩, 4, 3, 5⟩
def parameterCapture : SourceInstance := ⟨⟨.parameter, 7⟩, 4, 4, 5⟩
def sameObject : SourceInstance := { inserted with object := saved.object }
def heap : List HeapEdge := [⟨saved, 0, child⟩, ⟨child, 0, saved⟩]
def laterHeap : List HeapEdge := ⟨saved, 1, inserted⟩ :: heap
def arguments : List (Nat × List SourceInstance) := [(0, [saved])]
def emptyFrozen : CoreEntry.Frozen := ⟨[], [], by decide⟩
def freeze (sourceHeap : List HeapEdge) (args : List (Nat × List SourceInstance)) : CoreEntry.Frozen :=
  (CoreEntry.capturePrepared sourceHeap args).toOption.getD emptyFrozen

def capturedInstances (sourceHeap : List HeapEdge) (roots : List SourceInstance) : List SourceInstance :=
  (((freeze sourceHeap [(0, roots)]).snapshots.head?).map CoreEntry.Snapshot.srcInsts).getD []

def entries := freeze heap arguments
def parentAlias : SourceInstance := { saved with source := ⟨.capture, 98⟩ }
def conflictingContext : SourceInstance := { parentAlias with activation := 99 }

def actual : CallInstance :=
  ⟨(fun _ selection => if selection = 0 then saved else if selection = 1 then child else inserted),
    [1, 2, 3, 4], 9, 10⟩

def projected : Template := { rootReturn := [.parameter 0 1] }
def forged : Template := { rootReturn := [.parameter 0 2] }
def captured : Template := { createdEnvironments := [.concrete saved, .concrete parameterCapture] }
def allocatedReference : Reference := .allocated saved.source 0
def sharedAlloc : Template := { rootReturn := [allocatedReference], contained := [allocatedReference] }
def distinctAlloc : Template := { rootReturn := [allocatedReference, .allocated inserted.source 1] }
def collision : Template := { rootReturn := [allocatedReference, .allocated inserted.source 0] }
def allFields : Template :=
  ⟨[.parameter 0 0], [.parameter 0 1], [.parameter 0 1], [.concrete saved],
    [.concrete parameterCapture], [allocatedReference], [6]⟩

def pureConst : SourceInstance := ⟨⟨.module, 50⟩, 0, 50, 0⟩
def liveVar : SourceInstance := ⟨⟨.capture, 51⟩, 0, 51, 0⟩
def foreignHandle : SourceInstance := ⟨⟨.foreign, 52⟩, 0, 52, 0⟩
def pureLocal : SourceInstance := ⟨⟨.capture, 53⟩, 0, 53, 0⟩
def pureTable : List Source := [pureConst.source, parameterCapture.source, foreignHandle.source, pureLocal.source]
def emptySummary : Summary := ⟨[], [], [], [], [], [], []⟩
def pureReadSummary : Summary := { emptySummary with namedReads := [pureConst], createdEnvironments := [parameterCapture] }
def moduleReadSummary : Summary := { emptySummary with namedReads := [pureConst] }
def pureLocalReadSummary : Summary := { emptySummary with namedReads := [pureLocal, parameterCapture] }
def factorySummary : Summary := { emptySummary with createdEnvironments := [parameterCapture] }
def liveReadSummary : Summary := { emptySummary with namedReads := [liveVar] }
def foreignReadSummary : Summary := { emptySummary with namedReads := [foreignHandle] }
def writeSummary : Summary := { emptySummary with writes := [liveVar], effects := [6] }
def retainedSummary : Summary := { emptySummary with retained := [liveVar], effects := [6, 7] }
def pureReadTemplate : Template := { namedReads := [.concrete pureConst] }
def upperEffectTemplate : Template := { effects := [6, 7] }

def callbackModePairs : List (CallbackModeCall Nat String) :=
  [⟨0, [(0, some "Shared"), (1, some "Ref")], none⟩,
   ⟨0, [(0, some "Mut"), (1, some "Shared")], none⟩]

def crossedCallbackModePairs : List (CallbackModeCall Nat String) :=
  [⟨0, [(0, some "Shared"), (1, some "Shared")], none⟩,
   ⟨0, [(0, some "Mut"), (1, some "Ref")], none⟩]

def signatureCases : List (String × Bool × Bool) :=
  let writes := { emptySummary with writes := [liveVar] }
  let retains := { emptySummary with retained := [liveVar], contained := [liveVar] }
  let effects := { emptySummary with effects := [6] }
  let exact := Summary.exactSignature pureTable
  let subsumes := Summary.subsumes pureTable
  let widerRoot := { emptySummary with rootReturn := [saved, child] }
  let narrowerRoot := { emptySummary with rootReturn := [saved] }
  [("writable_parameter_compile_pass", exact writes writes, true),
   ("missing_write_clause", exact emptySummary writes, false),
   ("excessive_write_clause", exact writes emptySummary, false),
   ("retaining_a_writer_does_not_exercise_a_write_clause",
      exact { retains with writes := [liveVar] } retains, false),
   ("retaining_a_contained_writer_requires_its_state_clause",
      exact { retains with retained := [] } retains, false),
   ("a_pure_factory_declares_its_immutable_capture", exact factorySummary pureReadSummary, true),
   ("a_pure_factory_cannot_omit_its_immutable_capture", exact emptySummary pureReadSummary, false),
   ("an_environment_free_factory_cannot_declare_capture", exact factorySummary emptySummary, false),
   ("a_named_helper_can_declare_a_pure_capture", exact pureLocalReadSummary pureLocalReadSummary, true),
   ("a_named_helper_must_declare_its_capture", exact emptySummary pureLocalReadSummary, false),
   ("a_named_helper_cannot_declare_an_unused_pure_capture", exact pureLocalReadSummary emptySummary, false),
   ("a_module_constant_needs_no_captured_state_clause", exact emptySummary moduleReadSummary, true),
   ("immutable_return_source_requires_a_contained_dependency",
      exact emptySummary { emptySummary with contained := [parameterCapture] }, false),
   ("exact_io_asserted", exact effects effects, true),
   ("missing_io", exact emptySummary effects, false),
   ("a_named_function_cannot_declare_an_unused_effect", exact effects emptySummary, false),
   ("narrower_inferred_root_relation_is_compatible", subsumes widerRoot narrowerRoot, true),
   ("additional_inferred_root_breaks_compatibility", subsumes narrowerRoot widerRoot, false),
   ("a_smaller_published_effect_set_is_compatible", subsumes effects emptySummary, true),
   ("a_larger_published_effect_set_breaks_compatibility", subsumes emptySummary effects, false),
   ("changing_callback_mode_pairs_breaks_compatibility",
     callbackModeCallsSubsumed callbackModePairs crossedCallbackModePairs, false)]

def examples : List (String × Bool) :=
  [("core entry: cyclic graph closure includes exactly both entry objects",
      decide ((capturedInstances heap [saved]).length = 2 ∧
        saved ∈ capturedInstances heap [saved] ∧ child ∈ capturedInstances heap [saved])),
   ("core summary: projected child names its original formal", (checkAtEntry actual heap arguments projected).isOk),
   ("core summary: later insertion cannot fabricate frozen entry origin", !(check actual entries forged).isOk),
   ("core summary: snapshot at a later call legitimately includes prior insertion",
      (checkAtEntry actual laterHeap arguments forged).isOk),
   ("core entry: argument preparation finishes before graph capture",
      decide (inserted ∈ capturedInstances laterHeap [saved])),
   ("core entry: saved argument remains distinct from a subsequently rebound slot",
      !(checkAtEntry actual heap [(0, [inserted])] projected).isOk),
   ("core summary: allocation-origin and parameter-origin captures are accepted", (check actual entries captured).isOk),
   ("core summary: allocation-origin capture keeps its full identity",
      decide ((instantiate actual captured).createdEnvironments = [saved, parameterCapture])),
   ("core summary: fresh template at a captured allocation site remains fresh",
      decide (resolve actual allocatedReference ≠ saved)),
   ("core summary: independent fresh templates remain separate", (check actual entries distinctAlloc).isOk &&
      decide ((resolve actual allocatedReference).object ≠ (resolve actual (.allocated inserted.source 1)).object)),
   ("core summary: two templates cannot reuse one allocation serial", !(check actual entries collision).isOk),
   ("core summary: repeated reference preserves an intentional alias", (check actual entries sharedAlloc).isOk &&
      decide ((instantiate actual sharedAlloc).rootReturn = (instantiate actual sharedAlloc).contained)),
   ("core summary: missing formal entry rejected", !(check actual (freeze heap []) projected).isOk),
   ("core summary: duplicate formal entries rejected", !(check actual (freeze heap (arguments ++ arguments)) projected).isOk),
   ("core summary: incomplete old-object coverage rejected",
      !(check { actual with existingObjects := [1] } entries projected).isOk),
   ("core summary: concrete capture absent from old-object coverage rejected",
      !(check actual entries { captured with namedReads := [.concrete { child with object := 77 }] }).isOk),
   ("core summary: reused callee allocation context rejected",
      !(check { actual with activation := 4, scope := 5 } entries projected).isOk),
   ("core summary: fresh reference must describe an allocation source",
      !(check actual entries { rootReturn := [.allocated child.source 0] }).isOk),
   ("core summary: all six state components and effect row compose", (check actual entries allFields).isOk &&
      decide (instantiate actual allFields = ⟨[saved], [child], [child], [saved], [parameterCapture],
        [resolve actual allocatedReference], [6]⟩)),
   ("core graph: disjoint cyclic region accepted", CoreEntry.separated heap [saved] [inserted]),
   ("core graph: shared descendant defeats separation", !CoreEntry.separated heap [saved] [child]),
   ("core graph: later insertion changes separation", !CoreEntry.separated laterHeap [saved] [inserted]),
   ("core graph: unknown index includes every possible selection",
      !CoreEntry.separated heap [saved, inserted] [inserted]),
   ("identity: source labels cannot hide a child alias", !CoreEntry.separated heap [child] [parentAlias]),
   ("identity: aliased parent traversal retains child", decide (child ∈ capturedInstances heap [parentAlias])),
   ("identity: every source explanation survives normalization", decide
      (saved ∈ capturedInstances heap [parentAlias] ∧ parentAlias ∈ capturedInstances heap [parentAlias])),
   ("identity: aliased formal still has physical entry origins",
      (checkAtEntry actual heap [(0, [parentAlias])] projected).isOk),
   ("identity: conflicting allocation contexts fail entry validation",
      !(CoreEntry.capturePrepared heap [(0, [conflictingContext])]).isOk),
   ("identity: conflicting allocation contexts cannot prove separation",
      !CoreEntry.separated heap [inserted] [conflictingContext]),
   ("core graph: different provenance descriptions cannot hide object alias",
      !CoreEntry.separated heap [saved] [sameObject]),
   ("callable match: verified pure .ril read and capture fit empty callable type",
      emptySummary.subsumes pureTable pureReadSummary),
   ("callable match: deeply immutable return sources preserve purity and must match the signature",
      let returns : Summary := { emptySummary with rootReturn := [parameterCapture], contained := [pureConst] }
      returns.isPure pureTable &&
        !returns.isPure [] &&
        !Summary.isPure pureTable { returns with rootReturn := [foreignHandle] } &&
        !Summary.isPure pureTable { returns with contained := [liveVar] } &&
        returns.subsumes pureTable returns &&
        !Summary.subsumes pureTable { returns with rootReturn := [] } returns &&
        !Summary.subsumes pureTable { returns with contained := [] } returns),
   ("callable match: live captured var read rejected by empty callable type",
      !emptySummary.subsumes pureTable liveReadSummary),
   ("callable match: foreign .d.ril source never qualifies as pure",
      !emptySummary.subsumes pureTable foreignReadSummary),
   ("callable match: effect subset and write-to-retained state upper bound accepted",
      retainedSummary.subsumes pureTable writeSummary && writeSummary.subsumes pureTable liveReadSummary),
   ("callable match: retained state cannot downgrade to write-only callable type",
      !writeSummary.subsumes pureTable retainedSummary),
   ("callable match: root return source subset accepted and superset rejected",
      Summary.subsumes pureTable { emptySummary with rootReturn := [saved, child] } { emptySummary with rootReturn := [saved] } &&
        !Summary.subsumes pureTable { emptySummary with rootReturn := [saved] } { emptySummary with rootReturn := [saved, child] }),
   ("callable match: template subsumption preserved across call instantiation",
      upperEffectTemplate.subsumes pureTable pureReadTemplate &&
        (instantiate actual upperEffectTemplate).subsumes pureTable (instantiate actual pureReadTemplate)),
   ("named fn signature: exact signature accepts matching obligations and rejects unexercised &mut/&^mut (E0529)",
      Summary.exactSignature pureTable writeSummary writeSummary &&
      !Summary.exactSignature pureTable writeSummary emptySummary &&
      !Summary.exactSignature pureTable retainedSummary writeSummary),
   ("named fn signature: retained state cannot hide an unexercised write (E0529)",
      !Summary.exactSignature pureTable { retainedSummary with writes := [liveVar] } retainedSummary),
   ("named fn signature: pure immutable factory capture still requires &capture (E0510)",
      !Summary.exactSignature pureTable emptySummary pureReadSummary &&
      Summary.exactSignature pureTable factorySummary pureReadSummary &&
      !Summary.exactSignature pureTable factorySummary emptySummary),
   ("named fn signature: pure outer locals and parameters still require &up (E0510)",
      !Summary.exactSignature pureTable emptySummary pureLocalReadSummary &&
      Summary.exactSignature pureTable pureLocalReadSummary pureLocalReadSummary &&
      !Summary.exactSignature pureTable pureLocalReadSummary emptySummary),
   ("named fn signature: only verified pure module reads need no state clause",
      Summary.exactSignature pureTable emptySummary moduleReadSummary &&
      !Summary.exactSignature [] emptySummary moduleReadSummary &&
      !Summary.exactSignature pureTable emptySummary foreignReadSummary),
   ("named fn signature: rows ignore ordering and duplicate provenance explanations",
      Summary.exactSignature pureTable
        { emptySummary with writes := [liveVar, liveVar], effects := [6, 7] }
        { emptySummary with writes := [liveVar], effects := [7, 6, 7] }),
   ("named fn signature: return and effect rows remain exact",
      !Summary.exactSignature pureTable emptySummary { emptySummary with rootReturn := [saved] } &&
      !Summary.exactSignature pureTable emptySummary { emptySummary with contained := [pureConst] } &&
      !Summary.exactSignature pureTable emptySummary { emptySummary with effects := [6] })] ++
  (signatureCases.map fun (name, verdict, expected) => (name, verdict == expected))

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

end RilAccess.CoreSummary.Examples
