import RilAccess.Visibility

namespace RilAccess.Examples.VisibilityExamples

open VisibilityModel

def rilExtIoError : SumDef := ⟨.rilPkg, .pubExport, .transparent, true, [0, 1]⟩
def foreignErrno : SumDef := ⟨.foreignDecl, .pubExport, .transparent, true, [0, 1]⟩
def emptyOpenFuture : SumDef := ⟨.rilPkg, .pubExport, .transparent, true, []⟩
def opaqueScopeSecret : SumDef := ⟨.rilPkg, .pubExport, .opaqueScope, false, [0, 1]⟩

def fixtures : List (String × Bool) :=
  [("visibility: pub(pkg) visible across defining package", visibleFrom .pubPkg .samePkg),
   ("visibility: pub(pkg) hidden from external packages", !visibleFrom .pubPkg .externalPkg),
   ("visibility: pub opaque type visible across package and externally while representation stays file-scoped",
      visibleFrom .pubExport .samePkg &&
      visibleFrom .pubExport .externalPkg &&
      representationTransparent .pubExport .opaqueScope .sameScope &&
      !representationTransparent .pubExport .opaqueScope .samePkg &&
      !representationTransparent .pubExport .opaqueScope .externalPkg),
   ("visibility: pub signature or with cleanup clause referencing pub(pkg) item rejected (E0910)",
      !signatureWellFormed true .pubExport [.pubExport, .pubPkg]),
   ("visibility: pub signature referencing pub item accepted",
      signatureWellFormed true .pubExport [.pubExport]),
   ("visibility: pub(pkg) signature referencing pub(pkg) item accepted",
      signatureWellFormed true .pubPkg [.pubPkg]),
   ("visibility: pub-less library file caps effective visibility at pub(pkg)",
      decide (effectiveVisibility false .pubExport = .pubPkg)),
   ("visibility: module top-level accepts pure/meta constants and rejects mutable or live state (E0906)",
      validTopLevelBinding .pureConst &&
      validTopLevelBinding .metaConst &&
      !validTopLevelBinding .mutableOrLiveState),
   ("sum: .ril extensible sum closed inside package without wildcard",
      exhaustiveMatch rilExtIoError .samePkg [0, 1] false),
   ("sum: .ril extensible sum rejects redundant wildcard inside package when all covered (E0304)",
      !exhaustiveMatch rilExtIoError .samePkg [0, 1] true),
   ("sum: .ril extensible sum requires wildcard outside package (E0303)",
      !exhaustiveMatch rilExtIoError .externalPkg [0, 1] false &&
      exhaustiveMatch rilExtIoError .externalPkg [0, 1] true),
   ("sum: .d.ril extensible sum requires wildcard even inside same scope/package (E0303)",
      !exhaustiveMatch foreignErrno .sameScope [0, 1] false &&
      exhaustiveMatch foreignErrno .sameScope [0, 1] true),
   ("sum: empty extensible { .. } sum admits wildcard externally",
      exhaustiveMatch emptyOpenFuture .externalPkg [] true &&
      !exhaustiveMatch emptyOpenFuture .externalPkg [] false),
   ("sum: pub opaque sum permits defining-file match only and blocks external/package match (E0908)",
      exhaustiveMatch opaqueScopeSecret .sameScope [0, 1] false &&
      !exhaustiveMatch opaqueScopeSecret .samePkg [0, 1] false &&
      !exhaustiveMatch opaqueScopeSecret .externalPkg [0] true),
   ("anchor: pkg/... sees pub(pkg) while ril/... and external deps do not",
      visibleFrom .pubPkg (importContext .pkg) &&
      !visibleFrom .pubPkg (importContext .ril) &&
      !visibleFrom .pubPkg (importContext .externalDep)),
   ("anchor: dependency mount names pkg and ril rejected",
      !validDependencyMountName "pkg" &&
      !validDependencyMountName "ril" &&
      validDependencyMountName "crypto"),
   ("sub: enclosing private or pub(pkg) inline sub caps effective path visibility",
      decide (pathVisibility true [.pubExport] .pubExport = .pubExport) &&
      decide (pathVisibility true [.pubPkg] .pubExport = .pubPkg) &&
      decide (pathVisibility true [.priv] .pubExport = .priv))]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.Examples.VisibilityExamples
