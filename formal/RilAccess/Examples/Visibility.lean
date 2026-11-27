import RilAccess.Visibility

namespace RilAccess.Examples.VisibilityExamples

open VisibilityModel

def rilExtIoError : SumDef := ⟨.pubExport, .transparent, true, [0, 1]⟩
def pkgExtErrno : SumDef := ⟨.pubExport, .transparent, true, [1, 2, 3]⟩
def emptyOpenFuture : SumDef := ⟨.pubExport, .transparent, true, []⟩
def opaqueScopeSecret : SumDef := ⟨.pubExport, .opaqueScope, false, [0, 1]⟩

def publicRoot : DeclarationVisibility := ⟨true, [], .pubExport⟩
def packageRoot : DeclarationVisibility := ⟨true, [], .pubPkg⟩
def underPackageSub : DeclarationVisibility := ⟨true, [.pubExport, .pubPkg], .pubExport⟩

def examples : List (String × Bool) :=
  [("visibility: pub(pkg) visible across defining package", visibleFrom .pubPkg .samePkg),
   ("visibility: pub(pkg) hidden from external packages", !visibleFrom .pubPkg .externalPkg),
   ("visibility: pub opaque type visible across package and externally while representation stays file-scoped",
      visibleFrom .pubExport .samePkg &&
      visibleFrom .pubExport .externalPkg &&
      representationTransparent .pubExport .opaqueScope .sameScope &&
      !representationTransparent .pubExport .opaqueScope .samePkg &&
      !representationTransparent .pubExport .opaqueScope .externalPkg),
   ("visibility: pub signature or use cleanup clause referencing pub(pkg) item rejected (E0910)",
      !signatureWellFormed publicRoot [publicRoot, packageRoot]),
   ("visibility: pub signature referencing pub item accepted",
      signatureWellFormed publicRoot [publicRoot]),
   ("visibility: pub(pkg) signature referencing pub(pkg) item accepted",
      signatureWellFormed packageRoot [packageRoot]),
   ("visibility: E0910 uses the effective sub path of the declaration and each reference",
      !signatureWellFormed publicRoot [underPackageSub] &&
      !signatureWellFormed publicRoot [⟨true, [.priv], .pubExport⟩] &&
      !signatureWellFormed publicRoot [⟨false, [], .pubExport⟩] &&
      signatureWellFormed underPackageSub [packageRoot] &&
      signatureWellFormed packageRoot [underPackageSub]),
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
   ("sum: extensible sum requires wildcard only outside the defining package when variants are covered",
      exhaustiveMatch pkgExtErrno .samePkg [1, 2, 3] false &&
      !exhaustiveMatch pkgExtErrno .samePkg [1, 2, 3] true &&
      !exhaustiveMatch pkgExtErrno .externalPkg [1, 2, 3] false &&
      exhaustiveMatch pkgExtErrno .externalPkg [1, 2, 3] true),
   ("sum: empty extensible { .. } sum admits wildcard externally",
      exhaustiveMatch emptyOpenFuture .externalPkg [] true &&
      !exhaustiveMatch emptyOpenFuture .externalPkg [] false),
   ("sum: pub opaque sum permits matching within its defining scope (E0308)",
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

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

end RilAccess.Examples.VisibilityExamples
