import RilAccess.Visibility

namespace RilAccess.Examples.VisibilityExamples

open VisibilityModel

def rilExtIoError : SumDef := ⟨.rilPkg, .pubExport, .transparent, true, [0, 1]⟩
def foreignErrno : SumDef := ⟨.foreignDecl, .pubExport, .transparent, true, [0, 1]⟩
def emptyOpenFuture : SumDef := ⟨.rilPkg, .pubExport, .transparent, true, []⟩
def opaquePkgToken : SumDef := ⟨.rilPkg, .pubExport, .opaquePkg, false, [0, 1]⟩
def opaqueScopeSecret : SumDef := ⟨.rilPkg, .pubExport, .opaqueScope, false, [0, 1]⟩

def fixtures : List (String × Bool) :=
  [("visibility: pub(pkg) visible across defining package", visibleFrom .pubPkg .samePkg),
   ("visibility: pub(pkg) hidden from external packages", !visibleFrom .pubPkg .externalPkg),
   ("visibility: opaque(pkg) valid on pub export", validOpacity .pubExport .opaquePkg),
   ("visibility: bare or pub(pkg) opaque(pkg) rejected (E0911)",
      !validOpacity .priv .opaquePkg && !validOpacity .pubPkg .opaquePkg),
   ("visibility: pub opaque(pkg) type visible externally while representation stays package-only",
      visibleFrom .pubExport .externalPkg &&
      representationTransparent .pubExport .opaquePkg .samePkg &&
      !representationTransparent .pubExport .opaquePkg .externalPkg),
   ("visibility: pub signature referencing pub(pkg) type rejected (E0910)",
      !signatureWellFormed true .pubExport [.pubExport, .pubPkg]),
   ("visibility: pub signature referencing pub opaque(pkg) type accepted",
      signatureWellFormed true .pubExport [.pubExport]),
   ("visibility: pub(pkg) signature referencing pub(pkg) type accepted",
      signatureWellFormed true .pubPkg [.pubPkg]),
   ("visibility: pub-less library file caps effective visibility at pub(pkg)",
      decide (effectiveVisibility false .pubExport = .pubPkg)),
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
   ("sum: pub opaque(pkg) sum permits package-internal match and blocks external match (E0908)",
      exhaustiveMatch opaquePkgToken .samePkg [0, 1] false &&
      !exhaustiveMatch opaquePkgToken .externalPkg [0, 1] false &&
      !exhaustiveMatch opaquePkgToken .externalPkg [0] true),
   ("sum: pub opaque sum permits defining-scope match only",
      exhaustiveMatch opaqueScopeSecret .sameScope [0, 1] false &&
      !exhaustiveMatch opaqueScopeSecret .samePkg [0, 1] false),
   ("anchor: pkg/... sees pub(pkg) while ril/... and external deps do not",
      visibleFrom .pubPkg (importContext .pkg) &&
      !visibleFrom .pubPkg (importContext .ril) &&
      !visibleFrom .pubPkg (importContext .externalDep)),
   ("anchor: dependency mount names pkg and ril rejected",
      !validDependencyMountName "pkg" &&
      !validDependencyMountName "ril" &&
      validDependencyMountName "crypto"),
   ("sub: pub opaque(pkg) rejected inside private or pub(pkg) enclosing sub (E0911)",
      validPathOpacity true [.pubExport] .pubExport .opaquePkg &&
      !validPathOpacity true [.pubPkg] .pubExport .opaquePkg &&
      !validPathOpacity true [.priv] .pubExport .opaquePkg),
   ("sub: generic sub permits meta let and rejects runtime module storage (E0912)",
      validSubStorage 0 .runtimeStorage &&
      validSubStorage 1 .metaConst &&
      !validSubStorage 1 .runtimeStorage &&
      !validSubStorage 2 .runtimeStorage)]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.Examples.VisibilityExamples
