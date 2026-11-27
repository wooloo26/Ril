import RilAccess.Effects.Ctl

namespace RilAccess.CoreCtl.Examples
open Integrated

def singleCont : LinearState :=
  ⟨1, [{ id := 1, kind := .ctlContinuation }]⟩

def afterConsume : LinearState :=
  (consumeLinear singleCont 1 false).getD singleCont

def armedCont : LinearState :=
  (armDefer singleCont 1 1).getD singleCont

def outerArmedCont : LinearState :=
  ⟨2, [{ id := 1, kind := .opaqueMustConsume, armedDefer := some 1 }]⟩

def examples : List (String × Bool) :=
  [("ctl: unconsumed continuation blocks scope exit (E0625)", !canExitLinearScope singleCont),
   ("ctl: direct root consumption discharges continuation and enables exit",
      (consumeLinear singleCont 1 false).isSome && canExitLinearScope afterConsume),
   ("ctl: projected invocation on ctl continuation rejected (E0548)",
      (consumeLinear singleCont 1 true).isNone),
   ("ctl: double invocation on ctl continuation rejected (E0549)",
      (consumeLinear afterConsume 1 false).isNone),
   ("ctl: unarmed must-consume value cannot cross unhandled ctl (E0625)",
      !canCrossUnhandledCtl singleCont),
   ("ctl: defer armed outside ctl boundary cannot protect crossing unhandled ctl (E0625)",
      !canCrossUnhandledCtl outerArmedCont),
   ("ctl: defer armed inside ctl boundary permits crossing unhandled ctl and discharges on exit",
      (armDefer singleCont 1 1).isSome &&
      canCrossUnhandledCtl armedCont &&
      canExitLinearScope (runArmedDefers armedCont)),
   ("ctl: ^mut shared writer cannot downgrade to mut (E0523) or ref (E0524) across unhandled effect",
      !canPassSharedAs .shared .mutable true &&
      !canPassSharedAs .shared .observe true &&
      canPassSharedAs .shared .retained true &&
      canPassSharedAs .shared .mutable false),
   ("ctl: K-IFACE no_ctl_params rejects ctl-performing callback (E0616) and permits pure/fn callback",
      !checkNoCtlCall [0] 0 true &&
      checkNoCtlCall [0] 0 false &&
      checkNoCtlCall [0] 1 true)]

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

end RilAccess.CoreCtl.Examples
