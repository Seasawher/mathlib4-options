option autoImplicit : Bool := true
  Unbound local variables in declaration headers become implicit arguments. In "relaxed" mode (default), any atomic identifier is eligible, otherwise only single character followed by numeric digits are eligible. For example, `def f (x : Vector α n) : Vector α n :=` automatically introduces the implicit variables {α n}.

option autoLift : Bool := true
  insert monadic lifts (i.e., `liftM` and coercions) when needed

option bootstrap.genMatcherCode : Bool := true
  disable code generation for auxiliary matcher function

option bootstrap.inductiveCheckResultingUniverse : Bool := true
  by default the `inductive/structure commands report an error if the resulting universe is not zero, but may be zero for some universe parameters. Reason: unless this type is a subsingleton, it is hardly what the user wants since it can only eliminate into `Prop`. In the `Init` package, we define subsingletons, and we use this option to disable the check. This option may be deleted in the future after we improve the validator

option checkBinderAnnotations : Bool := true
  check whether type is a class instance whenever the binder annotation `[...]` is used

option compiler.check : Bool := true
  type check code after each compiler step (this is useful for debugging purses)

option compiler.checkTypes : Bool := false
  (compiler) perform type compatibility checking after each compiler pass. Note this is not a complete check, and it is used only for debugging purposes. It fails in code that makes heavy use of dependent types.

option compiler.enableNew : Bool := true
  (compiler) enable the new code generator, this should have no significant effect on your code but it does help to test the new code generator; unset to only use the old code generator instead

option compiler.extract_closed : Bool := true
  (compiler) enable/disable closed term caching

option compiler.maxRecInline : Nat := 1
  (compiler) maximum number of times a recursive definition tagged with `[inline]` can be recursively inlined before generating an error during compilation.

option compiler.maxRecInlineIfReduce : Nat := 16
  (compiler) maximum number of times a recursive definition tagged with `[inline_if_reduce]` can be recursively inlined before generating an error during compilation.

option compiler.reuse : Bool := true
  heuristically insert reset/reuse instruction pairs

option compiler.small : Nat := 1
  (compiler) function declarations with size `≤ small` is inlined even if there are multiple occurrences.

option format.indent : Nat := 2
  indentation

option format.inputWidth : Nat := 100
  ideal input width

option format.unicode : Bool := true
  unicode characters

option format.width : Nat := 120
  indentation

option genInjectivity : Bool := true
  generate injectivity theorems for inductive datatype constructors

option genSizeOf : Bool := true
  generate `SizeOf` instance for inductive types and structures

option genSizeOfSpec : Bool := true
  generate `SizeOf` specification theorems for automatically generated instances

option hygiene : Bool := true
  Annotate identifiers in quotations such that they are resolved relative to the scope at their declaration, not that at their eventual use/expansion, to avoid accidental capturing. Note that quotations/notations already defined are unaffected.

option internal.parseQuotWithCurrentStage : Bool := false
  (Lean bootstrapping) use parsers from the current stage inside quotations

option interpreter.prefer_native : Bool := true
  (interpreter) whether to use precompiled code where available

option linter.all : Bool := false
  enable all linters

option linter.deprecated : Bool := true
  if true, generate deprecation warnings

option linter.missingDocs : Bool := false
  enable the 'missing documentation' linter

option linter.suspiciousUnexpanderPatterns : Bool := true
  enable the 'suspicious unexpander patterns' linter

option linter.unnecessarySeqFocus : Bool := true
  enable the 'unnecessary <;>' linter

option linter.unreachableTactic : Bool := true
  enable the 'unreachable tactic' linter

option linter.unusedVariables : Bool := true
  enable the 'unused variables' linter

option linter.unusedVariables.funArgs : Bool := true
  enable the 'unused variables' linter to mark unused function arguments

option linter.unusedVariables.patternVars : Bool := true
  enable the 'unused variables' linter to mark unused pattern variables

option match.ignoreUnusedAlts : Bool := false
  if true, do not generate error if an alternative is not used

option maxBackwardChainingDepth : Nat := 10
  The maximum search depth used in the backwards chaining part of the proof of `brecOn` for inductive predicates.

option maxHeartbeats : Nat := 200000
  maximum amount of heartbeats per command. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit

option maxRecDepth : Nat := 512
  maximum recursion depth for many Lean procedures

option maxUniverseOffset : Nat := 32
  maximum universe level offset

option pp.all : Bool := false
  (pretty printer) display coercions, implicit parameters, proof terms, fully qualified names, universe, and disable beta reduction and notations during pretty printing

option pp.analyze : Bool := false
  (pretty printer analyzer) determine annotations sufficient to ensure round-tripping

option pp.analyze.checkInstances : Bool := false
  (pretty printer analyzer) confirm that instances can be re-synthesized

option pp.analyze.explicitHoles : Bool := false
  (pretty printer analyzer) use `_` for explicit arguments that can be inferred

option pp.analyze.knowsType : Bool := true
  (pretty printer analyzer) assume the type of the original expression is known

option pp.analyze.omitMax : Bool := true
  (pretty printer analyzer) omit universe `max` annotations (these constraints can actually hurt)

option pp.analyze.trustId : Bool := true
  (pretty printer analyzer) always assume an implicit `fun x => x` can be inferred

option pp.analyze.trustKnownFOType2TypeHOFuns : Bool := true
  (pretty printer analyzer) omit higher-order functions whose values seem to be knownType2Type

option pp.analyze.trustOfNat : Bool := true
  (pretty printer analyzer) always 'pretend' `OfNat.ofNat` applications can elab bottom-up

option pp.analyze.trustOfScientific : Bool := true
  (pretty printer analyzer) always 'pretend' `OfScientific.ofScientific` applications can elab bottom-up

option pp.analyze.trustSubst : Bool := false
  (pretty printer analyzer) always 'pretend' applications that can delab to ▸ are 'regular'

option pp.analyze.trustSubtypeMk : Bool := true
  (pretty printer analyzer) assume the implicit arguments of Subtype.mk can be inferred

option pp.analyze.typeAscriptions : Bool := true
  (pretty printer analyzer) add type ascriptions when deemed necessary

option pp.auxDecls : Bool := false
  display auxiliary declarations used to compile recursive functions

option pp.coercions : Bool := true
  (pretty printer) hide coercion applications

option pp.explicit : Bool := false
  (pretty printer) display implicit arguments

option pp.fullNames : Bool := false
  (pretty printer) display fully qualified names

option pp.funBinderTypes : Bool := false
  (pretty printer) display types of lambda parameters

option pp.implementationDetailHyps : Bool := false
  display implementation detail hypotheses in the local context

option pp.inaccessibleNames : Bool := true
  display inaccessible declarations in the local context

option pp.instanceTypes : Bool := false
  (pretty printer) when printing explicit applications, show the types of inst-implicit arguments

option pp.instances : Bool := true
  (pretty printer) if set to false, replace inst-implicit arguments to explicit applications with placeholders

option pp.instantiateMVars : Bool := false
  (pretty printer) instantiate mvars before delaborating

option pp.letVarTypes : Bool := false
  (pretty printer) display types of let-bound variables

option pp.macroStack : Bool := false
  dispaly macro expansion stack

option pp.match : Bool := true
  (pretty printer) disable/enable 'match' notation

option pp.motives.all : Bool := false
  (pretty printer) print all motives

option pp.motives.nonConst : Bool := false
  (pretty printer) print all motives that are not constant functions

option pp.motives.pi : Bool := true
  (pretty printer) print all motives that return pi types

option pp.notation : Bool := true
  (pretty printer) disable/enable notation (infix, mixfix, postfix operators and unicode characters)

option pp.oneline : Bool := false
  (pretty printer) elide all but first line of pretty printer output

option pp.piBinderTypes : Bool := true
  (pretty printer) display types of pi parameters

option pp.privateNames : Bool := false
  (pretty printer) display internal names assigned to private declarations

option pp.proofs : Bool := false
  (pretty printer) if set to false, replace proofs appearing as an argument to a function with a placeholder

option pp.proofs.withType : Bool := true
  (pretty printer) when eliding a proof (see `pp.proofs`), show its type instead

option pp.raw : Bool := false
  (pretty printer) print raw expression/syntax tree

option pp.raw.maxDepth : Nat := 32
  (pretty printer) maximum `Syntax` depth for raw printer

option pp.raw.showInfo : Bool := false
  (pretty printer) print `SourceInfo` metadata with raw printer

option pp.rawOnError : Bool := false
  (pretty printer) fallback to 'raw' printer when pretty printer fails

option pp.safeShadowing : Bool := true
  (pretty printer) allow variable shadowing if there is no collision

option pp.sanitizeNames : Bool := true
  add suffix to shadowed/inaccessible variables when pretty printing

option pp.showLetValues : Bool := true
  display let-declaration values in the info view

option pp.structureInstanceTypes : Bool := false
  (pretty printer) display type of structure instances

option pp.structureInstances : Bool := true
  (pretty printer) display structure instances using the '{ fieldName := fieldValue, ... }' notation or '⟨fieldValue, ... ⟩' if structure is tagged with [pp_using_anonymous_constructor] attribute

option pp.structureProjections : Bool := true
  (pretty printer) display structure projections using field notation

option pp.tagAppFns : Bool := false
  (pretty printer) tag all constants that are the function in a function application

option pp.unicode.fun : Bool := false
  (pretty printer) disable/enable unicode ↦ notation for functions

option pp.universes : Bool := false
  (pretty printer) display universe

option printMessageEndPos : Bool := false
  print end position of each message in addition to start position

option profiler : Bool := false
  show execution times of various Lean components

option profiler.threshold : Nat := 100
  threshold in milliseconds, profiling times under threshold will not be reported individually

option quotPrecheck : Bool := true
  Enable eager name analysis on notations in order to find unbound identifiers early.
  Note that type-sensitive syntax ("elaborators") needs special support for this kind of check, so it might need to be turned off when using such syntax.

option quotPrecheck.allowSectionVars : Bool := false
  Allow occurrences of section variables in checked quotations, it is useful when declaring local notation.

option relaxedAutoImplicit : Bool := true
  When "relaxed" mode is enabled, any atomic nonempty identifier is eligible for auto bound implicit locals (see optin `autoBoundImplicitLocal`.

option server.stderrAsMessages : Bool := true
  (server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message

option showPartialSyntaxErrors : Bool := false
  show elaboration errors from partial syntax trees (i.e. after parser recovery)

option showTacticDiff : Bool := true
  When true, interactive goals for tactics will be decorated with diffing information.

option smartUnfolding : Bool := true
  when computing weak head normal form, use auxiliary definition created for functions defined by structural recursion

option structureDiamondWarning : Bool := false
  enable/disable warning messages for structure diamonds

option synthInstance.checkSynthOrder : Bool := true
  check that instances do not introduce metavariable in non-out-params

option synthInstance.maxHeartbeats : Nat := 20000
  maximum amount of heartbeats per typeclass resolution problem. A heartbeat is number of (small) memory allocations (in thousands), 0 means no limit

option synthInstance.maxSize : Nat := 128
  maximum number of instances used to construct a solution in the type class instance synthesis procedure

option tactic.dbg_cache : Bool := false
  enable tactic cache debug messages (remark: they are sent to the standard error)

option tactic.hygienic : Bool := true
  make sure tactics are hygienic

option tactic.simp.trace : Bool := false
  When tracing is enabled, calls to `simp` or `dsimp` will print an equivalent `simp only` call.

option trace.Compiler : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.commonJoinPointArgs : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.cse : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.eagerLambdaLifting : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.elimDeadBranches : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.extendJoinPointContext : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.findJoinPoints : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.floatLetIn : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.init : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.jp : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.lambdaLifting : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.pullFunDecls : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.pullInstances : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.reduceArity : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.reduceJpArity : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.result : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.saveBase : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.saveMono : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.simp : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.simp.inline : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.simp.jpCases : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.simp.stat : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.simp.step : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.simp.step.new : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.specialize : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.specialize.candidate : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.specialize.info : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.specialize.step : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.stat : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.test : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.toMono : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Compiler.trace : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Debug.Meta.Tactic.simp : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Debug.Meta.Tactic.simp.congr : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.Deriving : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.Deriving.RpcEncodable : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.Deriving.beq : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.Deriving.decEq : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.Deriving.hashable : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.Deriving.inhabited : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.Deriving.ord : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.Deriving.repr : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.app : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.app.args : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.app.finalize : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.app.propagateExpectedType : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.axiom : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.binop : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.binrel : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.cases : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.coe : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.command : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.debug : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.definition : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.definition.body : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.definition.eqns : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.definition.scc : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.definition.structural : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.definition.structural.eqns : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.definition.unfoldEqn : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.definition.wf : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.definition.wf.eqns : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.do : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.induction : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.inductive : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.info : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.input : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.let : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.letrec : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.lint : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.match : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.match_syntax : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.match_syntax.alt : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.match_syntax.result : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.postpone : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.resume : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.step : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.step.result : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.struct : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.structure : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.syntax : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.tactic : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Elab.tactic.backtrack : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Kernel : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.AC : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.IndPredBelow : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.IndPredBelow.match : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Match : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Match.debug : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Match.match : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Match.matchEqs : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Match.unify : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.acyclic : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.cases : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.contradiction : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.induction : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.simp : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.simp.congr : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.simp.discharge : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.simp.heads : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.simp.numSteps : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.simp.rewrite : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.simp.unify : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.split : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.splitIf : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.Tactic.subst : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.appBuilder : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.appBuilder.error : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.appBuilder.result : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.check : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.debug : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.injective : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.assign : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.assign.beforeMkLambda : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.assign.checkTypes : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.assign.occursCheck : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.assign.outOfScopeFVar : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.assign.readOnlyMVarWithBiggerLCtx : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.assign.typeError : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.cache : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.constApprox : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.delta : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.delta.unfoldLeft : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.delta.unfoldLeftRight : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.delta.unfoldRight : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.eta.struct : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.foApprox : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.hint : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.onFailure : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.stuck : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.stuckMVar : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isDefEq.whnf.reduceBinOp : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isLevelDefEq : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isLevelDefEq.postponed : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.isLevelDefEq.stuck : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.sizeOf : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.synthInstance : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.synthInstance.instances : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.synthInstance.newAnswer : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.synthInstance.resume : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.synthInstance.tryResolve : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.synthInstance.unusedArgs : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.synthOrder : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.synthPending : Bool := false
  enable/disable tracing for the given module and submodules

option trace.Meta.whnf : Bool := false
  enable/disable tracing for the given module and submodules

option trace.PrettyPrinter : Bool := false
  enable/disable tracing for the given module and submodules

option trace.PrettyPrinter.delab : Bool := false
  enable/disable tracing for the given module and submodules

option trace.PrettyPrinter.format : Bool := false
  enable/disable tracing for the given module and submodules

option trace.PrettyPrinter.format.backtrack : Bool := false
  enable/disable tracing for the given module and submodules

option trace.PrettyPrinter.format.input : Bool := false
  enable/disable tracing for the given module and submodules

option trace.PrettyPrinter.parenthesize : Bool := false
  enable/disable tracing for the given module and submodules

option trace.PrettyPrinter.parenthesize.backtrack : Bool := false
  enable/disable tracing for the given module and submodules

option trace.PrettyPrinter.parenthesize.input : Bool := false
  enable/disable tracing for the given module and submodules

option trace.compiler : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.cce : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.code_gen : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.cse : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.eager_lambda_lifting : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.elim_dead_let : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.erase_irrelevant : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.eta_expand : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.extract_closed : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.inline : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.input : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir.borrow : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir.boxing : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir.elim_dead : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir.elim_dead_branches : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir.expand_reset_reuse : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir.init : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir.push_proj : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir.rc : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir.reset_reuse : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir.result : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ir.simp_case : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.lambda_lifting : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.lambda_pure : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.lcnf : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.ll_infer_type : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.llnf : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.optimize_bytecode : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.reduce_arity : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.result : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.simp : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.simp_app_args : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.simp_detail : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.simp_float_cases : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.spec_candidate : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.spec_info : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.specialize : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.stage1 : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.stage2 : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.compiler.struct_cases_on : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.debug : Bool := false
  (trace) enable/disable tracing for the given module and submodules

option trace.pp.analyze : Bool := false
  enable/disable tracing for the given module and submodules

option trace.pp.analyze.annotate : Bool := false
  enable/disable tracing for the given module and submodules

option trace.pp.analyze.error : Bool := false
  enable/disable tracing for the given module and submodules

option trace.pp.analyze.tryUnify : Bool := false
  enable/disable tracing for the given module and submodules

option trace.profiler : Bool := false
  activate nested traces with execution time over threshold

option trace.profiler.threshold : Nat := 10
  threshold in milliseconds, traces below threshold will not be activated

option warningAsError : Bool := false
  treat warnings as errors

