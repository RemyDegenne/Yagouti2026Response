module

public import LeanMachineLearning.SequentialLearning.FiniteActions
public import LeanMachineLearning.SequentialLearning.ActionIndicator
public import Lean.Environment
public import Lean.Modifiers
public import Lean.ProjFns
public import Lean.Runtime
public import Lean.ResolveName
public import Lean.Attributes
public import Lean.Parser
public import Lean.ReducibilityAttrs
public import Lean.Class
public import Lean.LocalContext
public import Lean.MetavarContext
public import Lean.AuxRecursor
public import Lean.Structure
public import Lean.PrettyPrinter
public import Lean.CoreM
public import Lean.ReservedNameAction
public import Lean.InternalExceptionId
public import Lean.ScopedEnvExtension
public import Lean.DocString
public import Lean.DeclarationRange
public import Lean.LoadDynlib
public import Lean.Log
public import Lean.SubExpr
public import Lean.LabelAttribute
public import Lean.AutoDecl
public import Lean.AddDecl
public import Lean.PrivateName
public import Lean.Namespace
public import Lean.EnvExtension
public import Lean.ErrorExplanation
public import Lean.DefEqAttrib
public import Lean.ExtraModUses
public import Lean.OriginalConstKind
public import Init.Data.SInt.Basic
public import Init.System.IO
public import Init.Data.Prod
public import Init.Data.Array.Lemmas
public import Init.Data.Array.Bootstrap
public import Init.Data.List.Range
public import Init.Data.List.Nat.Range
public import Init.Data.ByteArray.Lemmas
public import Init.Data.List.Sublist
public import Init.Data.List.TakeDrop
public import Init.Omega
public import Init.ByCases
public import Init.Data.Hashable
public import Init.Data.ToString
public import Init.Data.String.Bootstrap
public meta import Lean.Elab.Command
public meta import Lean.Meta.Eval
public import Lean.Elab.ParseImportsFast
public import Init.System.Platform
public import Init.Data.String.Lossy
public import Lean.Compiler.Options
public import Std.Data.HashMap
public import Init.Data.Ord.UInt
public import Init.System.Promise
public import Init.Data.Vector.Basic
public import Std.Time.Time
public import Std.Time.Date
public import Std.Time.Zoned
public import Std.Time.Format
public import Std.Time.DateTime
public import Std.Time.Duration
public import Std.Time.Zoned.Database
public meta import Std.Time.Format
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.NameMangling
public import Lean.Compiler.LCNF.PhaseExt
public import Lean.Compiler.ExportAttr
public import Lean.Compiler.ModPkgExt
public import Lean.Compiler.LCNF.SimpleGroundExpr
public import Lean.Compiler.ClosedTermCache
public import Lean.Compiler.LCNF.Internalize
public import Lean.Compiler.InitAttr
public import Init.While
public import Lean.Compiler.LCNF.SimpCase
public import Lean.Compiler.LCNF.PrettyPrinter
public import Lean.Server.FileWorker.Utils
public import Lean.Server.FileWorker.RequestHandling
public import Init.Data.String.OrderInstances
public import Lean.Server.Completion.CompletionInfoSelection
public import Lean.Server.CodeActions.Basic
public import Lean.Language.Lean.Util
public import Lean.Data.Lsp
public import Lean.Parser.Module
public meta import Lean.Parser.Module
public import Lean.Server.Utils
public import Lean.Server.ServerTask
public import Lean.Server.Rpc.RequestHandling
public import Lean.PrettyPrinter.Delaborator.Builtins
public import Lean.Language.Lean.Types
public import Lean.Elab.Import
public import Lean.Elab.InfoTree
public import Init.Data.Format.Macro
public import Init.Data.Queue
public import Std.Sync.Mutex
public import Init.Data.Option.BasicAux
public import Init.Data.Random
public import Init.Data.ByteArray.Extra
public import Lean.Data.FuzzyMatching
public import Lean.Server.Requests
public import Lean.Server.References
public import Lean.Server.Completion.CompletionUtils
public import Init.Data.List.Sort
public import Lean.Data.Lsp.InitShutdown
public import Lean.Linter.PersistentLintLog
public import Init.Data.String.Legacy
public import Init.Data.Function
public import Init.Data.ToString.Macro
public import Std.Data.HashSet
public import Std.Data.DHashMap.RawLemmas
public import Std.Data.HashMap.RawLemmas
public import Std.Data.HashSet.RawLemmas
public import Std.Data.Iterators
public import Std.Data.ByteSlice
public import Init.Data.String.Slice
public import Init.Data.String.Search
public import Init.Data.ToString.Extra
public import Init.Data.String.TakeDrop
public import Init.Data.String.Lemmas.Pattern.TakeDrop.Basic
public import Init.Data.String.Lemmas.Pattern.TakeDrop.Char
public import Init.Data.Int.ToString
public import Init.Data.Nat.ToString
public import Init.Data.String.Lemmas.Iterate
public import Std.Tactic.Do.ProofMode
public import Std.Tactic.Do.Syntax
public import Std.Data.TreeSet.Raw.Basic
public import Std.Data.TreeMap.Raw.Basic
public import Std.Data.DTreeMap.Raw.Basic
public import Std.Data.DTreeMap.Internal.Lemmas
public import Std.Data.Iterators.Lemmas.Producers.Slice
public import Init.Data.Slice
public import Init.Data.Iterators.Combinators.FilterMap
public import Init.Data.Iterators.Lemmas.Combinators.FilterMap
public import Init.Data.Iterators.Lemmas.Consumers.Collect
public import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect
public import Init.Data.List.Pairwise
public import Init.Data.Slice.InternalLemmas
public import Std.Data.DTreeMap.AdditionalOperations
public import Init.Data.Array.Perm
public import Init.Data.List.Find
public import Std.Data.TreeSet.AdditionalOperations
public import Std.Data.TreeMap.Basic
public import Init.Data.List.BasicAux
public import Init.Data.Order.ClassesExtra
public import Init.Data.Order.Classes
public import Init.Data.List.Impl
public import Std.Data.HashSet.Raw
public import Std.Data.HashMap.Raw
public import Std.Data.DHashMap.Internal.RawLemmas
public import Std.Data.ExtTreeSet.Basic
public import Std.Data.ExtTreeSet.Lemmas
public import Std.Data.ExtTreeMap.Basic
public import Std.Data.ExtTreeMap.Lemmas
public import Std.Data.ExtDTreeMap.Basic
public import Std.Data.ExtDTreeMap.Lemmas
public import Std.Data.ExtHashSet.Basic
public import Std.Data.ExtHashSet.Lemmas
public import Std.Data.ExtHashMap.Basic
public import Std.Data.ExtHashMap.Lemmas
public import Std.Data.ExtDHashMap.Basic
public import Std.Data.ExtDHashMap.Lemmas
public import Std.Data.TreeSet.Basic
public import Std.Data.TreeSet.Lemmas
public import Std.Data.DTreeMap.Lemmas
public import Std.Data.TreeMap.AdditionalOperations
public import Std.Data.TreeMap.Lemmas
public import Std.Data.DTreeMap.Basic
public import Std.Data.DHashMap.Basic
public import Std.Data.DHashMap.AdditionalOperations
public import Std.Data.DHashMap.Iterator
public import Std.Data.DHashMap.Lemmas
public import Std.Data.DHashMap.IteratorLemmas
public import Std.Data.DHashMap.DecidableEquiv
public import Init.Data.Repr
public import Init.Data.Char
public import Init.Data.String.Basic
public import Init.Data.Int.Basic
public import Init.Grind
public import Init.Data.String.Csimp
public import Init.Data.ByteArray.Basic
public import Init.Data.Int.OfNat
public import Init.Data.UInt.Lemmas
public import Init.Data.String.Modify
public import Init.Data.String.Lemmas.Modify
public import Init.Data.String.Iter
public import Std.Internal.Parsec.Basic
public import Std.Internal.Parsec
public import Std.Internal.Parsec.ByteArray
public import Init.Data.Nat.Basic
public import Init.Data.String.Length
public import Init.Data.SInt.Lemmas
public import Init.Data.UInt.Bitwise
public import Init.Dynamic
public import Init.Data.String.Compare
public import Std.Sync.Basic
public import Init.Data.Vector
public import Init.Data.Array
public import Lean.Util.Trace
public import Init.Data.Range.Polymorphic.Iterators
public import Lean.LibrarySuggestions.Basic
public import Lean.Meta.Basic
public import Lean.Util.FoldConsts
public import Lean.Linter.Util
public import Lean.Linter.AmbiguousOpen
public import Lean.Linter.Deprecated
public import Lean.Linter.UnusedVariables
public import Lean.Linter.MissingDocs
public import Lean.Linter.Sets
public import Lean.Linter.Basic
public import Lean.Elab.Command
public import Lean.Meta.Check
public import Lean.Meta.Diagnostics
public import Lean.Meta.ForEachExpr
public import Lean.Meta.Sorry
public import Lean.Elab.InfoTree.Util
public import Lean.Parser.Syntax
public import Init.Try
public import Lean.Linter.Init
public import Lean.Util.Path
public import Lean.Elab.InfoTree.Main
public import Lean.Elab.Term.TermElabM
public import Lean.Elab.Tactic.Simp
public import Lean.Data.Options
public import Lean.Linter.CodeQuality.Basic
public import Lean.Message
public import Lean.Util.CollectLevelParams
public import Lean.Util.ForEachExpr
public import Lean.Widget.InteractiveCode
public import Lean.Widget.InteractiveDiagnostic
public import Lean.Widget.InteractiveGoal
public import Lean.Widget.TaggedText
public import Lean.Widget.UserWidget
public import Lean.Widget.Commands
public import Lean.Server.CodeActions
public import Init.Prelude
public import Lean.Server.GoTo
public import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.Basic
public import Lean.Server.Rpc.Basic
public import Lean.Elab.Deriving.Basic
public import Lean.Util.CollectFVars
public import Lean.Util.CollectMVars
public import Lean.Util.CollectLevelMVars
public import Lean.Util.CollectLooseBVars
public import Lean.Util.FindMVar
public import Lean.Util.FindLevelMVar
public import Lean.Util.MonadCache
public import Lean.Util.PPExt
public import Lean.Util.Profile
public import Lean.Util.RecDepth
public import Lean.Util.ShareCommon
public import Lean.Util.Sorry
public import Lean.Util.FindExpr
public import Lean.Util.ReplaceExpr
public import Lean.Util.ForEachExprWhere
public import Lean.Util.ReplaceLevel
public import Lean.Util.SCC
public import Lean.Util.OccursCheck
public import Lean.Util.HasConstCache
public import Lean.Util.Heartbeats
public import Lean.Util.SafeExponentiation
public import Lean.Util.NumObjs
public import Lean.Util.NumApps
public import Lean.Util.SortExprs
public import Lean.Util.ParamMinimizer
public import Init.Notation
public import Lean.Exception
public meta import Lean.Compiler.ImplementedByAttr
public meta import Lean.Compiler.ExternAttr
public import Lean.Meta.Tactic.Delta
public import Lean.Meta.Tactic.Simp.Main
public import Lean.Meta.WHNF
public import Lean.Meta.HasAssignableMVar
public import Lean.Meta.InferType
public import Lean.Meta.FunInfo
public import Lean.Meta.DecLevel
public import Lean.Meta.DiscrTree
public import Lean.Meta.Reduce
public import Lean.Meta.Instances
public import Lean.Meta.AbstractMVars
public import Lean.Meta.SynthInstance
public import Lean.Meta.AppBuilder
public import Lean.Meta.KAbstract
public import Lean.Meta.RecursorInfo
public import Lean.Meta.GeneralizeTelescope
public import Lean.Meta.ReduceEval
public import Lean.Meta.Closure
public import Lean.Meta.AbstractNestedProofs
public import Lean.Meta.WrapInstance
public import Lean.Meta.LetToHave
public import Lean.Meta.Transform
public import Lean.Meta.PPGoal
public import Lean.Meta.SizeOf
public import Lean.Meta.IndPredBelow
public import Lean.Meta.Coe
public import Lean.Meta.CollectFVars
public import Lean.Meta.GeneralizeVars
public import Lean.Meta.Injective
public import Lean.Meta.Structure
public import Lean.Meta.Constructions
public import Lean.Meta.CongrTheorems
public import Lean.Meta.Eqns
public import Lean.Meta.ExprLens
public import Lean.Meta.Eval
public import Lean.Meta.CoeAttr
public import Lean.Meta.Iterator
public import Lean.Meta.LazyDiscrTree
public import Lean.Meta.LitValues
public import Lean.Meta.Canonicalizer
public import Lean.Meta.BinderNameHint
public import Lean.Meta.TryThis
public import Lean.Meta.Hint
public import Lean.Meta.MethodSpecs
public import Lean.Meta.CtorIdxHInj
public import Lean.Meta.MonadSimp
public import Lean.Meta.HaveTelescope
public import Lean.Meta.Sym.AlphaShareBuilder
public import Lean.Meta.Sym.AlphaShareCommon
public import Lean.Meta.Sym.ExprPtr
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Sym.MaxFVar
public import Lean.Meta.Sym.ReplaceS
public import Lean.Meta.Sym.LooseBVarsS
public import Lean.Meta.Sym.InstantiateS
public import Lean.Meta.Sym.IsClass
public import Lean.Meta.Sym.InstantiateMVarsS
public import Lean.Meta.Sym.ProofInstInfo
public import Lean.Meta.Sym.AbstractS
public import Lean.Meta.Sym.Pattern
public import Lean.Meta.Sym.Apply
public import Lean.Meta.Sym.InferType
public import Lean.Meta.Sym.DSimp
public import Lean.Meta.Sym.Util
public import Lean.Meta.Sym.Eta
public import Lean.Meta.Sym.Canon
public import Lean.Meta.Sym.SynthInstance
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.Simp.Discharger
public import Lean.Meta.Tactic.Grind.Main
public import Lean.Meta.Tactic.Grind.Solve
public import Lean.Meta.Tactic.Assumption
public import Lean.Meta.Tactic.Intro
public import Lean.Meta.Tactic.Util
public import Lean.Meta.Sym.Arith.Types
public import Lean.Meta.Sym.Arith.EvalNum
public import Lean.Meta.Sym.Arith.Insts
public import Lean.Meta.Sym.Arith.Classify
public import Lean.Meta.Sym.Arith.MonadCanon
public import Lean.Meta.Sym.Arith.MonadRing
public import Lean.Meta.Sym.Arith.MonadSemiring
public import Lean.Meta.Sym.Arith.MonadVar
public import Lean.Meta.Sym.Arith.Functions
public import Lean.Meta.Sym.Arith.DenoteExpr
public import Lean.Meta.Sym.Arith.ToExpr
public import Lean.Meta.Sym.Arith.VarRename
public import Lean.Meta.Sym.Arith.Poly
public import Lean.Meta.Sym.Arith.SafePoly
public import Lean.Meta.Sym.Arith.Norm
public import Lean.Meta.Sym.LitValues
public import Lean.Meta.Sym.Simp.App
public import Lean.Meta.Sym.Simp.CongrInfo
public import Lean.Meta.Sym.Simp.DiscrTree
public import Lean.Meta.Sym.Simp.Main
public import Lean.Meta.Sym.Simp.Result
public import Lean.Meta.Sym.Simp.Rewrite
public import Lean.Meta.Sym.Simp.Simproc
public import Lean.Meta.Sym.Simp.Theorems
public import Lean.Meta.Sym.Simp.Have
public import Lean.Meta.Sym.Simp.Lambda
public import Lean.Meta.Sym.Simp.Forall
public import Lean.Meta.Sym.Simp.EvalGround
public import Lean.Meta.Sym.Simp.ControlFlow
public import Lean.Meta.Sym.Simp.Attr
public import Lean.Meta.Sym.Simp.Arith
public import Lean.Meta.Sym.Simp.Reduce
public meta import Init.Data.ToString.Name
public meta import Init.Data.String.Extra
public import Lean.Meta.Match.MatchPatternAttr
public import Lean.Meta.Match.Match
public import Lean.Meta.Match.CaseValues
public import Lean.Meta.Match.CaseArraySizes
public import Lean.Meta.Match.MatchEqsExt
public import Lean.Meta.Tactic.Refl
public import Lean.Meta.Tactic.SplitIf
public import Lean.Meta.Tactic.CasesOnStuckLHS
public import Lean.Meta.Match.SimpH
public import Lean.Meta.Match.AltTelescopes
public import Lean.Meta.Match.NamedPatterns
public import Lean.Meta.Tactic.Rewrite
public import Lean.Meta.Constructions.SparseCasesOn
public import Lean.Meta.Constructions.SparseCasesOnEq
public import Lean.Meta.HasNotBit
public import Lean.Meta.Tactic.Cases
public import Lean.Meta.Tactic.Replace
public import Lean.Meta.Tactic.Contradiction
public import Lean.Meta.Tactic.Apply
public import Lean.Meta.Tactic.Revert
public import Lean.Meta.Tactic.Clear
public import Lean.Meta.Tactic.Assert
public import Lean.Meta.Tactic.Generalize
public import Lean.Meta.Tactic.Induction
public import Lean.Meta.Tactic.ElimInfo
public import Lean.Meta.Tactic.Constructor
public import Lean.Meta.Tactic.Simp
public import Lean.Meta.Tactic.AuxLemma
public import Lean.Meta.Tactic.Split
public import Lean.Meta.Tactic.TryThis
public import Lean.Meta.Tactic.Cleanup
public import Lean.Meta.Tactic.Rename
public import Lean.Meta.Tactic.Congr
public import Lean.Meta.Tactic.Repeat
public import Lean.Meta.Tactic.NormCast
public import Lean.Meta.Tactic.IndependentOf
public import Lean.Meta.Tactic.Symm
public import Lean.Meta.Tactic.Backtrack
public import Lean.Meta.Tactic.SolveByElim
public import Lean.Meta.Tactic.Rfl
public import Lean.Meta.Tactic.Ext
public import Lean.Meta.Tactic.Try
public import Lean.Elab.ConfigEval
public import Init.Simproc
public import Init.Grind.Tactics
public import Init.MetaTypes
public import Init.Data.Nat.Bitwise.Basic
public import Lean.Meta.Sym.DSimp.DSimpM
public import Lean.Elab.Tactic.FalseOrByContra
public import Lean.Meta.Tactic.Grind.Util
public import Lean.Meta.Tactic.Grind.Simp
public import Lean.Meta.Sym.DSimp.Result
public import Init.Data.BitVec.Bitblast
public import Init.Data.AC
public import Init.Data.BitVec.Lemmas
public import Init.Data.BitVec.Package
public import Init.Data.BitVec.Bootstrap
public import Init.PropLemmas
public import Init.Data.BitVec.Decidable
public import Init.Data.BEq
public import Init.Data.Nat.Power2.Bitwise
public import Init.Data.UInt.IntToBitVec
public import Init.Data.SInt.IntToBitVec
public import Lean.Elab.Tactic.Rewrite
public import Init.SimpLemmas
public import Init.Data.Array.MapIdx
public import Init.Data.Nat.Order
public import Init.Data.Option.Lemmas
public import Init.Data.List.MinMax
public import Init.Data.Array.MinMax
public import Init.TacticsExtra
public import Lean.Elab.DeclarationRange
public import Init.Data.Nat.Fold
public import Init.Data.Range.Polymorphic
public import Std.Do.Triple.SpecLemmas
public import Init.Data.String.Defs
public import Init.Data.RArray
public import Std.Data.HashMap.Basic
public import Init.Data.Nat.Internal.Linear
public import Init.Data.Vector.Lemmas
public import Init.Data.Order.Lemmas
public import Init.Data.Int.Pow
public import Init.Data.Nat.Mod
public import Lean.Data.RArray
public import Lean.Data.NameMap.Basic
public import Init.CbvSimproc
public import Init.GetElem
public import Init.Sym.Lemmas
public import Lean.Compiler.NoncomputableAttr
public import Lean.Meta.Tactic.Grind.Attr
public import Lean.Meta.Tactic.Grind.MarkAccessible
public import Lean.Meta.Tactic.Grind.Cases
public import Lean.Meta.Tactic.Grind.Injection
public import Lean.Meta.Tactic.Grind.Core
public import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
public import Lean.Meta.Tactic.Grind.Inv
public import Lean.Meta.Tactic.Grind.Proof
public import Lean.Meta.Tactic.Grind.PP
public import Lean.Meta.Tactic.Grind.Ctor
public import Lean.Meta.Tactic.Grind.Parser
public import Lean.Meta.Tactic.Grind.EMatchTheorem
public import Lean.Meta.Tactic.Grind.EMatch
public import Lean.Meta.Tactic.Grind.CasesMatch
public import Lean.Meta.Tactic.Grind.MatchCond
public import Lean.Meta.Tactic.Grind.MatchDiscrOnly
public import Lean.Meta.Tactic.Grind.LawfulEqCmp
public import Lean.Meta.Tactic.Grind.ReflCmp
public import Lean.Meta.Tactic.Grind.SynthInstance
public import Lean.Meta.Tactic.Grind.VarRename
public import Lean.Meta.Tactic.Grind.PropagateInj
public import Lean.Meta.Tactic.Grind.Anchor
public import Lean.Meta.Tactic.Grind.Action
public import Lean.Meta.Tactic.Grind.EMatchTheoremParam
public import Lean.Meta.Tactic.Grind.EMatchAction
public import Lean.Meta.Tactic.Grind.CollectParams
public import Lean.Meta.Tactic.Grind.Finish
public import Lean.Meta.Tactic.Grind.RegisterCommand
public import Lean.Meta.Tactic.Grind.Homo
public import Init.Grind.Homo.Extra
public import Lean.Meta.NatInstTesters
public import Init.Grind.Lemmas
public import Lean.Meta.Tactic.Grind.Arith.Util
public import Init.Grind.Propagator
public import Init.Grind.Order
public import Lean.Meta.Tactic.Grind.PropagatorAttr
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
public import Init.Grind.Module.Envelope
public import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
public import Lean.Meta.Tactic.Grind.AC.Types
public import Lean.Meta.Tactic.Grind.AC.Util
public import Lean.Meta.Tactic.Grind.AC.Seq
public import Lean.Meta.Tactic.Grind.AC.DenoteExpr
public import Lean.Meta.Tactic.Grind.AC.PP
public import Init.Grind.AC
public import Lean.ToExpr
public import Lean.Meta.Tactic.Grind.Split
public import Lean.Meta.Tactic.Grind.CastLike
public import Lean.Meta.Tactic.Grind.Arith.Simproc
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
public import Lean.Meta.Tactic.Simp.Arith.Int.Simp
public import Init.Data.Int.Linear
public import Lean.Meta.IntInstTesters
public import Lean.Meta.Tactic.Simp.Arith.Int
public import Init.Data.Nat.Dvd
public import Lean.Meta.Tactic.Grind.Arith.ModelUtil
public import Lean.Meta.Tactic.Grind.Arith.Linear.Types
public import Lean.Meta.Tactic.Grind.Arith.Linear.Util
public import Lean.Meta.Tactic.Grind.Arith.Linear.Var
public import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
public import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
public import Lean.Meta.Tactic.Grind.Arith.Linear.Model
public import Lean.Meta.Tactic.Grind.Arith.Linear.PP
public import Init.Grind.Module.OfNatModule
public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
public import Init.Grind.Module.NatModuleNorm
public import Init.Grind.Ordered.Linarith
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Types
public import Lean.Meta.Tactic.Grind.Arith.CommRing.PP
public import Init.Core
public import Init.Data.BitVec.Basic
public import Lean.Meta.Tactic.Simp.Types
public import Lean.Meta.Match.MatcherApp.Transform
public import Lean.Meta.ArgsPacker
public import Lean.Elab.PreDefinition.WF.Eqns
public import Lean.Elab.PreDefinition.Structural.Eqns
public import Lean.Elab.PreDefinition.Structural.FindRecArg
public import Lean.Meta.Tactic.FunIndInfo
public import Lean.Data.Array
public import Lean.Meta.Tactic.Simp.Rewrite
public import Lean.Elab.Exception
public import Lean.Elab.Config
public import Lean.Elab.Term
public import Lean.Elab.App
public import Lean.Elab.Binders
public import Lean.Elab.BuiltinNotation
public import Lean.Elab.Declaration
public import Lean.Elab.Match
public import Lean.Elab.Quotation
public import Lean.Elab.Syntax
public import Lean.Elab.Do
public import Lean.Elab.MutualInductive
public import Lean.Elab.MutualDef
public import Lean.Elab.AuxDef
public import Lean.Elab.BuiltinTerm
public import Lean.Elab.Arg
public import Lean.Elab.DeprecatedArg
public import Lean.Elab.PatternVar
public import Lean.Elab.ElabRules
public import Lean.Elab.BuiltinCommand
public import Lean.Elab.AssertExists
public import Lean.Elab.RecAppSyntax
public import Lean.Elab.Eval
public import Lean.Elab.Calc
public import Lean.Elab.Tactic.Doc
public import Lean.Elab.DocString
public import Lean.Elab.Parallel
public import Lean.Elab.Tactic.Config
public import Lean.Elab.ConfigEval.Commands
public import Lean.Elab.ConfigEval.DeriveEvalConfigItem
public import Lean.Elab.Do.Basic
public meta import Lean.Parser.Do
public meta import Init.Data.Erased
public import Init.Control.Do
public import Lean.Meta.ProdN
public import Init.BinderNameHint
public import Std.Internal.ForIn.Basic
public import Init.Data.List.Control
public import Init.Data.Array.Basic
public import Init.Data.Range.Basic
public import Init.Data.Range.Polymorphic.Lemmas
public import Init.Data.Iterators.Lemmas.Consumers.Loop
public import Init.Data.Slice.Lemmas
public import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
public import Init.Data.List.Basic
public import Init.Data.List.Monadic
public import Init.Data.Range.Lemmas
public import Init.Data.Slice.Array
public import Init.Data.Range
public import Init.Data.Iterators.Lemmas
public import Init.Data.List.Nat.TakeDrop
public import Init.Data.String.Iterate
public import Init.Data.String.Lemmas.Splits
public import Init.Data.String.Termination
public import Init.Internal.Order
public import Init.Classical
public import Init.Control.Lawful.MonadAttach.Instances
public import Init.Data.Option.Attach
public import Lean.Elab.Do.Control
public import Lean.Elab.Do.InferControlInfo
public import Lean.Elab.Do.PatternVar
public import Lean.Elab.MatchAltView
public import Lean.DocString.View
public import Lean.Elab.Open
public import Lean.DocString.Syntax
public import Lean.DocString.DeferredCheck
public import Lean.Parser.Extension
public import Init.Data.Array.Attach
public import Init.Data.Array.Mem
public meta import Lean.Widget.UserWidget
public import Lean.Elab.DeclUtil
public import Lean.PrettyPrinter.Delaborator
public import Lean.Elab.Tactic.ElabTerm
public import Lean.Elab.Tactic.Meta
public import Lean.Server.CodeActions.Attr
public import Lean.DocString.Markdown
public import Lean.Elab.ErrorUtils
public import Lean.Elab.Attributes
public import Init.Syntax
public import Lean.Elab.MacroArgUtil
public import Lean.Meta.Constructions.CtorIdx
public import Lean.Elab.Deriving.Util
public import Init.LawfulBEqTactics
public import Lean.Meta.Constructions.CasesOnSameCtor
public import Lean.Meta.SameCtorUtils
public import Init.Data.Array.OfFn
public import Lean.Meta.NatTable
public import Lean.Elab.PreDefinition.Basic
public import Lean.Elab.PreDefinition.Structural
public import Lean.Elab.PreDefinition.Main
public import Lean.Elab.PreDefinition.MkInhabitant
public import Lean.Elab.PreDefinition.EqnsUtils
public import Lean.Elab.PreDefinition.WF.Main
public import Lean.Elab.Tactic.Induction
public import Lean.Elab.Tactic.Location
public import Lean.Elab.Tactic.SimpTrace
public import Lean.Elab.Tactic.BuiltinTactic
public import Lean.Elab.Tactic.Split
public import Lean.Elab.Tactic.Calc
public import Lean.Elab.Tactic.RCases
public import Lean.Elab.Tactic.Ext
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.SolveByElim
public import Lean.Elab.Tactic.LibrarySearch
public import Lean.Elab.Tactic.Classical
public import Lean.Elab.Tactic.Monotonicity
public import Lean.Elab.Tactic.Try
public import Lean.Elab.Tactic.Grind.Main
public import Lean.Elab.Tactic.Grind.Basic
public import Lean.Meta.DiscrTree.Util
public import Lean.Meta.Match.MatcherInfo
public import Std.WP.Tactic
public import Std.Do.SPred.DerivedLaws
public import Lean.Elab.Util
public import Lean.DocString.Extension
public meta import Lean.Parser.Command
public meta import Lean.Parser.Term
public import Init.Grind.Interactive
public import Std.Do.Triple.Basic
public import Lean.Meta.Tactic.ExposeNames
public import Lean.Elab.Tactic.Grind.Config
public import Lean.Elab.Tactic.Grind.Annotated
public import Lean.Meta.Tactic.Grind.NormSym
public import Init.Sym.DSimp.DSimprocDSL
public import Lean.Meta.Sym.DSimp.Variant
public import Lean.Meta.Sym.DSimp.Reduce
public import Lean.Meta.Sym.DSimp.DSimproc
public import Lean.Meta.Sym.DSimp.EvalGround
public import Lean.Meta.Sym.DSimp.Rewrite
public import Init.Sym.Simp.SimprocDSL
public import Lean.Elab.SyntheticMVars
public import Init.Grind.Lint
public import Std.Do
public import Lean.Elab.Tactic.Grind.Param
public import Lean.Meta.Tactic.Grind.Intro
public import Lean.Meta.Tactic.Grind.Internalize
public import Lean.Elab.Tactic.RenameInaccessibles
public import Lean.Elab.Tactic.Grind.Anchor
public import Lean.Meta.Tactic.Simp.Attr
public import Lean.Meta.Tactic.Simp.SimpTheorems
public import Lean.Elab.Tactic.Conv.Simp
public import Init.Guard
public import Lean.Elab.Tactic.Conv.Basic
public import Lean.Elab.Tactic.Conv.Pattern
public import Lean.Meta.Tactic.Simp.Simproc
public import Lean.Meta.Tactic.Injection
public import Lean.Compiler.InlineAttrs
public import Lean.Compiler.Specialize
public import Lean.Compiler.ExternAttr
public import Lean.Compiler.ImplementedByAttr
public import Lean.Compiler.NeverExtractAttr
public import Lean.Compiler.IR
public import Lean.Compiler.CSimpAttr
public import Lean.Compiler.MetaAttr
public import Lean.Compiler.Old
public import Lean.Data.NameTrie
public import Lean.Compiler.LCNF.AlphaEqv
public import Lean.Compiler.LCNF.Basic
public import Lean.Compiler.LCNF.Bind
public import Lean.Compiler.LCNF.Check
public import Lean.Compiler.LCNF.CSE
public import Lean.Compiler.LCNF.DependsOn
public import Lean.Compiler.LCNF.ElimDead
public import Lean.Compiler.LCNF.FixedParams
public import Lean.Compiler.LCNF.InferType
public import Lean.Compiler.LCNF.JoinPoints
public import Lean.Compiler.LCNF.LCtx
public import Lean.Compiler.LCNF.Level
public import Lean.Compiler.LCNF.Main
public import Lean.Compiler.LCNF.Passes
public import Lean.Compiler.LCNF.PassManager
public import Lean.Compiler.LCNF.PullFunDecls
public import Lean.Compiler.LCNF.PullLetDecls
public import Lean.Compiler.LCNF.ReduceJpArity
public import Lean.Compiler.LCNF.Simp
public import Lean.Compiler.LCNF.Specialize
public import Lean.Compiler.LCNF.SpecInfo
public import Lean.Compiler.LCNF.ToDecl
public import Lean.Compiler.LCNF.ToExpr
public import Lean.Compiler.LCNF.ToLCNF
public import Lean.Compiler.LCNF.Types
public import Lean.Compiler.LCNF.Util
public import Lean.Compiler.LCNF.ConfigOptions
public import Lean.Compiler.LCNF.MonoTypes
public import Lean.Compiler.LCNF.ToMono
public import Lean.Compiler.LCNF.MonadScope
public import Lean.Compiler.LCNF.Closure
public import Lean.Compiler.LCNF.LambdaLifting
public import Lean.Compiler.LCNF.ReduceArity
public import Lean.Compiler.LCNF.Irrelevant
public import Lean.Compiler.LCNF.SplitSCC
public import Init.System.FilePath
public import Lean.Data.AssocList
public import Lean.Data.Format
public import Lean.Data.Json
public import Lean.Data.JsonRpc
public import Lean.Data.KVMap
public import Lean.Data.LBool
public import Lean.Data.LOption
public import Lean.Data.Name
public import Lean.Data.OpenDecl
public import Lean.Data.PersistentArray
public import Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
public import Lean.Data.Position
public import Lean.Data.PrefixTree
public import Lean.Data.SMap
public import Lean.Data.Trie
public import Lean.Data.Iterators.Producers.PersistentHashMap
public import Init.Data.Ord.Basic
public import Init.WFTactics
public import Lean.Data.Html.Basic
public import Lean.Data.Html.CharRef
public import Lean.Data.Html.Elab
public import Lean.Data.Html.Syntax
public import Lean.Data.Html.Spec
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Algebra.Ring.IsFormallyReal
public import LeanMachineLearning.SequentialLearning.FeedbackMartingale
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Probability.Martingale.Centering
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Probability.Moments.Variance
public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
public import LeanMachineLearning.SequentialLearning.Means
public import Mathlib.Analysis.PSeries
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.SpecificLimits.Basic
public meta import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.NormNum
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Standalone extraction for `AlphaRAR.aRTS_clt_joint`
Definitions are copied verbatim; theorem proofs are replaced by `sorry`.
Auto-generated by ChallengeGen. -/

set_option quotPrecheck false

-- The options the project is built with.
set_option autoImplicit false
set_option relaxedAutoImplicit false

-- Namespace stubs (so later `open`s resolve).
namespace MeasureTheory
end MeasureTheory
namespace ProbabilityTheory
end ProbabilityTheory
namespace ProbabilityTheory.Kernel
end ProbabilityTheory.Kernel
namespace Learning
end Learning
namespace AlphaRAR
end AlphaRAR

-- ═══ AlphaRAR.ForLMLExplore.SequentialLearning.Means ═══
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Finset
namespace ProbabilityTheory.Kernel
variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨} [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨]

/-- The means of a kernel. -/
noncomputable def means (ν : Kernel 𝓐 𝓨) (k : 𝓐) : 𝓨 := (ν k)[id]

end ProbabilityTheory.Kernel
end

-- ═══ AlphaRAR.YDK2026.Count ═══
@[expose] public section
open Filter Finset MeasureTheory Learning
namespace AlphaRAR

/-- Allocation count of a fixed arm, `N n = ∑_{j<n} X j`, the count `N_{n,k}` of Section 2 of the
paper. Stated for a general `AddCommMonoid` so it serves both the deterministic per-path counts
(`X : ℕ → ℝ`) and the process-level count (`X : ℕ → Ω → ℝ`, the assignment count process of
`Assignment.lean`). -/
def count {M : Type*} [AddCommMonoid M] (X : ℕ → M) (n : ℕ) : M := ∑ j ∈ range n, X j

end AlphaRAR
end

-- ═══ AlphaRAR.YDK2026.Deterministic ═══
@[expose] public section
open Finset Filter
open scoped Topology
namespace AlphaRAR
variable (X p ρ : ℕ → ℝ) (α : ℝ)

/-- Sequential estimator of a fixed arm, equation (1) of the paper:
`θ̂ n = (∑_{j<n} X j ξ j + θ₀) / (N n + 1)`, with initial value `θ₀` and the `+1`
regularization in the denominator. -/
noncomputable def estimator (ξ : ℕ → ℝ) (θ₀ : ℝ) (n : ℕ) : ℝ :=
  ((∑ j ∈ range n, X j * ξ j) + θ₀) / (count X n + 1)

end AlphaRAR
end

-- ═══ AlphaRAR.YDK2026.ResponseConsistency ═══
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Learning
open scoped Topology
namespace AlphaRAR
variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐} [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν] {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm Unit 𝓐 ℝ}

/-- **Attainable set of the estimator.** The closure of all values `θ̂_{n,k}(ω)` of the sequential
estimator for arm `k`, over times `n` and outcomes `ω`. Every pointwise limit of `θ̂_{·,k}` lies
in it (`estimator_limit_mem_attainableSet`), so Condition **B**'s positivity requirement on this
set transfers to the plug-in-target limit `u_k = T(z)_k`. -/
noncomputable def attainableSet (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : ℝ) (k : 𝓐) : Set ℝ :=
  closure (Set.range fun p : ℕ × Ω ↦
    estimator (fun j ↦ actionIndicator A k j p.2) (Y · p.2) θ₀ p.1)

end AlphaRAR
end

-- ═══ AlphaRAR.YDK2026.ARTSAlgorithm ═══
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Learning Finset
open scoped Topology
namespace AlphaRAR
variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐} [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν] {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm Unit 𝓐 ℝ}

/-- History-level plug-in target `ρ̂_k`: the target map `T` applied to the vector of regularized
empirical means `(sumRewards' + θ₀)/(pullCount' + 1)` computed from a history
`h : Hist Unit 𝓐 ℝ n`. This is the design's target as a function of the observed history, matching
`aRTSTarget` on the history of the process (`histTarget_eq`). -/
noncomputable def histTarget (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (k : 𝓐) (n : ℕ)
    (h : Hist Unit 𝓐 ℝ n) : ℝ :=
  T (fun k' ↦ (sumRewards' n h k' + θ₀ k') / ((pullCount' n h k' : ℝ) + 1)) k

/-- **The aRTS design family**, algorithm form (Definition 3.1 of the paper). An algorithm `alg` is
an `α`-throttled aRTS design with offsets `θ₀` and target map `T` if its policy throttles every
over-sampled arm: for any history `h : Hist Unit 𝓐 ℝ n`, if arm `k` is over-sampled
(`N_{n,k}(h) > n ρ̂_k(h)`), then the probability the policy assigns to arm `k` for patient `n`
is at most `α ρ̂_k(h)`. (At `n = 0` the condition is vacuous: `N_{0,k} = 0`.) -/
structure IsARTS (alg : Algorithm Unit 𝓐 ℝ) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ) (α : ℝ) :
    Prop where
  throttle : ∀ (n : ℕ) (h : Hist Unit 𝓐 ℝ n) (k : 𝓐),
    (n : ℝ) * histTarget θ₀ T k n h < (pullCount' n h k : ℝ) →
      (alg.policy n (h, ()) {k}).toReal ≤ α * histTarget θ₀ T k n h

end AlphaRAR
end

-- ═══ AlphaRAR.YDK2026.PluginTargetCLT ═══
@[expose] public section
open MeasureTheory Filter ProbabilityTheory Learning
open scoped Topology RealInnerProductSpace Matrix ENNReal
namespace AlphaRAR
variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐} [MeasurableSingletonClass 𝓐] [DecidableEq 𝓐] [Fintype 𝓐] {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν] {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm Unit 𝓐 ℝ}

/-- The `√n`-scaled proportion-deviation vector `√n(N_{n,k}/n - v_k) ∈ ℝ^𝓐`. -/
noncomputable def propSqrtNVec (A : ℕ → Ω → 𝓐) (v : 𝓐 → ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ 𝓐 :=
  WithLp.toLp 2 (fun k ↦ √n * (count (fun j ↦ actionIndicator A k j ω) n / (n : ℝ) - v k))

/-- The `√n`-scaled plug-in-target error vector `√n(T(θ̂_n) - T(θ)) ∈ ℝ^𝓐`. -/
noncomputable def targetSqrtNVec (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ)
    (T : (𝓐 → ℝ) → 𝓐 → ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ 𝓐 :=
  WithLp.toLp 2 (fun k ↦ √n *
    (T (fun k' ↦ estimator (fun j ↦ actionIndicator A k' j ω) (Y · ω) (θ₀ k') n) k
      - T ν.means k))

/-- The `√n`-scaled joint vector `(√n(N_n/n - v), √n(ρ̂_n - v)) ∈ ℝ^(𝓐 ⊕ 𝓐)`. -/
noncomputable def jointSqrtNVec (ν : Kernel 𝓐 ℝ) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → ℝ) (θ₀ : 𝓐 → ℝ)
    (T : (𝓐 → ℝ) → 𝓐 → ℝ) (v : 𝓐 → ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ (𝓐 ⊕ 𝓐) :=
  WithLp.toLp 2 (Sum.elim (WithLp.ofLp (propSqrtNVec A v n ω))
    (WithLp.ofLp (targetSqrtNVec ν A Y θ₀ T n ω)))

end AlphaRAR
end

-- ═══ AlphaRAR.YDK2026.ARTSNormality ═══
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Learning
open scoped Topology ENNReal NNReal Matrix
namespace AlphaRAR
variable {Ω 𝓐 : Type*} {mΩ : MeasurableSpace Ω} {m𝓐 : MeasurableSpace 𝓐} [MeasurableSingletonClass 𝓐] {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν] {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm Unit 𝓐 ℝ}

/-- **Joint central limit theorem for the aRTS design**, equation (9) of Theorem 4.2 (ii) of the
paper, fully self-contained. From the `aRTS` design bundle — an `IsAlgEnvSeq` sequence, Condition
**A** (the kernel `L²` bound `hνk`), a simplex-valued target `T` that is `LipschitzWith K`
(Condition **B**), the algorithm-level predicate `IsARTS`, `α ∈ [0,1)`, the non-sparsity `hTpos`,
and the first-order differentiability of `T` at `θ` with Jacobian `G` (`hTderiv`) — the `√n`-scaled
joint vector `(√n(N_n/n - v), √n(ρ̂_n - v))` converges weakly to the block-Gaussian `𝒩(0, Ω)`, with
every block equal to `G · diag(V_k / v_k) · Gᵀ` with `V_k = Var[id; ν k]`, and
`v_k = T ν.means k`.

The `aRTS` instantiation of `clt_joint_of_hitting` at the last under-sampling time: the throttle is
`throttle_of_isARTS` (from `IsARTS`), the consistency smallness is `aRTS_smallness_all`, and the
`o_p`-smallness is `aRTS_smallness_op`, both automatic because `N_ℓ - ℓ ρ̂_ℓ ≤ 0` at that time
(`preliminary_small`). -/
theorem aRTS_clt_joint [Fintype 𝓐] [DecidableEq 𝓐] [StandardBorelSpace 𝓐] [Nonempty 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hνk : ∀ a, MemLp id 2 (ν a)) (θ₀ : 𝓐 → ℝ) (T : (𝓐 → ℝ) → 𝓐 → ℝ)
    (hTnn : ∀ z k, 0 ≤ T z k) (hTsum : ∀ z, ∑ k, T z k = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα1 : α < 1) (hARTS : IsARTS alg θ₀ T α)
    {K : ℝ≥0} (hlip : LipschitzWith K T)
    (hTpos : ∀ z : 𝓐 → ℝ, (∀ k, z k ∈ attainableSet A Y (θ₀ k) k) → ∀ k, 0 < T z k)
    (G : Matrix 𝓐 𝓐 ℝ)
    (hTderiv : HasFDerivAt
      (fun x : EuclideanSpace ℝ 𝓐 ↦ (WithLp.toLp 2 (T (WithLp.ofLp x)) : EuclideanSpace ℝ 𝓐))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) G) (WithLp.toLp 2 ν.means)) :
    TendstoInDistribution (jointSqrtNVec ν A Y θ₀ T (T ν.means)) atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (Matrix.fromBlocks
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T ν.means a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T ν.means a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T ν.means a) * Gᵀ)
        (G * Matrix.diagonal (fun a ↦ Var[id; ν a] / T ν.means a) * Gᵀ))) := sorry

end AlphaRAR
end
