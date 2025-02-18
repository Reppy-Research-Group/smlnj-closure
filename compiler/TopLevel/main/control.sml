(* control.sml
 *
 * COPYRIGHT (c) 2019 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *)

(* Code generation controls (including some used in FLINT?) *)
structure Control_CG : CGCONTROL =
  struct
    val priority = [10, 11, 2]
    val obscurity = 6
    val prefix = "cg"

    val registry = ControlRegistry.new { help = "code generator settings" }

    val _ = BasicControl.nest (prefix, registry, priority)

    val b = ControlUtil.Cvt.bool
    val i = ControlUtil.Cvt.int
    val r = ControlUtil.Cvt.real
    val sl = ControlUtil.Cvt.stringList

    val nextpri = ref 0

    fun new (c, n, h, d) = let
	  val r = ref d
	  val p = !nextpri
	  val ctl = Controls.control {
		  name = n,
		  pri = [p],
		  obscurity = obscurity,
		  help = h,
		  ctl = r }
	  in
	    nextpri := p + 1;
	    ControlRegistry.register
		registry
		{ ctl = Controls.stringControl c ctl,
		  envName = SOME (ControlUtil.EnvName.toUpper "CG_" n) };
	    r
	  end

    val closureStrategy = new (i, "closure-strategy", "?", 0)	(* see CPS/clos/closure.sml *)
    val cpsopt = new (sl, "cpsopt", "cps optimizer phases", [
	    "first_contract", "eta", "zeroexpand", "last_contract"
	  ])
    (* ["first_contract", "eta", "uncurry", "etasplit",
	"cycle_expand", "eta", "last_contract" ] *)
    val rounds = new (i, "rounds", "max # of cpsopt rounds", 10)
    val path = new (b, "path", "?", false)
    val betacontract = new (b, "betacontract", "?", true)
    val eta = new (b, "eta", "?", true)
    val selectopt = new (b, "selectopt", "enable contraction of record select", true)
    val dropargs = new (b, "dropargs", "?", true)
    val deadvars = new (b, "deadvars", "?", true)
    val flattenargs = new (b, "flattenargs", "?", false)
    val extraflatten = new (b, "extraflatten", "?", false)
    val switchopt = new (b, "switchopt", "?", true)
    val handlerfold = new (b, "handlerfold", "?", true)
    val branchfold = new (b, "branchfold", "?", false)
    val arithopt = new (b, "arithopt", "?", true)
    val betaexpand = new (b, "betaexpand", "?", true)
    val unroll = new (b, "unroll", "?", true)
    val invariant = new (b, "invariant", "?", true)
    val lambdaprop = new (b, "lambdaprop", "?", false)
    val newconreps = new (b, "newconreps", "?", true)
    val boxedconstconreps = ElabDataControl.boxedconstconreps
    val unroll_recur = new (b, "unroll-recur", "?", true)
    val sharepath = new (b, "sharepath", "?", true)
    val staticprof = new (b, "staticprof", "?", false)
    val verbose = new (b, "verbose", "?", false)
    val debugcps = new (b, "debugcps", "?", false)
    val bodysize = new (i, "bodysize", "?", 20)
    val reducemore = new (i, "reducemore", "?", 15)
    val comment = new (b, "comment", "?", false)
    val knownGen = new (i, "known-gen", "?", 0)
    val knownClGen = new (i, "known-cl-gen", "?", 0)
    val escapeGen = new (i, "escape-gen", "?", 0)
    val calleeGen = new (i, "callee-gen", "?", 0)
    val spillGen = new (i, "spill-gen", "?", 0)
    val etasplit = new (b, "etasplit", "?", true)
    val uncurry = new (b, "uncurry", "enable uncurrying optimization", true)
    val ifidiom = new (b, "if-idiom", "enable if-idiom optimization", true)
    val comparefold = new (b, "comparefold", "enable optimization of conditional tests", true)
    val debugLits = new (b, "debug-lits", "print results of literal lifting", false)
    val newLiterals = new (b, "new-literals", "use new literal representation", false)
    val debugRep = new (b, "debug-rep", "?", false)
    val deadup = new (b, "deadup", "?", true)
    val printit = new (b, "printit", "whether to show CPS", false)
    val printClusters = new (b, "print-clusters", "whether to print clusters prior to codegen", false)
    val printCFG = new (b, "print-cfg", "whether to convert to CFG and print it", false)
    val dumpCFG = new (b, "dump-cfg", "whether to convert to CFG and pickle it", false)
    val verifyLLVM = new (b, "verify-llvm", "enable verification of generated LLVM code", false)
    val debugSpill = new (b, "debug-cps-spill", "enable CPS spill debugging", false)
    val debugSpillInfo = new (b, "debug_cps_spill_info", "enable CPS spill info", false)
  end (* structure Control_CG *)

structure Control_NC : NEW_CLOSURE_CONTROL =
  struct
    val priority = [10, 11, 2]
    val obscurity = 6
    val prefix = "nc"

    val registry =
      ControlRegistry.new { help = "new closure converter settings" }

    val _ = BasicControl.nest (prefix, registry, priority)

    val b = ControlUtil.Cvt.bool
    val i = ControlUtil.Cvt.int
    val r = ControlUtil.Cvt.real
    val sl = ControlUtil.Cvt.stringList

    val nextpri = ref 0
    fun new (c, n, h, d) = let
	  val r = ref d
	  val p = !nextpri
	  val ctl = Controls.control {
		  name = n,
		  pri = [p],
		  obscurity = obscurity,
		  help = h,
		  ctl = r }
	  in
	    nextpri := p + 1;
	    ControlRegistry.register
		registry
		{ ctl = Controls.stringControl c ctl,
		  envName = SOME (ControlUtil.EnvName.toUpper "CG_" n) };
	    r
	  end

    val enable = new (b, "enable", "enable new closure converter", true)

    val flatClosure = new (b, "flat-closure", "use flat closure policy", false)

    val flattenPolicy =
      new (i, "flatten-policy", "select policy for closure flattening", 1)
    val flattenLiberally =
      new (b, "flatten-liberally",
              "use max to resolve arity among functions in the same web", true)
    val flattenSelfRef =
      new (b, "flatten-selfref",
              "whether to flatten self-referential environments", true)
    val flattenRegLimit =
      new (b, "flatten-reg-limit",
              "whether to impose register limit for known function environment \
              \passing", true)

    val sharingPolicy =
      new (i, "sharing-policy",
              "which sharing analysis to use", 2)
    val sharingDistCutOff =
      new (i, "sharing-dist-cutoff",
              "maximum difference of binding time among variables in a shared \
              \closure", 4)

    val sharingSizeCutOff =
      new (i, "sharing-size-cutoff",
              "minimum size of a shared closure", 6)

    val sharingUseCutOff =
      new (i, "sharing-use-cutoff",
              "minimum number of times by which a shared closure has to be \
              \shared", 4)

    val sharingNoThinning =
      new (b, "sharing-no-thinning",
              "whether to turn off thinning in the same closure", false)

    val instrument =
      new (b, "instrumentation",
              "insert counting instrumentation code", false)

    val dumpWeb = new (b, "dump-web", "dump call web", false)
    val dumpDecision = new (b, "dump-decision", "dump decision", false)
    val warnPath = 
      new (b, "warn-path", "emit warning for long access paths", false)
  end (* structure NewClosureControl *)

structure Control : CONTROL =
  struct

    local
      val priority = [10, 10, 9]
      val obscurity = 4
      val prefix = "control"

      val registry = ControlRegistry.new
                         { help = "miscellaneous control settings" }

      val _ = BasicControl.nest (prefix, registry, priority)

      val bool_cvt = ControlUtil.Cvt.bool
      val string_cvt = ControlUtil.Cvt.string

      val nextpri = ref 0

      fun register (cvtFn, name, help, defaultRef) = let
	    val p = !nextpri
	    val ctl = Controls.control {
		    name = name,
		    pri = [p],
		    obscurity = obscurity,
		    help = help,
		    ctl = defaultRef
		  }
	    in
	      nextpri := p + 1;
              ControlRegistry.register registry {
		  ctl = Controls.stringControl cvtFn ctl,
		  envName = SOME (ControlUtil.EnvName.toUpper "CONTROL_" name)
		};
	      defaultRef
	    end

    (* `new (n, h, d)` defines new control reference with default value `d`
     * and registers it with name `n` and help message `h`.
     *)
      fun new (n, h, d) = register (bool_cvt, n, h, ref d)

    in

    structure Print : PRINTCONTROL = Control_Print (* Basics/print/printcontrol.sml *)

    (* ElabData controls *)
    structure ElabData : ELABDATA_CONTROL = ElabDataControl (* ElabData/main/edcontrol.{sml,sig} *)

    (* elaborator controls *)
    structure Elab : ELAB_CONTROL = ElabControl (* Elaborator/control/elabcontrol.{sml,sig} *)

    (* MatchComp (match compiler) controls *)
    structure MC : MC_CONTROL = MCControl (* Elaborator/control/mccontrol.{sml,sig} *)

    (* FLINT controls *)
    structure FLINT = FLINT_Control (* FLINT/main/control.{sml,sig} *)

    structure CG : CGCONTROL = Control_CG

    structure NC : NEW_CLOSURE_CONTROL = Control_NC

    open BasicControl
    (* provides: val printWarnings = ref true *)

    open ParserControl
    (* provides: val primaryPrompt = ref "- "
		 val secondaryPrompt = ref "= "
		 val overloadKW = ref false
		 val lazysml = ref false
		 val quotation = ref false
                 val setSuccML : bool -> unit
     *)

    val debugging = new ("debugging", "?", false)
    val eldebugging = new ("eldebugging", "evalloop debugging", false)
    val pddebugging = new ("pddebugging", "PPDec debugging", false)
    val printAst = new ("printAst", "whether to print Ast representation", false)
    val printAbsyn = ElabControl.printAbsyn

    val interp = new ("interp", "?", false)

    val progressMsgs =
	new ("progressMsgs", "whether to print a message after each phase is completed", false)
    val trackExn =
	new ("track-exn", "whether to generate code that tracks exceptions", true)
    (* warning message when call of polyEqual compiled: *)
    val polyEqWarn =
	new ("poly-eq-warn", "whether to warn about calls of polyEqual", true)

    val preserveLvarNames = new ("preserve-names", "?", false)
    (* these are really all the same ref cell: *)
    val saveit : bool ref = ElabData.saveLvarNames
    val saveAbsyn : bool ref = saveit
    val saveLambda : bool ref = saveit
    val saveConvert : bool ref = saveit
    val saveCPSopt : bool ref = saveit
    val saveClosure : bool ref = saveit

    val tdp_instrument = TDPInstrument.enabled

    end (* local *)

  end (* structure Control *)
